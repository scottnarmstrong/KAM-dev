/-
Copyright (c) 2026 Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zohar Komargodski
-/
module

public import KAM.Strip.FourierBasic
public import KAM.Strip.CohomologicalDefs
public import KAM.Diophantine.SolverAlgebra
public import KAM.Diophantine.Frozen
public import KAM.Fourier.ExpSums
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cohomological equation on strips

Blueprint `bp:p1:cohomological`, stated about the interface definitions `KAM.cohSolution` and
`KAM.cohConst` of `KAM/Strip/CohomologicalDefs.lean` (design §2.4).

Let `ω` be `(γ, τ)`-Diophantine and let `g` be holomorphic, `1`-periodic and bounded by `A` on the
strip of width `ρ`, with `⟨g⟩ = 0`. For `0 < δ < ρ` the map `cohSolution ω g`, the Fourier series
of the coefficient solution `KAM.Diophantine.solve`, is holomorphic and `1`-periodic on the strip of
width `ρ - δ`, has zero average, solves `Du(θ)ω = g(θ)` there, and is bounded by
`cohConst n τ / (γ δ^{τ+n}) A`, with `cohConst n τ = (2π)⁻¹ (τ/(eπ))^τ (8n/π)^n`. It is the only
zero-average holomorphic `1`-periodic solution on that strip, bounded or not, and it is real on real
points when `g` is.

The coefficients of a directional derivative of a periodic holomorphic map are
`2πi (k · v) û_k` (`torusCoeff_fderiv`, `bp:p1:fourier-basic` (a) for such maps). Data with
values in `ι → ℂ` are solved componentwise by `cohSolutionPi` (definitionally `KAM.Apost.cohR` for
`ι = Fin p`), with the same bound in the sup norm. The operator-norm bound for matrix data
(`bp:p1:cohomological-operator`) is not proved here.
-/

public noncomputable section

open Set Filter MeasureTheory Topology

namespace KAM

variable {n : ℕ}

theorem continuous_realPoint : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

/-- The zeroth Fourier coefficient is the average. -/
theorem torusCoeff_zero (v : (Fin n → ℝ) → ℂ) : torusCoeff v 0 = torusAverage v := by
  simp [torusCoeff, character_zero]

/-- The derivative of a periodic map is periodic. -/
theorem fderiv_add_single_of_periodic {r : ℝ} {u : (Fin n → ℂ) → ℂ}
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n r → u (z + Pi.single i 1) = u z)
    (i : Fin n) {z : Fin n → ℂ} (hz : z ∈ complexStrip n r) :
    fderiv ℂ u (z + Pi.single i 1) = fderiv ℂ u z := by
  have hev : (fun w => u (w + Pi.single i 1)) =ᶠ[𝓝 z] u :=
    eventually_of_mem ((isOpen_complexStrip n r).mem_nhds hz) fun w hw => hp i w hw
  rw [← fderiv_comp_add_right, hev.fderiv_eq]

/-- **Coefficients of a directional derivative** (blueprint `bp:p1:fourier-basic` (a), for
periodic holomorphic maps): `(Du·v)^_k = 2πi (k · v) û_k`. -/
theorem torusCoeff_fderiv {r : ℝ} (hr : 0 < r) {u : (Fin n → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n r))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n r → u (z + Pi.single i 1) = u z)
    (v : Fin n → ℂ) (k : Fin n → ℤ) :
    torusCoeff (fun x => fderiv ℂ u (fun j => (x j : ℂ)) v) k =
      (2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * v j) *
        torusCoeff (fun x => u fun j => (x j : ℂ)) k := by
  have hw : DifferentiableOn ℂ (fun θ => character (-k) θ * u θ) (complexStrip n r) :=
    (differentiable_character (-k)).differentiableOn.mul hu
  have hwp : ∀ (i : Fin n) z, z ∈ complexStrip n r →
      character (-k) (z + Pi.single i 1) * u (z + Pi.single i 1) = character (-k) z * u z := by
    intro i z hz
    rw [character_add_single, hp i z hz]
  have h0 := torusAverage_complex_direction_eq_zero hr hw hwp v
  set c : ℂ := 2 * Real.pi * Complex.I * ∑ j, (((-k) j : ℤ) : ℂ) * v j with hc_def
  have hfd : ∀ x : Fin n → ℝ,
      fderiv ℂ (fun θ => character (-k) θ * u θ) (fun j => (x j : ℂ)) v =
        character (-k) (fun j => (x j : ℂ)) * fderiv ℂ u (fun j => (x j : ℂ)) v +
          c * (character (-k) (fun j => (x j : ℂ)) * u (fun j => (x j : ℂ))) := by
    intro x
    have hux : DifferentiableAt ℂ u (fun j => (x j : ℂ)) :=
      hu.differentiableAt ((isOpen_complexStrip n r).mem_nhds (ofReal_mem_complexStrip hr x))
    have hm := (hasFDerivAt_character (-k) (fun j => (x j : ℂ))).mul hux.hasFDerivAt
    rw [show fderiv ℂ (fun θ => character (-k) θ * u θ) (fun j => (x j : ℂ)) = _ from hm.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, modeForm_apply, hc_def]
    ring
  have hχ : Continuous fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character _).continuous.comp continuous_realPoint
  have hcu : Continuous fun x : Fin n → ℝ => u fun j => (x j : ℂ) :=
    hu.continuousOn.comp_continuous continuous_realPoint fun x => ofReal_mem_complexStrip hr x
  have hcDu : Continuous fun x : Fin n → ℝ => fderiv ℂ u (fun j => (x j : ℂ)) v :=
    ((differentiableOn_fderiv_of_isOpen_pi (isOpen_complexStrip n r) hu).continuousOn
      |>.comp_continuous continuous_realPoint fun x => ofReal_mem_complexStrip hr x).clm_apply
      continuous_const
  simp only [hfd] at h0
  have hsplit : torusAverage (fun x : Fin n → ℝ =>
      character (-k) (fun j => (x j : ℂ)) * fderiv ℂ u (fun j => (x j : ℂ)) v +
        c * (character (-k) (fun j => (x j : ℂ)) * u (fun j => (x j : ℂ)))) =
      torusAverage (fun x : Fin n → ℝ =>
        character (-k) (fun j => (x j : ℂ)) * fderiv ℂ u (fun j => (x j : ℂ)) v) +
        c * torusAverage (fun x : Fin n → ℝ =>
          character (-k) (fun j => (x j : ℂ)) * u (fun j => (x j : ℂ))) := by
    unfold torusAverage
    rw [← integral_const_mul]
    exact integral_add (integrableOn_unitCube_of_continuous (hχ.mul hcDu))
      (integrableOn_unitCube_of_continuous (continuous_const.mul (hχ.mul hcu)))
  rw [hsplit] at h0
  have hcneg : c = -(2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * v j) := by
    rw [hc_def]
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
  rw [hcneg] at h0
  simp only [torusCoeff]
  linear_combination h0

/-- The symbol of `v ↦ Dv·ω` is the flow multiplier of the coefficient solver. -/
theorem sum_mul_eq_flowMultiplier (ω : Fin n → ℝ) (k : Fin n → ℤ) :
    2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * ((ω j : ℝ) : ℂ) =
      Diophantine.flowMultiplier ω k := by
  simp [Diophantine.flowMultiplier, Diophantine.frequencyDot]

/-! ### The estimate -/

theorem cohConst_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ cohConst n τ := by
  unfold cohConst
  positivity

/-- The coefficients of a zero-average datum have weighted norm at most `(8n/(πδ))ⁿ A` at the
coefficient radius `2π(ρ - δ/2)`. -/
theorem weightedNorm_torusCoeff_le_of_avg_zero {ρ δ A : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
    (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0) :
    Fourier.SummableWeighted (2 * Real.pi * (ρ - δ / 2))
        (torusCoeff fun x => g fun j => (x j : ℂ)) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ / 2))
        (torusCoeff fun x => g fun j => (x j : ℂ)) ≤ (8 * n / (Real.pi * δ)) ^ n * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (ofReal_mem_complexStrip hρ 0))
  have hx : 0 < Real.pi * δ := by positivity
  have hS := (Fourier.hasSum_exp_neg_modeSize n hx).summable
  set f : (Fin n → ℤ) → ℝ := {k | k ≠ 0}.indicator
    fun k => Real.exp (-(Real.pi * δ) * Fourier.modeSize k) with hf_def
  have hf : Summable f := hS.indicator _
  have ha0 : torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) 0 = 0 := by
    rw [torusCoeff_zero, h0]
  have hle : ∀ k, ‖torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k‖ *
      Real.exp (2 * Real.pi * (ρ - δ / 2) * Fourier.modeSize k) ≤ A * f k := by
    intro k
    by_cases hk : k = 0
    · rw [hk, ha0, norm_zero, zero_mul]
      exact mul_nonneg hA0 (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
    · rw [hf_def, Set.indicator_of_mem (show k ∈ {k : Fin n → ℤ | k ≠ 0} from hk)]
      have hdec := norm_torusCoeff_le hρ hg hp hA k
      calc _ ≤ Real.exp (-(2 * Real.pi * ρ * Fourier.modeSize k)) * A *
            Real.exp (2 * Real.pi * (ρ - δ / 2) * Fourier.modeSize k) :=
          mul_le_mul_of_nonneg_right hdec (Real.exp_pos _).le
        _ = A * Real.exp (-(Real.pi * δ) * Fourier.modeSize k) := by
          rw [mul_comm _ A, mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hsum : Fourier.SummableWeighted (2 * Real.pi * (ρ - δ / 2))
      (torusCoeff fun x : Fin n → ℝ => g fun j => (x j : ℂ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle (hf.mul_left A)
  refine ⟨hsum, ?_⟩
  have htail : ∑' k, f k ≤ (8 * n / (Real.pi * δ)) ^ n := by
    rw [hf_def, ← tsum_subtype]
    exact Fourier.tsum_exp_neg_modeSize_ne_zero_le n hx
  calc Fourier.weightedNorm (2 * Real.pi * (ρ - δ / 2))
        (torusCoeff fun x : Fin n → ℝ => g fun j => (x j : ℂ))
      ≤ ∑' k, A * f k := Summable.tsum_le_tsum hle hsum (hf.mul_left A)
    _ = A * ∑' k, f k := tsum_mul_left
    _ ≤ A * (8 * n / (Real.pi * δ)) ^ n := mul_le_mul_of_nonneg_left htail hA0
    _ = (8 * n / (Real.pi * δ)) ^ n * A := mul_comm _ _

/-- The coefficient solution is summable at the coefficient radius `2π(ρ - δ)`, with weighted norm
at most `c(n, τ) γ⁻¹ δ^{-(τ+n)} A`. -/
theorem summableWeighted_solve_torusCoeff {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ}
    (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
    (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0) :
    Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
        (Diophantine.solve ω (torusCoeff fun x => g fun j => (x j : ℂ))) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
        (Diophantine.solve ω (torusCoeff fun x => g fun j => (x j : ℂ))) ≤
        cohConst n τ / (γ * δ ^ (τ + n)) * A := by
  obtain ⟨hsum, hbound⟩ := weightedNorm_torusCoeff_le_of_avg_zero hδ hδρ hg hp hA h0
  have hx : 0 < Real.pi * δ := by positivity
  have hrad : 2 * Real.pi * (ρ - δ / 2) - Real.pi * δ = 2 * Real.pi * (ρ - δ) := by ring
  have hs := Diophantine.summableWeighted_solve hω.condition hγ hτ hx hsum
  have hw := Diophantine.weightedNorm_solve_le hω.condition hγ hτ hx hsum
  rw [hrad] at hs hw
  refine ⟨hs, hw.trans ?_⟩
  calc Diophantine.solveBound γ τ (Real.pi * δ) * Fourier.weightedNorm (2 * Real.pi * (ρ - δ / 2))
        (torusCoeff fun x => g fun j => (x j : ℂ))
      ≤ Diophantine.solveBound γ τ (Real.pi * δ) * ((8 * n / (Real.pi * δ)) ^ n * A) :=
        mul_le_mul_of_nonneg_left hbound (Diophantine.solveBound_nonneg hγ hτ hx)
    _ = cohConst n τ / (γ * δ ^ (τ + n)) * A := by
        have h1 : τ / (Real.exp 1 * (Real.pi * δ)) = τ / (Real.exp 1 * Real.pi) / δ := by ring
        have h2 : 8 * (n : ℝ) / (Real.pi * δ) = 8 * n / Real.pi / δ := by ring
        have hτ' : 0 ≤ τ / (Real.exp 1 * Real.pi) := by positivity
        rw [Diophantine.solveBound, cohConst, h1, h2, Real.div_rpow hτ' hδ.le,
          div_pow (8 * (n : ℝ) / Real.pi) δ n, Real.rpow_add hδ, Real.rpow_natCast]
        have hδτ : δ ^ τ ≠ 0 := (Real.rpow_pos_of_pos hδ τ).ne'
        have hδn : δ ^ n ≠ 0 := (pow_pos hδ n).ne'
        have hγ' : γ ≠ 0 := hγ.ne'
        field_simp

/-! ### Existence, the equation and the bound -/

section Solution

variable {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ} {g : (Fin n → ℂ) → ℂ}

theorem cohSolution_add_single (ω : Fin n → ℝ) (g : (Fin n → ℂ) → ℂ) (θ : Fin n → ℂ)
    (i : Fin n) : cohSolution ω g (θ + Pi.single i 1) = cohSolution ω g θ :=
  fourierSum_add_single _ θ i

variable (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
  (hg : DifferentiableOn ℂ g (complexStrip n ρ))
  (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
  (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
  (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0)
include hω hγ hτ hδ hδρ hg hp hA h0

theorem differentiableOn_cohSolution :
    DifferentiableOn ℂ (cohSolution ω g) (complexStrip n (ρ - δ)) :=
  differentiableOn_fourierSum (summableWeighted_solve_torusCoeff hω hγ hτ hδ hδρ hg hp hA h0).1

/-- **The cohomological estimate** (blueprint `bp:p1:cohomological`):
`‖u‖_{ρ-δ} ≤ c(n, τ) γ⁻¹ δ^{-(τ+n)} A`. -/
theorem norm_cohSolution_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolution ω g θ‖ ≤ cohConst n τ / (γ * δ ^ (τ + n)) * A :=
  (norm_fourierSum_le (summableWeighted_solve_torusCoeff hω hγ hτ hδ hδρ hg hp hA h0).1 hθ).trans
    (summableWeighted_solve_torusCoeff hω hγ hτ hδ hδρ hg hp hA h0).2

theorem torusCoeff_cohSolution (k : Fin n → ℤ) :
    torusCoeff (fun x => cohSolution ω g fun j => (x j : ℂ)) k =
      Diophantine.solve ω (torusCoeff fun x => g fun j => (x j : ℂ)) k :=
  torusCoeff_fourierSum (by linarith)
    (summableWeighted_solve_torusCoeff hω hγ hτ hδ hδρ hg hp hA h0).1 k

theorem torusAverage_cohSolution :
    torusAverage (fun x => cohSolution ω g fun j => (x j : ℂ)) = 0 := by
  rw [← torusCoeff_zero, torusCoeff_cohSolution hω hγ hτ hδ hδρ hg hp hA h0,
    Diophantine.solve_zero_mode]

/-- **The cohomological equation** (blueprint `bp:p1:cohomological`): `Du(θ)ω = g(θ)` on the strip
of width `ρ - δ`. -/
theorem fderiv_cohSolution {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    fderiv ℂ (cohSolution ω g) θ (fun j => (ω j : ℂ)) = g θ := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hr : 0 < ρ - δ := by linarith
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun z hz j => by
    have := hz j
    linarith
  have hu := differentiableOn_cohSolution hω hγ hτ hδ hδρ hg hp hA h0
  have hup : ∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) →
      cohSolution ω g (z + Pi.single i 1) = cohSolution ω g z :=
    fun i z _ => cohSolution_add_single ω g z i
  have hDu := differentiableOn_fderiv_of_isOpen_pi (isOpen_complexStrip n (ρ - δ)) hu
  have hcDu : Continuous fun x : Fin n → ℝ =>
      fderiv ℂ (cohSolution ω g) (fun j => (x j : ℂ)) (fun j => (ω j : ℂ)) :=
    (hDu.continuousOn.comp_continuous continuous_realPoint
      fun x => ofReal_mem_complexStrip hr x).clm_apply continuous_const
  have hcg : Continuous fun x : Fin n → ℝ => g fun j => (x j : ℂ) :=
    hg.continuousOn.comp_continuous continuous_realPoint fun x => ofReal_mem_complexStrip hρ x
  have ha0 : torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) 0 = 0 := by
    rw [torusCoeff_zero, h0]
  have hw := eq_zero_of_torusCoeff_holomorphic hr
    (v := fun z => fderiv ℂ (cohSolution ω g) z (fun j => (ω j : ℂ)) - g z)
    ((hDu.clm_apply (differentiableOn_const _)).sub (hg.mono hsub))
    (fun i z hz => by
      show fderiv ℂ (cohSolution ω g) (z + Pi.single i 1) (fun j => (ω j : ℂ)) -
          g (z + Pi.single i 1) = fderiv ℂ (cohSolution ω g) z (fun j => (ω j : ℂ)) - g z
      rw [fderiv_add_single_of_periodic hup i hz, hp i z (hsub hz)])
    (fun k => by
      show torusCoeff (fun x : Fin n → ℝ =>
          fderiv ℂ (cohSolution ω g) (fun j => (x j : ℂ)) (fun j => (ω j : ℂ)) -
            g fun j => (x j : ℂ)) k = 0
      rw [torusCoeff_sub hcDu hcg, torusCoeff_fderiv hr hu hup, sum_mul_eq_flowMultiplier,
        torusCoeff_cohSolution hω hγ hτ hδ hδρ hg hp hA h0]
      have hsol := congrFun (Diophantine.directionalCoeff_solve (hω.condition.nonresonant hγ)
        (torusCoeff fun x : Fin n → ℝ => g fun j => (x j : ℂ))) k
      simp only [Diophantine.directionalCoeff, Diophantine.removeAverage] at hsol
      rw [hsol]
      split_ifs with hk
      · rw [hk, ha0, sub_zero]
      · exact sub_self _)
    θ hθ
  exact sub_eq_zero.mp hw

/-- **Uniqueness** (blueprint `bp:p1:cohomological`): every zero-average holomorphic `1`-periodic
solution of `Dv ω = g` on the strip of width `ρ - δ`, bounded or not, is `cohSolution ω g`. -/
theorem eq_cohSolution {v : (Fin n → ℂ) → ℂ}
    (hv : DifferentiableOn ℂ v (complexStrip n (ρ - δ)))
    (hvp : ∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) → v (z + Pi.single i 1) = v z)
    (hv0 : torusAverage (fun x : Fin n → ℝ => v fun j => (x j : ℂ)) = 0)
    (hveq : ∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ v θ (fun j => (ω j : ℂ)) = g θ)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) : v θ = cohSolution ω g θ := by
  have hr : 0 < ρ - δ := by linarith
  have ha0 : torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) 0 = 0 := by
    rw [torusCoeff_zero, h0]
  have hcoef : torusCoeff (fun x : Fin n → ℝ => v fun j => (x j : ℂ)) =
      Diophantine.solve ω (torusCoeff fun x : Fin n → ℝ => g fun j => (x j : ℂ)) := by
    apply Diophantine.solve_unique (hω.condition.nonresonant hγ)
    · rw [torusCoeff_zero, hv0]
    · funext k
      simp only [Diophantine.directionalCoeff, Diophantine.removeAverage]
      have hD := torusCoeff_fderiv hr hv hvp (fun j => (ω j : ℂ)) k
      beta_reduce at hD
      rw [sum_mul_eq_flowMultiplier] at hD
      have hDg : torusCoeff (fun x : Fin n → ℝ => fderiv ℂ v (fun j => (x j : ℂ))
          (fun j => (ω j : ℂ))) k = torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k :=
        congrArg (fun f => torusCoeff f k)
          (funext fun x => hveq _ (ofReal_mem_complexStrip hr x))
      rw [← hD, hDg]
      split_ifs with hk
      · rw [hk, ha0]
      · rfl
  have hu := differentiableOn_cohSolution hω hγ hτ hδ hδρ hg hp hA h0
  have hcv : Continuous fun x : Fin n → ℝ => v fun j => (x j : ℂ) :=
    hv.continuousOn.comp_continuous continuous_realPoint fun x => ofReal_mem_complexStrip hr x
  have hcu : Continuous fun x : Fin n → ℝ => cohSolution ω g fun j => (x j : ℂ) :=
    hu.continuousOn.comp_continuous continuous_realPoint fun x => ofReal_mem_complexStrip hr x
  have hw := eq_zero_of_torusCoeff_holomorphic hr (v := fun z => v z - cohSolution ω g z)
    (hv.sub hu)
    (fun i z hz => by
      show v (z + Pi.single i 1) - cohSolution ω g (z + Pi.single i 1) =
        v z - cohSolution ω g z
      rw [hvp i z hz, cohSolution_add_single])
    (fun k => by
      show torusCoeff (fun x : Fin n → ℝ =>
        v (fun j => (x j : ℂ)) - cohSolution ω g fun j => (x j : ℂ)) k = 0
      rw [torusCoeff_sub hcv hcu, hcoef, torusCoeff_cohSolution hω hγ hτ hδ hδρ hg hp hA h0,
        sub_self])
    θ hθ
  exact sub_eq_zero.mp hw

end Solution

/-! ### Realness -/

theorem conj_character_real (m : Fin n → ℤ) (x : Fin n → ℝ) :
    (starRingEnd ℂ) (character m fun j => (x j : ℂ)) = character (-m) fun j => (x j : ℂ) := by
  rw [character, character, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sum, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]

/-- Coefficients of a real function are conjugate symmetric. -/
theorem torusCoeff_conjugateSymmetric {v : (Fin n → ℝ) → ℂ} (hv : ∀ x, (v x).im = 0) :
    Fourier.ConjugateSymmetric (torusCoeff v) := by
  intro k
  simp only [torusCoeff, torusAverage]
  rw [← integral_conj]
  congr 1
  funext x
  rw [map_mul, conj_character_real, Complex.conj_eq_iff_im.mpr (hv x)]

/-- A Fourier series with conjugate-symmetric coefficients is real at real points. -/
theorem fourierSum_im_eq_zero {a : (Fin n → ℤ) → ℂ} (ha : Fourier.ConjugateSymmetric a)
    (x : Fin n → ℝ) : (fourierSum a fun j => (x j : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have hstar : ∀ f : (Fin n → ℤ) → ℂ, (starRingEnd ℂ) (∑' k, f k) = ∑' k, (starRingEnd ℂ) (f k) :=
    fun f => by
      simp only [starRingEnd_apply]
      exact tsum_star
  rw [fourierSum, hstar]
  conv_rhs => rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq]
  refine tsum_congr fun k => ?_
  show (starRingEnd ℂ) (a k * character k fun j => (x j : ℂ)) =
    a (-k) * character (-k) fun j => (x j : ℂ)
  rw [map_mul, conj_character_real, ha k]

/-- **Realness** (blueprint `bp:p1:cohomological`): if `g` is real on real points, so is
`cohSolution ω g`. -/
theorem cohSolution_im_eq_zero (ω : Fin n → ℝ) {g : (Fin n → ℂ) → ℂ}
    (hreal : ∀ x : Fin n → ℝ, (g fun j => (x j : ℂ)).im = 0) (x : Fin n → ℝ) :
    (cohSolution ω g fun j => (x j : ℂ)).im = 0 :=
  fourierSum_im_eq_zero
    (Diophantine.solve_conjugateSymmetric ω (torusCoeff_conjugateSymmetric hreal)) x

/-! ### Vector-valued data -/

section Vector

variable {ι : Type*}

/-- The componentwise solution for data with values in `ι → ℂ` (blueprint
`step:p1:coh-vector`). -/
@[expose] def cohSolutionPi (ω : Fin n → ℝ) (g : (Fin n → ℂ) → ι → ℂ) :
    (Fin n → ℂ) → ι → ℂ :=
  fun θ l => cohSolution ω (fun z => g z l) θ

theorem cohSolutionPi_add_single (ω : Fin n → ℝ) (g : (Fin n → ℂ) → ι → ℂ) (θ : Fin n → ℂ)
    (i : Fin n) : cohSolutionPi ω g (θ + Pi.single i 1) = cohSolutionPi ω g θ :=
  funext fun _ => cohSolution_add_single ω _ θ i

/-- Realness of the vector solution, componentwise. -/
theorem cohSolutionPi_im_eq_zero (ω : Fin n → ℝ) {g : (Fin n → ℂ) → ι → ℂ}
    (hreal : ∀ (x : Fin n → ℝ) l, (g (fun j => (x j : ℂ)) l).im = 0) (x : Fin n → ℝ) (l : ι) :
    (cohSolutionPi ω g (fun j => (x j : ℂ)) l).im = 0 :=
  cohSolution_im_eq_zero ω (g := fun z => g z l) (fun x => hreal x l) x

variable [Fintype ι]

/-- Components of the average of a continuous vector-valued map. -/
theorem torusAverage_apply {F : (Fin n → ℝ) → ι → ℂ} (hF : Continuous F) (l : ι) :
    torusAverage F l = torusAverage fun x => F x l := by
  have h := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.proj l : (ι → ℂ) →L[ℂ] ℂ) (integrableOn_unitCube_of_continuous hF)
  simp only [ContinuousLinearMap.proj_apply] at h
  exact h.symm

/-- Components of a derivative of a vector-valued map. -/
theorem fderiv_apply_of_differentiableAt {u : (Fin n → ℂ) → ι → ℂ} {θ : Fin n → ℂ}
    (hd : DifferentiableAt ℂ u θ) (w : Fin n → ℂ) (l : ι) :
    fderiv ℂ u θ w l = fderiv ℂ (fun z => u z l) θ w := by
  have h := ((ContinuousLinearMap.proj l : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt.comp θ
    hd.hasFDerivAt).fderiv
  have h2 := congrArg (fun L => L w) h
  simp only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] at h2
  exact h2.symm

/-- The components of a holomorphic `1`-periodic map with zero average are holomorphic,
`1`-periodic and have zero average. -/
theorem component_holomorphic_periodic {r : ℝ} (hr : 0 < r) {u : (Fin n → ℂ) → ι → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n r))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n r → u (z + Pi.single i 1) = u z)
    (h0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0) (l : ι) :
    DifferentiableOn ℂ (fun z => u z l) (complexStrip n r) ∧
      (∀ (i : Fin n) z, z ∈ complexStrip n r → u (z + Pi.single i 1) l = u z l) ∧
      torusAverage (fun x : Fin n → ℝ => u (fun j => (x j : ℂ)) l) = 0 := by
  refine ⟨differentiableOn_pi.mp hu l, fun i z hz => congrFun (hp i z hz) l, ?_⟩
  have hc : Continuous fun x : Fin n → ℝ => u fun j => (x j : ℂ) :=
    hu.continuousOn.comp_continuous continuous_realPoint fun x => ofReal_mem_complexStrip hr x
  rw [← torusAverage_apply hc, h0, Pi.zero_apply]

variable {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ} {g : (Fin n → ℂ) → ι → ℂ}
  (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
  (hg : DifferentiableOn ℂ g (complexStrip n ρ))
  (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
  (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
  (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0)
include hω hγ hτ hδ hδρ hg hp hA h0

theorem differentiableOn_cohSolutionPi :
    DifferentiableOn ℂ (cohSolutionPi ω g) (complexStrip n (ρ - δ)) := by
  refine differentiableOn_pi.mpr fun l => ?_
  obtain ⟨hgl, hpl, h0l⟩ := component_holomorphic_periodic (hδ.trans hδρ) hg hp h0 l
  exact differentiableOn_cohSolution (g := fun z => g z l) hω hγ hτ hδ hδρ hgl hpl
    (fun z hz => (norm_le_pi_norm (g z) l).trans (hA z hz)) h0l

/-- The cohomological estimate for vector-valued data, in the sup norm. -/
theorem norm_cohSolutionPi_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolutionPi ω g θ‖ ≤ cohConst n τ / (γ * δ ^ (τ + n)) * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (ofReal_mem_complexStrip hρ 0))
  have hc := cohConst_nonneg (n := n) hτ
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
  obtain ⟨hgl, hpl, h0l⟩ := component_holomorphic_periodic hρ hg hp h0 l
  exact norm_cohSolution_le (g := fun z => g z l) hω hγ hτ hδ hδρ hgl hpl
    (fun z hz => (norm_le_pi_norm (g z) l).trans (hA z hz)) h0l hθ

theorem torusAverage_cohSolutionPi :
    torusAverage (fun x => cohSolutionPi ω g fun j => (x j : ℂ)) = 0 := by
  have hr : 0 < ρ - δ := by linarith
  have hc : Continuous fun x : Fin n → ℝ => cohSolutionPi ω g fun j => (x j : ℂ) :=
    (differentiableOn_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0).continuousOn.comp_continuous
      continuous_realPoint fun x => ofReal_mem_complexStrip hr x
  funext l
  rw [torusAverage_apply hc l, Pi.zero_apply]
  obtain ⟨hgl, hpl, h0l⟩ := component_holomorphic_periodic (hδ.trans hδρ) hg hp h0 l
  exact torusAverage_cohSolution (g := fun z => g z l) hω hγ hτ hδ hδρ hgl hpl
    (fun z hz => (norm_le_pi_norm (g z) l).trans (hA z hz)) h0l

/-- The cohomological equation for vector-valued data. -/
theorem fderiv_cohSolutionPi {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    fderiv ℂ (cohSolutionPi ω g) θ (fun j => (ω j : ℂ)) = g θ := by
  have hd : DifferentiableAt ℂ (cohSolutionPi ω g) θ :=
    (differentiableOn_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0).differentiableAt
      ((isOpen_complexStrip n (ρ - δ)).mem_nhds hθ)
  funext l
  rw [fderiv_apply_of_differentiableAt hd]
  obtain ⟨hgl, hpl, h0l⟩ := component_holomorphic_periodic (hδ.trans hδρ) hg hp h0 l
  exact fderiv_cohSolution (g := fun z => g z l) hω hγ hτ hδ hδρ hgl hpl
    (fun z hz => (norm_le_pi_norm (g z) l).trans (hA z hz)) h0l hθ

/-- Uniqueness for vector-valued data: every zero-average holomorphic `1`-periodic solution on the
strip of width `ρ - δ`, bounded or not, is `cohSolutionPi ω g`. -/
theorem eq_cohSolutionPi {v : (Fin n → ℂ) → ι → ℂ}
    (hv : DifferentiableOn ℂ v (complexStrip n (ρ - δ)))
    (hvp : ∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) → v (z + Pi.single i 1) = v z)
    (hv0 : torusAverage (fun x : Fin n → ℝ => v fun j => (x j : ℂ)) = 0)
    (hveq : ∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ v θ (fun j => (ω j : ℂ)) = g θ)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) : v θ = cohSolutionPi ω g θ := by
  have hr : 0 < ρ - δ := by linarith
  funext l
  obtain ⟨hgl, hpl, h0l⟩ := component_holomorphic_periodic (hδ.trans hδρ) hg hp h0 l
  obtain ⟨hvl, hvpl, hv0l⟩ := component_holomorphic_periodic hr hv hvp hv0 l
  refine eq_cohSolution (g := fun z => g z l) hω hγ hτ hδ hδρ hgl hpl
    (fun z hz => (norm_le_pi_norm (g z) l).trans (hA z hz)) h0l hvl hvpl hv0l
    (fun θ' hθ' => ?_) hθ
  rw [← fderiv_apply_of_differentiableAt
    (hv.differentiableAt ((isOpen_complexStrip n (ρ - δ)).mem_nhds hθ')), hveq θ' hθ']

end Vector

end KAM

end
