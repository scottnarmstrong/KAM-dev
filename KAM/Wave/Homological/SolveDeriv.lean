/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.SolveLinear
public import KAM.Wave.Homological.HolomorphicBanach
public import KAM.Strip.Averages
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Derivatives of Fourier coefficients and of the multiplier solve (blueprint-W `bpW:w4:fourier-ops`
(ii), `bpW:w4:solve` (iii))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still being built.

* `homPartial_differentiableOn`, `homPartial_periodic`: `∂_{θ_i} f` is holomorphic and `1`-periodic;
* `homCoeff_partial`: `(∂_{θ_i} f)^_k = 2πi k_i f̂_k` (Banach-valued, by duality with the scalar
  `KAM.torusCoeff_fderiv`);
* `fderiv_fourierSumVec_single`: termwise differentiation of an absolutely convergent series;
* `homSolve_partial`: `∂_{θ_i} 𝒮 f = 𝒮 (∂_{θ_i} f)` on `T_{s-σ}` when `∂_{θ_i} f` is bounded.
-/

@[expose] public section

namespace KAM.Wave

open KAM

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']

/-- The coordinate derivative `∂_{θ_i} f`. -/
noncomputable def homPartial (i : Fin 2) (u : (Fin 2 → ℂ) → E) : (Fin 2 → ℂ) → E :=
  fun z => fderiv ℂ u z (Pi.single i 1)


/-- **Scalar coefficients of a directional derivative** (the scalar case of
`bpW:w4:fourier-ops` (ii); this is track K's `KAM.torusCoeff_fderiv`, reproved here to avoid the
heavier import). -/
theorem homScalar_torusCoeff_fderiv {r : ℝ} (hr : 0 < r) {u : (Fin 2 → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip 2 r))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 r → u (z + Pi.single i 1) = u z)
    (v : Fin 2 → ℂ) (k : Fin 2 → ℤ) :
    torusCoeff (fun x => fderiv ℂ u (fun j => (x j : ℂ)) v) k =
      (2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * v j) *
        torusCoeff (fun x => u fun j => (x j : ℂ)) k := by
  have hrp : Continuous fun x : Fin 2 → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hw : DifferentiableOn ℂ (fun θ => character (-k) θ * u θ) (complexStrip 2 r) :=
    (differentiable_character (-k)).differentiableOn.mul hu
  have hwp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 r →
      character (-k) (z + Pi.single i 1) * u (z + Pi.single i 1) = character (-k) z * u z := by
    intro i z hz
    rw [character_add_single, hp i z hz]
  have h0 := torusAverage_complex_direction_eq_zero hr hw hwp v
  set c : ℂ := 2 * Real.pi * Complex.I * ∑ j, (((-k) j : ℤ) : ℂ) * v j with hc_def
  have hfd : ∀ x : Fin 2 → ℝ,
      fderiv ℂ (fun θ => character (-k) θ * u θ) (fun j => (x j : ℂ)) v =
        character (-k) (fun j => (x j : ℂ)) * fderiv ℂ u (fun j => (x j : ℂ)) v +
          c * (character (-k) (fun j => (x j : ℂ)) * u (fun j => (x j : ℂ))) := by
    intro x
    have hux : DifferentiableAt ℂ u (fun j => (x j : ℂ)) :=
      hu.differentiableAt ((isOpen_complexStrip 2 r).mem_nhds (ofReal_mem_complexStrip hr x))
    have hm := (hasFDerivAt_character (-k) (fun j => (x j : ℂ))).mul hux.hasFDerivAt
    rw [show fderiv ℂ (fun θ => character (-k) θ * u θ) (fun j => (x j : ℂ)) = _ from hm.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      modeForm_apply, hc_def]
    ring
  have hχ : Continuous fun x : Fin 2 → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character _).continuous.comp hrp
  have hcu : Continuous fun x : Fin 2 → ℝ => u fun j => (x j : ℂ) :=
    hu.continuousOn.comp_continuous hrp fun x => ofReal_mem_complexStrip hr x
  have hcDu : Continuous fun x : Fin 2 → ℝ => fderiv ℂ u (fun j => (x j : ℂ)) v :=
    ((differentiableOn_fderiv_of_isOpen_pi (isOpen_complexStrip 2 r) hu).continuousOn
      |>.comp_continuous hrp fun x => ofReal_mem_complexStrip hr x).clm_apply
      continuous_const
  simp only [hfd] at h0
  have hsplit : torusAverage (fun x : Fin 2 → ℝ =>
      character (-k) (fun j => (x j : ℂ)) * fderiv ℂ u (fun j => (x j : ℂ)) v +
        c * (character (-k) (fun j => (x j : ℂ)) * u (fun j => (x j : ℂ)))) =
      torusAverage (fun x : Fin 2 → ℝ =>
        character (-k) (fun j => (x j : ℂ)) * fderiv ℂ u (fun j => (x j : ℂ)) v) +
        c * torusAverage (fun x : Fin 2 → ℝ =>
          character (-k) (fun j => (x j : ℂ)) * u (fun j => (x j : ℂ))) := by
    unfold torusAverage
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_add (integrableOn_unitCube_of_continuous (hχ.mul hcDu))
      (integrableOn_unitCube_of_continuous (continuous_const.mul (hχ.mul hcu)))
  rw [hsplit] at h0
  have hcneg : c = -(2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * v j) := by
    rw [hc_def]
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
  rw [hcneg] at h0
  simp only [torusCoeff]
  linear_combination h0

/-- `∂_{θ_i} f` is complex differentiable (**`bpW:w4:fourier-ops` (ii)**, first part). -/
theorem homPartial_differentiableOn {s : ℝ} (i : Fin 2) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s)) :
    DifferentiableOn ℂ (homPartial i u) (complexStrip 2 s) :=
  (differentiableOn_fderiv_of_isOpen_pi_banach (isOpen_complexStrip 2 s) hu).clm_apply
    (differentiableOn_const _)

omit [CompleteSpace E] in
/-- `∂_{θ_i} f` is `1`-periodic (**`bpW:w4:fourier-ops` (ii)**, first part). -/
theorem homPartial_periodic {s : ℝ} {u : (Fin 2 → ℂ) → E}
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (i j : Fin 2) {z : Fin 2 → ℂ} (hz : z ∈ complexStrip 2 s) :
    homPartial i u (z + Pi.single j 1) = homPartial i u z := by
  have hev : (fun w => u (w + Pi.single j 1)) =ᶠ[nhds z] u :=
    Filter.eventually_of_mem ((isOpen_complexStrip 2 s).mem_nhds hz) fun w hw => hp j w hw
  unfold homPartial
  rw [← fderiv_comp_add_right, hev.fderiv_eq]

/-- **Coefficients of derivatives** (blueprint `bpW:w4:fourier-ops` (ii)):
`(∂_{θ_i} f)^_k = 2πi k_i f̂_k`. -/
theorem homCoeff_partial {s : ℝ} (hs : 0 < s) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (i : Fin 2) (k : Fin 2 → ℤ) :
    homCoeff (homPartial i u) k = (2 * Real.pi * Complex.I * (k i : ℂ)) • homCoeff u k := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun φ => ?_
  have hdu := homPartial_differentiableOn i hu
  have h1 := homCoeff_clm hs hdu φ k
  have h2 := homCoeff_clm hs hu φ k
  have hφp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → φ (u (z + Pi.single i 1)) = φ (u z) :=
    fun i z hz => by rw [hp i z hz]
  have h3 := homScalar_torusCoeff_fderiv hs (u := fun w => φ (u w))
    (φ.differentiable.comp_differentiableOn hu) hφp (Pi.single i 1) k
  have hfd : ∀ z ∈ complexStrip 2 s,
      fderiv ℂ (fun w => φ (u w)) z (Pi.single i 1) = φ (homPartial i u z) := by
    intro z hz
    have hz' := hu.differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hz)
    have := (φ.hasFDerivAt.comp z hz'.hasFDerivAt).fderiv
    exact congrArg (fun L => L (Pi.single i 1)) this
  have hsum : ∑ j, (k j : ℂ) * (Pi.single i 1 : Fin 2 → ℂ) j = (k i : ℂ) := by
    simp [Pi.single_apply]
  have h4 : torusCoeff (fun x => fderiv ℂ (fun w => φ (u w)) (fun j => (x j : ℂ))
      (Pi.single i 1)) k = torusCoeff (fun x => φ (homPartial i u fun j => (x j : ℂ))) k := by
    congr 1; funext x; exact hfd _ (ofReal_mem_complexStrip hs x)
  rw [h4, hsum] at h3
  rw [map_smul]
  have h1' : φ (homCoeff (homPartial i u) k) =
      torusCoeff (fun x => φ (homPartial i u fun j => (x j : ℂ))) k := by
    rw [← homCoeff_clm hs hdu φ k]; rfl
  have h2' : φ (homCoeff u k) = torusCoeff (fun x => φ (u fun j => (x j : ℂ))) k := by
    rw [← homCoeff_clm hs hu φ k]; rfl
  rw [h1', h2', h3]
  simp only [smul_eq_mul]

/-- **Termwise differentiation** of an absolutely convergent Fourier series in the direction
`e_i`, when the termwise-differentiated coefficients `2πi k_i a_k` are also weighted-summable. -/
theorem fderiv_fourierSumVec_single {i : Fin 2} {ρ : ℝ} {a : (Fin 2 → ℤ) → E'}
    (ha : Summable fun k => ‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k))
    (hb : Summable fun k => ‖(2 * Real.pi * Complex.I * (k i : ℂ)) • a k‖ *
      Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 ρ) :
    fderiv ℂ (fourierSumVec a) θ (Pi.single i 1) =
      fourierSumVec (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) • a k) θ := by
  set e : Fin 2 → ℂ := Pi.single i 1 with he
  set U : Set ℂ := {t | θ + t • e ∈ complexStrip 2 ρ} with hU
  have hcont : Continuous fun t : ℂ => θ + t • e := by fun_prop
  have hUo : IsOpen U := (isOpen_complexStrip 2 ρ).preimage hcont
  have hUc : Convex ℝ U := by
    have hcv := (convex_complexStrip 2 ρ).affine_preimage
      ((AffineMap.const ℝ ℂ θ).comp (AffineMap.id ℝ ℂ) +ᵥ
        (((LinearMap.id : ℂ →ₗ[ℝ] ℂ).smulRight e : ℂ →ₗ[ℝ] (Fin 2 → ℂ)).toAffineMap))
    convert hcv using 1
    ext t; simp [hU]
  have h0 : (0 : ℂ) ∈ U := by simpa [hU] using hθ
  have hl : ∀ t : ℂ, HasDerivAt (fun t : ℂ => θ + t • e) e t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const e).const_add θ
  have hterm : ∀ (k : Fin 2 → ℤ) (t : ℂ), HasDerivAt
      (fun t : ℂ => character k (θ + t • e) • a k)
      (character k (θ + t • e) • ((2 * Real.pi * Complex.I * (k i : ℂ)) • a k)) t := by
    intro k t
    have h := ((hasFDerivAt_character k (θ + t • e)).comp_hasDerivAt t (hl t)).smul_const (a k)
    have hv : (character k (θ + t • e) • ((2 * Real.pi * Complex.I : ℂ) • modeForm k)) e =
        character k (θ + t • e) * (2 * Real.pi * Complex.I * (k i : ℂ)) := by
      simp [e, modeForm_apply, Pi.single_apply]
    refine h.congr_deriv ?_
    rw [hv, smul_smul]
  have hbd : ∀ (k : Fin 2 → ℤ) (t : ℂ), t ∈ U →
      ‖character k (θ + t • e) • ((2 * Real.pi * Complex.I * (k i : ℂ)) • a k)‖ ≤
        ‖(2 * Real.pi * Complex.I * (k i : ℂ)) • a k‖ *
          Real.exp (2 * Real.pi * ρ * Fourier.modeSize k) :=
    fun k t ht => norm_character_smul_le (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) • a k) ht k
  have hder := hasDerivAt_tsum_of_isPreconnected (g := fun k t => character k (θ + t • e) • a k)
    (g' := fun k t => character k (θ + t • e) • ((2 * Real.pi * Complex.I * (k i : ℂ)) • a k))
    hb hUo hUc.isPreconnected (fun k t _ => hterm k t) hbd h0
    (summable_character_smul ha (by simpa [hU] using h0)) h0
  have hdiff : DifferentiableAt ℂ (fourierSumVec a) θ :=
    (differentiableOn_fourierSumVec ha).differentiableAt
      ((isOpen_complexStrip 2 ρ).mem_nhds hθ)
  have hcomp : HasDerivAt (fun t : ℂ => fourierSumVec a (θ + t • e))
      (fderiv ℂ (fourierSumVec a) θ e) 0 := by
    have hd' : HasFDerivAt (fourierSumVec a) (fderiv ℂ (fourierSumVec a) θ) (θ + (0 : ℂ) • e) := by
      simpa using hdiff.hasFDerivAt
    have := hd'.comp_hasDerivAt (0 : ℂ) (hl 0)
    simpa [Function.comp_def] using this
  have hfun : (fun t : ℂ => fourierSumVec a (θ + t • e)) =
      fun t => ∑' k, character k (θ + t • e) • a k := rfl
  rw [hfun] at hcomp
  have := hcomp.unique (by simpa using hder)
  rw [this]
  simp [fourierSumVec]

/-- **Multiplier solve, (iii)** (blueprint `bpW:w4:solve` (iii)): if `∂_{θ_i} f` is bounded on
`T_s` then `∂_{θ_i} 𝒮 f = 𝒮 (∂_{θ_i} f)` on `T_{s-σ}`. -/
theorem homSolve_partial {s σ m m' κ α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hσ : 0 < σ) (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E'}
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hmu : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m)
    (i : Fin 2) (hm : ∀ z ∈ complexStrip 2 s, ‖homPartial i u z‖ ≤ m') {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    fderiv ℂ (homSolve T u) θ (Pi.single i 1) = homSolve T (homPartial i u) θ := by
  have hs : 0 < s := hσ.trans hσs
  have hdu := homPartial_differentiableOn i hu
  have hdp : ∀ (j : Fin 2) z, z ∈ complexStrip 2 s →
      homPartial i u (z + Pi.single j 1) = homPartial i u z :=
    fun j z hz => homPartial_periodic hp i j hz
  obtain ⟨hsb, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT hdu hdp hm
  have hcoef : ∀ k, T k (homCoeff (homPartial i u) k) =
      (2 * Real.pi * Complex.I * (k i : ℂ)) • T k (homCoeff u k) := fun k => by
    rw [homCoeff_partial hs hu hp i k, map_smul]
  have hb : Summable fun k => ‖(2 * Real.pi * Complex.I * (k i : ℂ)) • T k (homCoeff u k)‖ *
      Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) := by
    simpa only [hcoef] using hsb
  -- summability of the weighted coefficients of `𝒮 u`
  obtain ⟨hsu, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT hu hp hmu
  unfold homSolve
  rw [fderiv_fourierSumVec_single hsu hb hθ]
  unfold fourierSumVec
  refine tsum_congr fun k => ?_
  show _ = character k θ • (T k (homCoeff (homPartial i u) k))
  rw [hcoef k]

end KAM.Wave
