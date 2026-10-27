/-
Copyright (c) 2026 Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zohar Komargodski
-/
module

public import KAM.Strip.Fourier
public import KAM.Fourier.ExpSums
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fourier series on strips

A coefficient family with `∑ |a_k| e^{2π|k|₁ρ} < ∞` defines the series `u(θ) = ∑ a_k χ_k(θ)`. It is
`1`-periodic and bounded by the weighted norm on the strip of width `ρ`, holomorphic there, and its
Fourier coefficients are the `a_k` (blueprint `bp:p1:summation`, first part). Holomorphy uses the
termwise derivative `a_k χ_k(θ) 2πi (k · v)` on every narrower strip, where the radius loss absorbs
the factor `|k|₁`. The coefficients follow by integrating term by term, since `⟨χ_m⟩ = [m = 0]`.

Conversely, the decay of the coefficients of a bounded periodic holomorphic function gives
`∑ |û_k| e^{2π|k|₁(ρ-δ)} ≤ coth(πδ)ⁿ ‖u‖_ρ` (second part).
-/

public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace KAM

variable {n : ℕ}

/-! ### Strips -/

/-- Strips are convex. -/
theorem convex_complexStrip (n : ℕ) (ρ : ℝ) : Convex ℝ (complexStrip n ρ) := by
  intro θ hθ η hη a b ha hb hab i
  obtain ⟨hx1, hx2⟩ := abs_lt.mp (hθ i)
  obtain ⟨hy1, hy2⟩ := abs_lt.mp (hη i)
  have him : ((a • θ + b • η) i).im = a * (θ i).im + b * (η i).im := by simp
  obtain rfl : b = 1 - a := by linarith
  rw [him, abs_lt]
  rcases ha.eq_or_lt with ha0 | hapos
  · subst ha0
    constructor <;> linarith
  · constructor <;> nlinarith [mul_lt_mul_of_pos_left hx1 hapos, mul_lt_mul_of_pos_left hx2 hapos,
      mul_le_mul_of_nonneg_left hy1.le hb, mul_le_mul_of_nonneg_left hy2.le hb]

/-- Every point of a strip lies in a strictly narrower strip. -/
theorem exists_mem_complexStrip_sub {ρ : ℝ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    ∃ ε > 0, θ ∈ complexStrip n (ρ - ε) := by
  have h : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), |(θ i).im| < ρ - ε := by
    intro i
    have ht : Tendsto (fun ε : ℝ => ρ - ε) (𝓝[>] 0) (𝓝 (ρ - 0)) :=
      (tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds
    rw [sub_zero] at ht
    exact ht.eventually (lt_mem_nhds (hθ i))
  obtain ⟨ε, hε, hεpos⟩ := ((eventually_all.mpr h).and eventually_mem_nhdsWithin).exists
  exact ⟨ε, hεpos, hε⟩

/-! ### Derivatives of characters -/

/-- The linear form `v ↦ ∑ⱼ kⱼ vⱼ`. -/
@[expose] def modeForm (k : Fin n → ℤ) : (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ j, (k j : ℂ) • ContinuousLinearMap.proj j

theorem modeForm_apply (k : Fin n → ℤ) (v : Fin n → ℂ) :
    modeForm k v = ∑ j, (k j : ℂ) * v j := by
  simp [modeForm]

theorem norm_modeForm_le (k : Fin n → ℤ) : ‖modeForm k‖ ≤ Fourier.modeSize k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Fourier.modeSize_nonneg k) fun v => ?_
  rw [modeForm_apply, Fourier.modeSize, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  have hk : ‖(k j : ℂ)‖ = |(k j : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [hk]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)

theorem hasFDerivAt_character (k : Fin n → ℤ) (θ : Fin n → ℂ) :
    HasFDerivAt (character k)
      (character k θ • ((2 * Real.pi * Complex.I : ℂ) • modeForm k)) θ := by
  have hlin : HasFDerivAt
      (fun θ : Fin n → ℂ => 2 * (Real.pi : ℂ) * Complex.I * ∑ j, (k j : ℂ) * θ j)
      ((2 * Real.pi * Complex.I : ℂ) • modeForm k) θ := by
    have h : (fun θ : Fin n → ℂ => 2 * (Real.pi : ℂ) * Complex.I * ∑ j, (k j : ℂ) * θ j) =
        ⇑((2 * Real.pi * Complex.I : ℂ) • modeForm k) := by
      funext θ
      simp [modeForm_apply]
    rw [h]
    exact ContinuousLinearMap.hasFDerivAt _
  exact hlin.cexp

/-- `∂_j χ_m = 2πi m_j χ_m`. -/
theorem fderiv_character_single (m : Fin n → ℤ) (θ : Fin n → ℂ) (j : Fin n) :
    fderiv ℂ (character m) θ (Pi.single j 1) =
      character m θ * (2 * Real.pi * Complex.I * (m j : ℂ)) := by
  rw [(hasFDerivAt_character m θ).fderiv]
  simp [modeForm_apply, Pi.single_apply]

/-! ### Averages of characters -/

theorem character_zero (θ : Fin n → ℂ) : character 0 θ = 1 := by
  simp [character]

theorem character_mul (k l : Fin n → ℤ) (θ : Fin n → ℂ) :
    character k θ * character l θ = character (k + l) θ := by
  simp only [character, ← Complex.exp_add, Pi.add_apply, Int.cast_add, add_mul,
    Finset.sum_add_distrib, mul_add]

theorem norm_character_real (k : Fin n → ℤ) (x : Fin n → ℝ) :
    ‖character k (fun j => (x j : ℂ))‖ = 1 := by
  rw [norm_character]
  simp

/-- `⟨χ_m⟩ = 1` if `m = 0` and `0` otherwise. -/
theorem torusAverage_character (m : Fin n → ℤ) :
    torusAverage (fun x : Fin n → ℝ => character m (fun j => (x j : ℂ))) =
      if m = 0 then 1 else 0 := by
  split_ifs with hm
  · subst hm
    simp only [character_zero]
    rw [torusAverage, setIntegral_const, measureReal_def, volume_unitCube, ENNReal.toReal_one,
      one_smul]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hm
    have hc : (2 * Real.pi * Complex.I * (m j : ℂ)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · exact Int.cast_ne_zero.mpr (by simpa using hj)
    have h := torusAverage_complex_coordinate_eq_zero one_pos
      (differentiable_character m).differentiableOn j
      (fun z _ => character_add_single m z j)
    simp only [fderiv_character_single] at h
    rw [torusAverage, integral_mul_const] at h
    exact (mul_eq_zero.mp h).resolve_right hc

/-! ### The series -/

/-- The Fourier series `θ ↦ ∑ₖ aₖ χₖ(θ)`. -/
@[expose] def fourierSum (a : (Fin n → ℤ) → ℂ) (θ : Fin n → ℂ) : ℂ :=
  ∑' k, a k * character k θ

theorem norm_coeff_mul_character_le {ρ : ℝ} (a : (Fin n → ℤ) → ℂ) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) (k : Fin n → ℤ) :
    ‖a k * character k θ‖ ≤ ‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k) := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_character_le k hθ) (norm_nonneg _)

theorem summable_coeff_mul_character {ρ : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted (2 * Real.pi * ρ) a) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) : Summable fun k => a k * character k θ :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_coeff_mul_character_le a hθ) ha)

/-- The series is bounded by the weighted norm of its coefficients. -/
theorem norm_fourierSum_le {ρ : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted (2 * Real.pi * ρ) a) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) :
    ‖fourierSum a θ‖ ≤ Fourier.weightedNorm (2 * Real.pi * ρ) a :=
  tsum_of_norm_bounded ha.hasSum (norm_coeff_mul_character_le a hθ)

/-- The series is `1`-periodic in every coordinate. -/
theorem fourierSum_add_single (a : (Fin n → ℤ) → ℂ) (θ : Fin n → ℂ) (i : Fin n) :
    fourierSum a (θ + Pi.single i 1) = fourierSum a θ := by
  simp only [fourierSum, character_add_single]

/-- The series is holomorphic on the strip. -/
theorem differentiableOn_fourierSum {ρ : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted (2 * Real.pi * ρ) a) :
    DifferentiableOn ℂ (fourierSum a) (complexStrip n ρ) := by
  intro θ hθ
  obtain ⟨ε, hε, hθε⟩ := exists_mem_complexStrip_sub hθ
  have hsub : complexStrip n (ρ - ε) ⊆ complexStrip n ρ := fun z hz j => by
    have := hz j
    linarith
  set C : ℝ := 2 * Real.pi * (Real.exp (-1) / (2 * Real.pi * ε)) with hC
  have hδ : 0 < 2 * Real.pi * ε := by positivity
  have hderiv : ∀ (k : Fin n → ℤ) (z : Fin n → ℂ), z ∈ complexStrip n (ρ - ε) →
      HasFDerivAt (fun z => a k * character k z)
        (a k • (character k z • ((2 * Real.pi * Complex.I : ℂ) • modeForm k))) z :=
    fun k z _ => (hasFDerivAt_character k z).const_mul (a k)
  have hbound : ∀ (k : Fin n → ℤ) (z : Fin n → ℂ), z ∈ complexStrip n (ρ - ε) →
      ‖a k • (character k z • ((2 * Real.pi * Complex.I : ℂ) • modeForm k))‖ ≤
        C * (‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) := by
    intro k z hz
    have hI : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    have hM := Fourier.mul_exp_radius_sub_le (2 * Real.pi * ρ) (Fourier.modeSize k) hδ
    have hexp : Real.exp ((2 * Real.pi * ρ - 2 * Real.pi * ε) * Fourier.modeSize k) =
        Real.exp (2 * Real.pi * (ρ - ε) * Fourier.modeSize k) := by
      congr 1
      ring
    rw [hexp] at hM
    calc ‖a k • (character k z • ((2 * Real.pi * Complex.I : ℂ) • modeForm k))‖
        = ‖a k‖ * (‖character k z‖ * (2 * Real.pi * ‖modeForm k‖)) := by
          rw [norm_smul, norm_smul, norm_smul, hI]
      _ ≤ ‖a k‖ * (Real.exp (2 * Real.pi * (ρ - ε) * Fourier.modeSize k) *
            (2 * Real.pi * Fourier.modeSize k)) := by
          gcongr
          · exact norm_character_le k hz
          · exact norm_modeForm_le k
      _ = 2 * Real.pi * ‖a k‖ * (Fourier.modeSize k *
            Real.exp (2 * Real.pi * (ρ - ε) * Fourier.modeSize k)) := by ring
      _ ≤ 2 * Real.pi * ‖a k‖ * (Real.exp (-1) / (2 * Real.pi * ε) *
            Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) := by
          gcongr
      _ = C * (‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) := by
          rw [hC]
          ring
  have h := hasFDerivAt_tsum_of_isPreconnected (ha.mul_left C) (isOpen_complexStrip n _)
    (convex_complexStrip n _).isPreconnected hderiv hbound hθε
    (summable_coeff_mul_character ha (hsub hθε)) hθε
  exact h.differentiableAt.differentiableWithinAt

/-- The Fourier coefficients of the series are the `a_k`. -/
theorem torusCoeff_fourierSum {ρ : ℝ} (hρ : 0 ≤ ρ) {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted (2 * Real.pi * ρ) a) (k : Fin n → ℤ) :
    torusCoeff (fun x => fourierSum a (fun j => (x j : ℂ))) k = a k := by
  have hsum : Summable fun l : Fin n → ℤ => ‖a l‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun l => le_mul_of_one_le_right (norm_nonneg _)
        (Real.one_le_exp (by have := Fourier.modeSize_nonneg l; positivity))) ha
  -- Multiply the series by `χ_{-k}` term by term.
  have hterm : ∀ x : Fin n → ℝ, character (-k) (fun j => (x j : ℂ)) *
      fourierSum a (fun j => (x j : ℂ)) =
        ∑' l, a l * character (l + -k) (fun j => (x j : ℂ)) := by
    intro x
    rw [fourierSum, ← tsum_mul_left]
    refine tsum_congr fun l => ?_
    rw [← character_mul]
    ring
  have hcont : ∀ l : Fin n → ℤ, Continuous fun x : Fin n → ℝ =>
      a l * character (l + -k) (fun j => (x j : ℂ)) := fun l =>
    continuous_const.mul ((differentiable_character _).continuous.comp
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)))
  have hint : ∀ l : Fin n → ℤ, ∫ x in Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1),
      ‖a l * character (l + -k) (fun j => (x j : ℂ))‖ = ‖a l‖ := by
    intro l
    simp only [norm_mul, norm_character_real, mul_one]
    rw [setIntegral_const, measureReal_def, volume_unitCube, ENNReal.toReal_one, one_smul]
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1))
    (F := fun l x => a l * character (l + -k) (fun j => (x j : ℂ)))
    (fun l => integrableOn_unitCube_of_continuous (hcont l)) (by simpa only [hint] using hsum)
  have hcoeff : torusCoeff (fun x => fourierSum a (fun j => (x j : ℂ))) k =
      ∑' l, a l * torusAverage (fun x : Fin n → ℝ => character (l + -k) (fun j => (x j : ℂ))) := by
    have h1 : torusCoeff (fun x => fourierSum a (fun j => (x j : ℂ))) k =
        ∫ x in Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1),
          ∑' l, a l * character (l + -k) (fun j => (x j : ℂ)) := by
      rw [torusCoeff, torusAverage]
      simp only [hterm]
    refine h1.trans (hswap.symm.trans (tsum_congr fun l => ?_))
    rw [torusAverage, ← integral_const_mul]
  rw [hcoeff, tsum_eq_single k]
  · rw [torusAverage_character, ite_eq_left (by simp), mul_one]
  · intro l hl
    rw [torusAverage_character, ite_eq_right, mul_zero]
    intro h
    exact hl (by simpa [add_neg_eq_zero] using h)

/-! ### The converse estimate -/

/-- **Summation, converse part** (blueprint `bp:p1:summation`): for `u` holomorphic, `1`-periodic
and bounded by `A` on the strip of width `ρ`, and `0 < δ < ρ`, the coefficients satisfy
`∑ |û_k| e^{2π|k|₁(ρ-δ)} ≤ coth(πδ)ⁿ A`. -/
theorem summableWeighted_torusCoeff {ρ δ A : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    {u : (Fin n → ℂ) → ℂ} (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖u z‖ ≤ A) :
    Fourier.SummableWeighted (2 * Real.pi * (ρ - δ)) (torusCoeff fun x => u fun j => (x j : ℂ)) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ)) (torusCoeff fun x => u fun j => (x j : ℂ)) ≤
        (Real.cosh (Real.pi * δ) / Real.sinh (Real.pi * δ)) ^ n * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ (ofReal_mem_complexStrip hρ 0))
  have hx : 0 < 2 * Real.pi * δ := by positivity
  have hgeom := Fourier.hasSum_exp_neg_modeSize n hx
  have hle : ∀ k : Fin n → ℤ, ‖torusCoeff (fun x => u fun j => (x j : ℂ)) k‖ *
      Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) ≤
        A * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) := by
    intro k
    have hdec := norm_torusCoeff_le hρ hu hp hA k
    calc ‖torusCoeff (fun x => u fun j => (x j : ℂ)) k‖ *
          Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k)
        ≤ Real.exp (-(2 * Real.pi * ρ * Fourier.modeSize k)) * A *
          Real.exp (2 * Real.pi * (ρ - δ) * Fourier.modeSize k) :=
          mul_le_mul_of_nonneg_right hdec (Real.exp_pos _).le
      _ = A * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) := by
          rw [mul_comm _ A, mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hsum : Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
      (torusCoeff fun x => u fun j => (x j : ℂ)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hle (hgeom.summable.mul_left A)
  refine ⟨hsum, ?_⟩
  calc Fourier.weightedNorm (2 * Real.pi * (ρ - δ)) (torusCoeff fun x => u fun j => (x j : ℂ))
      ≤ ∑' k : Fin n → ℤ, A * Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) :=
        Summable.tsum_le_tsum hle hsum (hgeom.summable.mul_left A)
    _ = (Real.cosh (Real.pi * δ) / Real.sinh (Real.pi * δ)) ^ n * A := by
        rw [tsum_mul_left, hgeom.tsum_eq, show 2 * Real.pi * δ / 2 = Real.pi * δ by ring]
        ring

end KAM

end
