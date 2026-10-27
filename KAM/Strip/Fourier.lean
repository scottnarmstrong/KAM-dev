/-
Copyright (c) 2026 Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zohar Komargodski
-/
module

public import KAM.Strip.Averages
public import KAM.Fourier.Derivative
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fourier coefficients of periodic holomorphic functions: decay

For `k ∈ ℤⁿ` the period-one character is `χ_k(θ) = exp(2πi k·θ)`, and the Fourier coefficient
`v̂_k = ⟨v χ_{-k}⟩` of a function on the real torus is its torus average against `χ_{-k}`.

Moving the real torus inside the strip by an imaginary vector does not change the average of a
periodic holomorphic function: the derivative of the average in the size of the shift is the
average of a periodic derivative, which vanishes. Shifting by `-ρ' sgn(k)` gives the decay
`|û_k| ≤ e^{-2π|k|₁ρ'} ‖u‖_ρ` for `0 ≤ ρ' < ρ` (blueprint `bp:p1:decay`), and letting `ρ' ↑ ρ`
gives the bound at `ρ` itself. The shift replaces the coordinatewise rectangle argument of the
blueprint; it uses no Fubini step.
-/

public noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace KAM

variable {n : ℕ}

/-- The period-one character `θ ↦ exp(2πi k·θ)` on `ℂⁿ`. -/
@[expose] def character (k : Fin n → ℤ) (θ : Fin n → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ j, (k j : ℂ) * θ j)

/-- The Fourier coefficient `v̂_k = ⟨v χ_{-k}⟩` of a function on the real torus. -/
@[expose] def torusCoeff (v : (Fin n → ℝ) → ℂ) (k : Fin n → ℤ) : ℂ :=
  torusAverage (fun x => character (-k) (fun j => (x j : ℂ)) * v x)

theorem character_add (k : Fin n → ℤ) (θ η : Fin n → ℂ) :
    character k (θ + η) = character k θ * character k η := by
  simp only [character, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.exp_add]

theorem character_single (k : Fin n → ℤ) (i : Fin n) : character k (Pi.single i 1) = 1 := by
  rw [character, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
    (by simp), Pi.single_eq_same, mul_one,
    show 2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ) = (k i : ℂ) * (2 * Real.pi * Complex.I) by
      ring]
  exact Complex.exp_int_mul_two_pi_mul_I (k i)

/-- Characters are `1`-periodic in every coordinate. -/
theorem character_add_single (k : Fin n → ℤ) (θ : Fin n → ℂ) (i : Fin n) :
    character k (θ + Pi.single i 1) = character k θ := by
  rw [character_add, character_single, mul_one]

theorem differentiable_character (k : Fin n → ℤ) : Differentiable ℂ (character k) := by
  unfold character
  fun_prop

/-- `|χ_k(θ)| = e^{-2π k·Im θ}`. -/
theorem norm_character (k : Fin n → ℤ) (θ : Fin n → ℂ) :
    ‖character k θ‖ = Real.exp (-(2 * Real.pi * ∑ j, (k j : ℝ) * (θ j).im)) := by
  rw [character, Complex.norm_exp]
  congr 1
  have hj : ∀ j, ((k j : ℂ) * θ j).im = (k j : ℝ) * (θ j).im := by
    intro j
    simp [Complex.mul_im]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ∑ j, (k j : ℂ) * θ j =
      ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * ∑ j, (k j : ℂ) * θ j) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re, Complex.im_sum]
  simp only [hj]
  ring

/-- On the strip of width `ρ`, `|χ_k| ≤ e^{2πρ|k|₁}`. -/
theorem norm_character_le {ρ : ℝ} (k : Fin n → ℤ) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) :
    ‖character k θ‖ ≤ Real.exp (2 * Real.pi * ρ * Fourier.modeSize k) := by
  rw [norm_character]
  apply Real.exp_le_exp.mpr
  have h1 : ∀ j, -((k j : ℝ) * (θ j).im) ≤ ρ * |(k j : ℝ)| := by
    intro j
    calc -((k j : ℝ) * (θ j).im) ≤ |(k j : ℝ) * (θ j).im| := neg_le_abs _
      _ = |(k j : ℝ)| * |(θ j).im| := abs_mul _ _
      _ ≤ |(k j : ℝ)| * ρ := mul_le_mul_of_nonneg_left (hθ j).le (abs_nonneg _)
      _ = ρ * |(k j : ℝ)| := mul_comm _ _
  have h2 : -(∑ j, (k j : ℝ) * (θ j).im) ≤ ρ * Fourier.modeSize k := by
    rw [Fourier.modeSize, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => h1 j
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hpi]

/-- A shift of the real torus by `s` times an imaginary vector of size at most `ρ'` stays in the
strip of width `r` as soon as `|s| ρ' < r`. -/
private theorem shift_mem_complexStrip {ρ' r s : ℝ} {t : Fin n → ℝ} (ht : ∀ j, |t j| ≤ ρ')
    (hs : |s| * ρ' < r) (x : Fin n → ℝ) :
    (fun j => (x j : ℂ)) + s • (fun j => (t j : ℂ) * Complex.I) ∈ complexStrip n r := by
  intro j
  have him : (((fun j => (x j : ℂ)) + s • (fun j => (t j : ℂ) * Complex.I)) j).im =
      s * t j := by
    simp [Complex.mul_im]
  rw [him, abs_mul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (ht j) (abs_nonneg s)) hs

/-- **Imaginary shifts.** If `g` is holomorphic, bounded and `1`-periodic on the strip of width `ρ`
and `|t_j| ≤ ρ' < ρ`, then the torus average of `g` is unchanged when the real torus is moved to
`ℝⁿ + i t`. -/
theorem torusAverage_imag_shift {ρ ρ' A : ℝ} (hρ' : 0 ≤ ρ') (hρρ' : ρ' < ρ)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
    {t : Fin n → ℝ} (ht : ∀ j, |t j| ≤ ρ') :
    torusAverage (fun x : Fin n → ℝ =>
        g ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I)) =
      torusAverage (fun x : Fin n → ℝ => g (fun j => (x j : ℂ))) := by
  set w : Fin n → ℂ := fun j => (t j : ℂ) * Complex.I with hw
  -- A margin `δ` and a parameter range `|s| < 1 + ε` keeping the shifted torus in `T_{ρ-δ}`.
  obtain ⟨δ, ε, hδ, hε, hsmall⟩ : ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧
      ∀ s : ℝ, |s| < 1 + ε → |s| * ρ' < ρ - δ := by
    have hρ1 : 0 < ρ' + 1 := by linarith
    refine ⟨(ρ - ρ') / 2, (ρ - ρ') / 2 / (ρ' + 1), by linarith,
      div_pos (by linarith) hρ1, fun s hs => ?_⟩
    have key : (ρ - ρ') / 2 / (ρ' + 1) * ρ' < (ρ - ρ') / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hρ1]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hs.le hρ']
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun z hz j => by
    have := hz j
    linarith
  have hmem : ∀ (x : Fin n → ℝ) (s : ℝ), |s| < 1 + ε →
      (fun j => (x j : ℂ)) + s • w ∈ complexStrip n (ρ - δ) := fun x s hs =>
    shift_mem_complexStrip ht (hsmall s hs) x
  have hL : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hDg : ContinuousOn (fderiv ℂ g) (complexStrip n ρ) :=
    (differentiableOn_fderiv_of_isOpen_pi (isOpen_complexStrip n ρ) hg).continuousOn
  have hDgA : ∀ z ∈ complexStrip n (ρ - δ), ‖fderiv ℂ g z‖ ≤ A / δ := fun z hz =>
    norm_fderiv_le_of_mem_complexStrip hg hA hδ hz
  have hcont : ∀ s : ℝ, |s| < 1 + ε →
      Continuous fun x : Fin n → ℝ => g ((fun j => (x j : ℂ)) + s • w) := fun s hs =>
    hg.continuousOn.comp_continuous (hL.add continuous_const)
      fun x => hsub (hmem x s hs)
  have hcont' : ∀ s : ℝ, |s| < 1 + ε →
      Continuous fun x : Fin n → ℝ => fderiv ℂ g ((fun j => (x j : ℂ)) + s • w) w :=
    fun s hs => (hDg.comp_continuous (hL.add continuous_const)
      fun x => hsub (hmem x s hs)).clm_apply continuous_const
  have hderiv : ∀ (x : Fin n → ℝ) (s : ℝ), |s| < 1 + ε →
      HasDerivAt (fun s : ℝ => g ((fun j => (x j : ℂ)) + s • w))
        (fderiv ℂ g ((fun j => (x j : ℂ)) + s • w) w) s := by
    intro x s hs
    have hgd : HasFDerivAt g (fderiv ℂ g ((fun j => (x j : ℂ)) + s • w))
        ((fun j => (x j : ℂ)) + s • w) :=
      (hg.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds
        (hsub (hmem x s hs)))).hasFDerivAt
    have hpath : HasDerivAt (fun s : ℝ => (fun j => (x j : ℂ)) + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add (fun j => (x j : ℂ))
    exact (hgd.restrictScalars ℝ).comp_hasDerivAt s hpath
  -- The average of the shifted function as a function of the shift size.
  set φ : ℝ → ℂ := fun s => torusAverage fun x : Fin n → ℝ =>
    g ((fun j => (x j : ℂ)) + s • w) with hφ_def
  have hφ : ∀ s₀ ∈ Icc (0 : ℝ) 1, HasDerivAt φ (torusAverage fun x : Fin n → ℝ =>
      fderiv ℂ g ((fun j => (x j : ℂ)) + s₀ • w) w) s₀ := by
    intro s₀ hs₀
    have hball : ∀ s ∈ Metric.ball s₀ ε, |s| < 1 + ε := by
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq] at hs
      have h1 := abs_sub_abs_le_abs_sub s s₀
      rw [abs_of_nonneg hs₀.1] at h1
      linarith [hs₀.2]
    have hs₀' : |s₀| < 1 + ε := hball s₀ (Metric.mem_ball_self hε)
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1))
      (F := fun s x => g ((fun j => (x j : ℂ)) + s • w))
      (F' := fun s x => fderiv ℂ g ((fun j => (x j : ℂ)) + s • w) w)
      (bound := fun _ => A / δ * ‖w‖) (Metric.ball_mem_nhds s₀ hε)
      (eventually_of_mem (Metric.ball_mem_nhds s₀ hε)
        fun s hs => (hcont s (hball s hs)).aestronglyMeasurable)
      (integrableOn_unitCube_of_continuous (hcont s₀ hs₀'))
      (hcont' s₀ hs₀').aestronglyMeasurable
      (ae_of_all _ fun x s hs =>
        ((fderiv ℂ g _).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (hDgA _ (hmem x s (hball s hs))) (norm_nonneg w)))
      (integrableOn_unitCube_of_continuous continuous_const)
      (ae_of_all _ fun x s hs => hderiv x s (hball s hs))
    exact h.2
  -- The derivative vanishes: it is the average of a periodic derivative.
  have hzero : ∀ s₀ ∈ Icc (0 : ℝ) 1, (torusAverage fun x : Fin n → ℝ =>
      fderiv ℂ g ((fun j => (x j : ℂ)) + s₀ • w) w) = 0 := by
    intro s₀ hs₀
    have hs1 : |s₀| ≤ 1 := by rw [abs_of_nonneg hs₀.1]; exact hs₀.2
    have hmaps : ∀ θ ∈ complexStrip n (ρ - ρ'), θ + s₀ • w ∈ complexStrip n ρ := by
      intro θ hθ j
      have him : ((θ + s₀ • w) j).im = (θ j).im + s₀ * t j := by
        simp [hw, Complex.mul_im]
      rw [him]
      have h1 : |s₀ * t j| ≤ 1 * ρ' := by
        rw [abs_mul]
        exact mul_le_mul hs1 (ht j) (abs_nonneg _) zero_le_one
      have h2 := hθ j
      calc |(θ j).im + s₀ * t j| ≤ |(θ j).im| + |s₀ * t j| := abs_add_le _ _
        _ < (ρ - ρ') + 1 * ρ' := by linarith
        _ = ρ := by ring
    have hf : DifferentiableOn ℂ (fun θ => g (θ + s₀ • w)) (complexStrip n (ρ - ρ')) :=
      hg.comp (differentiableOn_id.add_const _) fun θ hθ => hmaps θ hθ
    have hfp : ∀ (i : Fin n) z, z ∈ complexStrip n (ρ - ρ') →
        g (z + Pi.single i 1 + s₀ • w) = g (z + s₀ • w) := by
      intro i z hz
      rw [add_right_comm]
      exact hp i _ (hmaps z hz)
    have h := torusAverage_complex_direction_eq_zero (sub_pos.mpr hρρ') hf hfp w
    simpa only [fderiv_comp_add_right] using h
  have hconst := constant_of_has_deriv_right_zero (f := φ) (a := 0) (b := 1)
    (fun s hs => (hφ s hs).continuousAt.continuousWithinAt)
    (fun s hs => by
      have h := hφ s (Ico_subset_Icc_self hs)
      rw [hzero s (Ico_subset_Icc_self hs)] at h
      exact h.hasDerivWithinAt)
    1 (right_mem_Icc.mpr zero_le_one)
  simpa [hφ_def] using hconst

/-- **Coefficient decay** (blueprint `bp:p1:decay`). If `u` is holomorphic, `1`-periodic and
bounded by `A` on the strip of width `ρ`, then `|û_k| ≤ e^{-2π|k|₁ρ'} A` for `0 ≤ ρ' < ρ`. -/
theorem norm_torusCoeff_le_of_lt {ρ ρ' A : ℝ} (hρ' : 0 ≤ ρ') (hρρ' : ρ' < ρ)
    {u : (Fin n → ℂ) → ℂ} (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖u z‖ ≤ A) (k : Fin n → ℤ) :
    ‖torusCoeff (fun x => u (fun j => (x j : ℂ))) k‖ ≤
      Real.exp (-(2 * Real.pi * ρ' * Fourier.modeSize k)) * A := by
  set g : (Fin n → ℂ) → ℂ := fun θ => character (-k) θ * u θ with hg_def
  have hg : DifferentiableOn ℂ g (complexStrip n ρ) :=
    (differentiable_character (-k)).differentiableOn.mul hu
  have hgp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z := by
    intro i z hz
    simp only [hg_def, character_add_single, hp i z hz]
  have hgA : ∀ z ∈ complexStrip n ρ,
      ‖g z‖ ≤ Real.exp (2 * Real.pi * ρ * Fourier.modeSize (-k)) * A := by
    intro z hz
    rw [hg_def, norm_mul]
    exact mul_le_mul (norm_character_le (-k) hz) (hA z hz) (norm_nonneg _)
      (Real.exp_pos _).le
  obtain ⟨t, ht_def⟩ : ∃ t : Fin n → ℝ, t = fun j => if 0 ≤ k j then -ρ' else ρ' := ⟨_, rfl⟩
  have htj : ∀ j, t j = if 0 ≤ k j then -ρ' else ρ' := fun j => by rw [ht_def]
  have ht : ∀ j, |t j| ≤ ρ' := by
    intro j
    rw [htj j]
    split_ifs <;> simp [abs_of_nonneg hρ']
  have hshift := torusAverage_imag_shift hρ' hρρ' hg hgp hgA ht
  have hcoeff : torusCoeff (fun x => u (fun j => (x j : ℂ))) k =
      torusAverage (fun x : Fin n → ℝ => g (fun j => (x j : ℂ))) := rfl
  rw [hcoeff, ← hshift]
  apply norm_torusAverage_le
  intro x _
  have hmem : (fun j => (x j : ℂ)) + (fun j => (t j : ℂ) * Complex.I) ∈ complexStrip n ρ := by
    intro j
    have him : (((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I) j).im = t j := by
      simp [Complex.mul_im]
    rw [him]
    exact lt_of_le_of_lt (ht j) hρρ'
  rw [hg_def]
  simp only
  rw [norm_mul]
  refine mul_le_mul (le_of_eq ?_) (hA _ hmem) (norm_nonneg _) (Real.exp_pos _).le
  rw [norm_character]
  congr 1
  have hsum : ∑ j, (((-k) j : ℤ) : ℝ) *
      (((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I) j).im =
      ρ' * Fourier.modeSize k := by
    rw [Fourier.modeSize, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have him : (((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I) j).im = t j := by
      simp [Complex.mul_im]
    rw [him, htj j, Pi.neg_apply, Int.cast_neg]
    split_ifs with h
    · have h' : (0 : ℝ) ≤ k j := by exact_mod_cast h
      rw [abs_of_nonneg h']
      ring
    · have h' : (k j : ℝ) < 0 := by exact_mod_cast not_le.mp h
      rw [abs_of_neg h']
      ring
  rw [hsum]
  ring

/-- **Coefficient decay at the full width** (blueprint `bp:p1:decay`, limit form):
`|û_k| ≤ e^{-2π|k|₁ρ} A`. -/
theorem norm_torusCoeff_le {ρ A : ℝ} (hρ : 0 < ρ)
    {u : (Fin n → ℂ) → ℂ} (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖u z‖ ≤ A) (k : Fin n → ℤ) :
    ‖torusCoeff (fun x => u (fun j => (x j : ℂ))) k‖ ≤
      Real.exp (-(2 * Real.pi * ρ * Fourier.modeSize k)) * A := by
  have hc : Continuous fun r : ℝ => Real.exp (-(2 * Real.pi * r * Fourier.modeSize k)) * A := by
    fun_prop
  have hlim : Tendsto (fun r : ℝ => Real.exp (-(2 * Real.pi * r * Fourier.modeSize k)) * A)
      (𝓝[<] ρ) (𝓝 (Real.exp (-(2 * Real.pi * ρ * Fourier.modeSize k)) * A)) :=
    (hc.tendsto ρ).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hρ] with r hr
  exact norm_torusCoeff_le_of_lt hr.1.le hr.2 hu hp hA k

end KAM

end
