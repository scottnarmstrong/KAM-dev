/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.FourierBasic
public import KAM.Strip.Fourier
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bessel's inequality for shifted Fourier coefficients

For a continuous `1`-periodic `v : ℝⁿ → ℂ` with `|v| ≤ A`, every finite set `s` of modes satisfies
`∑_{k∈s} |v̂_k|² ≤ A²` (`KAM.sum_sq_torusCoeff_le`, from Mathlib's torus Parseval identity).

If `g` is holomorphic, `1`-periodic and bounded on `T_ρ` and `|t_j| ≤ ρ' < ρ`, the function
`x ↦ g(x + i t)` has coefficients `ĝ_k e^{-2π k·t}` (`KAM.torusCoeff_imag_shift`). Averaging
Bessel over the `2ⁿ` corners `t = -ρ' s`, `s ∈ {±1}ⁿ`, gives
`∑_{k∈s} |ĝ_k|² e^{4πρ'|k|₁} ≤ 2ⁿ A²` (`KAM.sum_sq_torusCoeff_exp_le`).
-/

public noncomputable section

open MeasureTheory

namespace KAM

section Bessel

/-- Mathlib normalises the measure on `ℝ / ℤ` this way in its torus Fourier file; we need the same
instance to apply its Parseval identity. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle : Measure UnitAddCircle))

variable {n : ℕ}

/-- **Bessel's inequality** for a continuous `1`-periodic function bounded by `A`. -/
theorem sum_sq_torusCoeff_le {v : (Fin n → ℝ) → ℂ} {A : ℝ} (hv : Continuous v)
    (hp : ∀ (i : Fin n) x, v (x + Pi.single i 1) = v x) (hA : ∀ x, ‖v x‖ ≤ A)
    (s : Finset (Fin n → ℤ)) : ∑ k ∈ s, ‖torusCoeff v k‖ ^ 2 ≤ A ^ 2 := by
  let F : C(UnitAddTorus (Fin n), ℂ) := ⟨torusLift v, continuous_torusLift hv hp⟩
  let L : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))) := F.toLp 2 volume ℂ
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin n) L
  have hc : ∀ k, UnitAddTorus.mFourierCoeff L k = torusCoeff v k := fun k =>
    (UnitAddTorus.mFourierCoeff_toLp F k).trans (mFourierCoeff_torusLift hp k)
  simp only [hc] at h
  have hFA : ∀ t, ‖F t‖ ≤ A := fun t => by
    obtain ⟨x, rfl⟩ := surjective_torusProj t
    exact (show F (torusProj x) = v x from torusLift_torusProj hp x) ▸ hA x
  have hint : ∫ t, ‖L t‖ ^ 2 ≤ A ^ 2 := by
    have hae : ∀ᵐ t ∂(volume : Measure (UnitAddTorus (Fin n))), ‖L t‖ ^ 2 ≤ A ^ 2 := by
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
        (μ := (volume : Measure (UnitAddTorus (Fin n)))) F] with t ht
      rw [ht]
      exact pow_le_pow_left₀ (norm_nonneg _) (hFA t) 2
    calc ∫ t, ‖L t‖ ^ 2 ≤ ∫ _t, A ^ 2 ∂(volume : Measure (UnitAddTorus (Fin n))) :=
          integral_mono_ae (Lp.memLp L).norm.integrable_sq (integrable_const _) hae
      _ = A ^ 2 := by simp
  exact (sum_le_hasSum s (fun _ _ => by positivity) h).trans hint


open Set Filter MeasureTheory

variable {n : ℕ}

/-- The imaginary shift of the real torus by `t`. -/
private theorem shift_mem_strip {ρ ρ' : ℝ} (hρρ' : ρ' < ρ) {t : Fin n → ℝ}
    (ht : ∀ j, |t j| ≤ ρ') (x : Fin n → ℝ) :
    ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I) ∈ complexStrip n ρ := by
  intro j
  have him : (((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I) j).im = t j := by
    simp [Complex.mul_im]
  rw [him]
  exact lt_of_le_of_lt (ht j) hρρ'

/-- **Shifted coefficients.** For `g` holomorphic, `1`-periodic and bounded on `T_ρ` and
`|t_j| ≤ ρ' < ρ`, the function `x ↦ g(x + i t)` has coefficients `ĝ_k e^{-2π k·t}`. -/
theorem torusCoeff_imag_shift {ρ ρ' A : ℝ} (hρ' : 0 ≤ ρ') (hρρ' : ρ' < ρ)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A) {t : Fin n → ℝ} (ht : ∀ j, |t j| ≤ ρ')
    (k : Fin n → ℤ) :
    torusCoeff (fun x : Fin n → ℝ => g ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I))
        k =
      torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k *
        (Real.exp (-(2 * Real.pi * ∑ j, (k j : ℝ) * t j)) : ℂ) := by
  set G : (Fin n → ℂ) → ℂ := fun θ => character (-k) θ * g θ with hG_def
  have hGd : DifferentiableOn ℂ G (complexStrip n ρ) :=
    (differentiable_character (-k)).differentiableOn.mul hg
  have hGp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → G (z + Pi.single i 1) = G z := by
    intro i z hz
    simp only [hG_def, character_add_single, hp i z hz]
  have hGA : ∀ z ∈ complexStrip n ρ,
      ‖G z‖ ≤ Real.exp (2 * Real.pi * ρ * Fourier.modeSize (-k)) * A := by
    intro z hz
    rw [hG_def, norm_mul]
    exact mul_le_mul (norm_character_le (-k) hz) (hA z hz) (norm_nonneg _) (Real.exp_pos _).le
  have hshift := torusAverage_imag_shift hρ' hρρ' hGd hGp hGA ht
  set c : ℝ := Real.exp (2 * Real.pi * ∑ j, (k j : ℝ) * t j) with hc_def
  have hcpos : 0 < c := Real.exp_pos _
  have hchar : character (-k) (fun j => (t j : ℂ) * Complex.I) = (c : ℂ) := by
    rw [character, hc_def, Complex.ofReal_exp]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.neg_apply, Int.cast_neg]
    linear_combination (-(2 * (Real.pi : ℂ) * (k j : ℂ) * (t j : ℂ))) * Complex.I_sq
  have hLHS : torusAverage (fun x : Fin n → ℝ =>
      G ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I)) =
      (c : ℂ) * torusCoeff (fun x : Fin n → ℝ =>
        g ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I)) k := by
    unfold torusCoeff torusAverage
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hG_def, character_add, hchar]
    ring
  have hRHS : torusAverage (fun x : Fin n → ℝ => G fun j => (x j : ℂ)) =
      torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k := rfl
  rw [hLHS, hRHS] at hshift
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  rw [← hshift]
  have : (Real.exp (-(2 * Real.pi * ∑ j, (k j : ℝ) * t j)) : ℂ) * (c : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hc_def, ← Real.exp_add]
    simp
  generalize torusCoeff (fun x : Fin n → ℝ =>
    g ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I)) k = X
  linear_combination (-X) * this

/-- Bessel's inequality for the shifted function `x ↦ g(x + i t)`. -/
theorem sum_sq_torusCoeff_shift_le {ρ ρ' A : ℝ} (hρ' : 0 ≤ ρ') (hρρ' : ρ' < ρ)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A) {t : Fin n → ℝ} (ht : ∀ j, |t j| ≤ ρ')
    (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, ‖torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (-(4 * Real.pi * ∑ j, (k j : ℝ) * t j)) ≤ A ^ 2 := by
  have hmem := shift_mem_strip hρρ' ht
  have hcont : Continuous fun x : Fin n → ℝ =>
      g ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I) :=
    hg.continuousOn.comp_continuous
      ((continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)).add
        continuous_const) hmem
  have hper : ∀ (i : Fin n) (x : Fin n → ℝ),
      g ((fun j => ((x + Pi.single i (1 : ℝ) : Fin n → ℝ) j : ℂ)) +
          fun j => (t j : ℂ) * Complex.I) =
        g ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I) := by
    intro i x
    have : ((fun j => ((x + Pi.single i (1 : ℝ) : Fin n → ℝ) j : ℂ)) +
          fun j => (t j : ℂ) * Complex.I) =
        ((fun j => (x j : ℂ)) + fun j => (t j : ℂ) * Complex.I) + Pi.single i 1 := by
      funext j
      by_cases h : j = i
      · subst h
        simp; ring
      · simp [h]
    rw [this]
    exact hp i _ (hmem x)
  have hB := sum_sq_torusCoeff_le hcont hper (fun x => hA _ (hmem x)) s
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) hB
  rw [torusCoeff_imag_shift hρ' hρρ' hg hp hA ht k, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring_nf


/-- **Corner weights.** `∑_{k∈s} |ĝ_k|² e^{4πρ'|k|₁} ≤ 2ⁿ A²` for every finite set `s` of modes and
`0 ≤ ρ' < ρ`: sum Bessel over the corners `t = ∓ρ'` of the shift. -/
theorem sum_sq_torusCoeff_exp_le {ρ ρ' A : ℝ} (hρ' : 0 ≤ ρ') (hρρ' : ρ' < ρ)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A) (s : Finset (Fin n → ℤ)) :
    ∑ k ∈ s, ‖torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k‖ ^ 2 *
        Real.exp (4 * Real.pi * ρ' * Fourier.modeSize k) ≤ 2 ^ n * A ^ 2 := by
  set a : (Fin n → ℤ) → ℝ := fun k => ‖torusCoeff (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) k‖ ^ 2
    with ha_def
  let t : (Fin n → Bool) → Fin n → ℝ := fun σ j => if σ j then -ρ' else ρ'
  have ht : ∀ σ j, |t σ j| ≤ ρ' := fun σ j => by
    simp only [t]
    split_ifs <;> simp [abs_of_nonneg hρ']
  have hcorner : ∀ k : Fin n → ℤ, Real.exp (4 * Real.pi * ρ' * Fourier.modeSize k) ≤
      ∑ σ : Fin n → Bool, Real.exp (-(4 * Real.pi * ∑ j, (k j : ℝ) * t σ j)) := by
    intro k
    have hterm : ∀ σ : Fin n → Bool, 0 ≤ Real.exp (-(4 * Real.pi * ∑ j, (k j : ℝ) * t σ j)) :=
      fun σ => (Real.exp_pos _).le
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (fun σ _ => hterm σ) (Finset.mem_univ fun j => decide (0 ≤ k j)))
    congr 1
    rw [Fourier.modeSize, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [t]
    by_cases h : 0 ≤ k j
    · have h' : (0 : ℝ) ≤ k j := by exact_mod_cast h
      simp [h, abs_of_nonneg h']
      ring
    · have h' : (k j : ℝ) < 0 := by exact_mod_cast not_le.mp h
      simp [h, abs_of_neg h']
      ring
  calc ∑ k ∈ s, a k * Real.exp (4 * Real.pi * ρ' * Fourier.modeSize k)
      ≤ ∑ k ∈ s, a k * ∑ σ : Fin n → Bool, Real.exp (-(4 * Real.pi * ∑ j, (k j : ℝ) * t σ j)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hcorner k) (by positivity)
    _ = ∑ σ : Fin n → Bool, ∑ k ∈ s, a k * Real.exp (-(4 * Real.pi * ∑ j, (k j : ℝ) * t σ j)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ _σ : Fin n → Bool, A ^ 2 :=
        Finset.sum_le_sum fun σ _ => sum_sq_torusCoeff_shift_le hρ' hρρ' hg hp hA (ht σ) s
    _ = 2 ^ n * A ^ 2 := by simp

end Bessel

end KAM

end
