/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.BodyVector
public import KAM.Frozen.Planetary.Defs.PlaneSq
public import KAM.Frozen.Planetary.Defs.PlaneLength

/-!
# Complexified plane squares and their principal square roots

Source: `LP:MAIN L8 (266–268)`, track LP, non-frozen.

`cDot v = ∑ v_k²` is the *bilinear* complex dot product on `Fin 2 → ℂ` (never the Hermitian norm).
* `re_cDot_ge`: if `w` is within `ε` (coordinatewise) of a real vector `u` with `|u_k| ≤ Q`, then
  `Re (w·w) ≥ |u|² - (2ε² + 4Qε)` (MAIN `|w·w - |w₀|²| ≤ 2Qη + η²`, sup-norm form).
* `norm_inv_sqrt_le`, `differentiableOn_inv_sqrt_cDot`: if `Re z ≥ d²/2` then the principal
  branch `z^(1/2)` has reciprocal of norm `≤ √2/d`, holomorphic along any holomorphic family.

-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary

/-- Body `i`'s block of a complex coordinate vector (complexified `bodyVector`). -/
def cBody {n : ℕ} (q : Fin (n * 2) → ℂ) (i : Fin n) : Fin 2 → ℂ :=
  fun k => q (finProdFinEquiv (i, k))

/-- The bilinear complex dot product `v · v = ∑ v_k²` (not the Hermitian squared norm). -/
def cDot (v : Fin 2 → ℂ) : ℂ := ∑ k, v k ^ 2

theorem cDot_ofReal (u : Fin 2 → ℝ) : cDot (fun k => (u k : ℂ)) = (planeSq u : ℂ) := by
  simp [cDot, planeSq]

/-- On a real vector the principal square root of `v · v` is the Euclidean length. -/
theorem cDot_cpow_ofReal (u : Fin 2 → ℝ) :
    (cDot (fun k => (u k : ℂ))) ^ (1 / 2 : ℂ) = (planeLength u : ℂ) := by
  have h0 : 0 ≤ planeSq u := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h := Complex.ofReal_cpow h0 (1 / 2)
  rw [cDot_ofReal]
  unfold planeLength
  rw [Real.sqrt_eq_rpow]
  push_cast at h ⊢
  exact h.symm

/-- Coordinatewise perturbation estimate: `Re (w · w) ≥ |u|² - (2ε² + 4Qε)`. -/
theorem re_cDot_ge {w : Fin 2 → ℂ} {u : Fin 2 → ℝ} {ε Q : ℝ}
    (hw : ∀ k, ‖w k - (u k : ℂ)‖ ≤ ε) (hu : ∀ k, |u k| ≤ Q) :
    planeSq u - (2 * ε * ε + 4 * Q * ε) ≤ (cDot w).re := by
  have key : ∀ k, (u k) ^ 2 - ε * (ε + 2 * Q) ≤ (w k ^ 2).re := by
    intro k
    have h1 : ‖w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2‖ ≤ ε * (ε + 2 * Q) := by
      have e : w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2 = (w k - u k) * (w k + u k) := by ring
      rw [e, norm_mul]
      have h2 : ‖w k + (u k : ℂ)‖ ≤ ε + 2 * Q := by
        have : w k + (u k : ℂ) = (w k - u k) + 2 * (u k : ℂ) := by ring
        rw [this]
        refine (norm_add_le _ _).trans ?_
        have h3 : ‖(2 : ℂ) * (u k : ℂ)‖ ≤ 2 * Q := by
          rw [norm_mul, Complex.norm_real]
          simpa using mul_le_mul_of_nonneg_left (hu k) (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add (hw k) h3
      exact mul_le_mul (hw k) h2 (norm_nonneg _) ((norm_nonneg _).trans (hw k))
    have h4 : |(w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2).re| ≤ ‖w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2‖ :=
      Complex.abs_re_le_norm _
    have h5 : (w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2).re = (w k ^ 2).re - (u k) ^ 2 := by
      simp [← Complex.ofReal_pow]
    rw [h5] at h4
    linarith [(abs_le.1 (h4.trans h1)).1]
  have h0 := key 0
  have h1 := key 1
  simp only [cDot, planeSq, Fin.sum_univ_two, Complex.add_re]
  nlinarith

/-- `‖(z^(1/2))⁻¹‖ ≤ √2 / d` as soon as `Re z ≥ d²/2` (principal branch). -/
theorem norm_inv_sqrt_le {z : ℂ} {d : ℝ} (hd : 0 < d) (hz : d ^ 2 / 2 ≤ z.re) :
    ‖(z ^ (1 / 2 : ℂ))⁻¹‖ ≤ Real.sqrt 2 / d := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
    nlinarith
  have hn : ‖z ^ (1 / 2 : ℂ)‖ = ‖z‖ ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero hz0]
    simp
  have h1 : d ^ 2 / 2 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have h2 : d / Real.sqrt 2 ≤ ‖z‖ ^ (1 / 2 : ℝ) := by
    have : (d ^ 2 / 2) ^ (1 / 2 : ℝ) ≤ ‖z‖ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    refine le_trans (le_of_eq ?_) this
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.sqrt_sq hd.le]
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [norm_inv, hn]
  calc (‖z‖ ^ (1 / 2 : ℝ))⁻¹ ≤ (d / Real.sqrt 2)⁻¹ := inv_anti₀ (by positivity) h2
    _ = Real.sqrt 2 / d := by rw [inv_div]

/-- Along a holomorphic family `W` of complex plane vectors with `Re (W·W) > 0`, the reciprocal of
the principal square root of `W · W` is holomorphic. -/
theorem differentiableOn_inv_sqrt_cDot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : Set E} {W : E → Fin 2 → ℂ} (hW : ∀ k, DifferentiableOn ℂ (fun z => W z k) T)
    (hre : ∀ z ∈ T, 0 < (cDot (W z)).re) :
    DifferentiableOn ℂ (fun z => ((cDot (W z)) ^ (1 / 2 : ℂ))⁻¹) T := by
  have hD : DifferentiableOn ℂ (fun z => cDot (W z)) T := by
    unfold cDot
    exact DifferentiableOn.fun_sum fun k _ => (hW k).pow 2
  have hslit : ∀ z ∈ T, cDot (W z) ∈ Complex.slitPlane := fun z hz =>
    Complex.mem_slitPlane_iff.2 (Or.inl (hre z hz))
  refine DifferentiableOn.inv (hD.cpow (differentiableOn_const _) hslit) fun z hz => ?_
  have : cDot (W z) ≠ 0 := fun h => by simpa [h] using hre z hz
  simp [Complex.cpow_eq_zero_iff, this]

end KAM.Planetary.StrongAMD

end
