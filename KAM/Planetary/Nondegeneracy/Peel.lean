/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularForm.LaplaceCoeff
public import KAM.Planetary.SecularForm.LaplaceSeries
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Peeling the innermost planet

Blueprint P, Part 10 (`bpP:p10:laplace-bounds`, `bpP:p10:formula69`, `bpP:p10:peel`): the Laplace
coefficients `b_{3/2}^{(1)}, b_{3/2}^{(2)}` for small argument, the resulting two-sided bounds
(Formula 69 with remainders) on `pairA`, `pairB`, and the structure of the secular matrix when the
innermost axis tends to `0`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-- The ratio of consecutive terms of the `b_{3/2}^{(k)}` series, `k ≥ 1`, is at most `2 α²`. -/
theorem laplaceTerm_succ_le {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (q : ℕ) :
    laplaceTerm (3/2) k (q+1) α ≤ 2 * α^2 * laplaceTerm (3/2) k q α := by
  have hT : 0 ≤ laplaceTerm (3/2) k q α := laplaceTerm_nonneg (by norm_num) hα k q
  have hq : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have key : laplaceTerm (3/2) k (q+1) α =
      laplaceTerm (3/2) k q α * (((3/2 + (q+k)) * (3/2 + q)) / (((q:ℝ)+k+1) * (q+1)) * α^2) := by
    simp only [laplaceTerm, poch_succ, show q + 1 + k = (q + k) + 1 by ring, poch_succ,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      show 2 * (q + 1) + k = (2 * q + k) + 2 by ring, pow_add]
    have h1 : (0:ℝ) < (q + k).factorial := by exact_mod_cast Nat.factorial_pos _
    have h2 : (0:ℝ) < q.factorial := by exact_mod_cast Nat.factorial_pos _
    field_simp
  rw [key]
  have hr : ((3/2 + ((q:ℝ)+k)) * (3/2 + q)) / (((q:ℝ)+k+1) * (q+1)) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hq (by linarith : (0:ℝ) ≤ k - 1)]
  have : ((3/2 + ((q:ℝ)+k)) * (3/2 + q)) / (((q:ℝ)+k+1) * (q+1)) * α^2 ≤ 2 * α^2 :=
    mul_le_mul_of_nonneg_right hr (sq_nonneg α)
  nlinarith

theorem laplaceTerm_le_geom {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (q : ℕ) :
    laplaceTerm (3/2) k q α ≤ laplaceTerm (3/2) k 0 α * (2 * α^2)^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc laplaceTerm (3/2) k (q+1) α ≤ 2 * α^2 * laplaceTerm (3/2) k q α :=
          laplaceTerm_succ_le hk hα q
      _ ≤ 2 * α^2 * (laplaceTerm (3/2) k 0 α * (2 * α^2)^q) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ = laplaceTerm (3/2) k 0 α * (2 * α^2)^(q+1) := by ring

/-- The two-sided bounds for one index `k ∈ {1,2}`, with first term `c α^k`. -/
theorem laplace_bounds_aux {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1/2) :
    laplaceTerm (3/2) k 0 α ≤ laplace_def (3/2) k α ∧
    laplace_def (3/2) k α ≤ laplaceTerm (3/2) k 0 α * (1 + 4 * α^2) := by
  have hα1' : α < 1 := by linarith
  have hS := hasSum_laplaceTerm (by norm_num : (0:ℝ) < 3/2) hα hα1' k
  have hx : 2 * α^2 < 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · exact le_hasSum hS 0 fun q _ => laplaceTerm_nonneg (by norm_num) hα k q
  · have hG : HasSum (fun q : ℕ => laplaceTerm (3/2) k 0 α * (2 * α^2)^q)
        (laplaceTerm (3/2) k 0 α * (1 - 2 * α^2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) hx).mul_left _
    refine (hasSum_le (fun q => laplaceTerm_le_geom hk hα q) hS hG).trans ?_
    have hT : 0 ≤ laplaceTerm (3/2) k 0 α := laplaceTerm_nonneg (by norm_num) hα k 0
    refine mul_le_mul_of_nonneg_left ?_ hT
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    have h4 : 0 ≤ 1 - 4 * α^2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg α) h4]

theorem laplace_bounds {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1/2) :
    (3/2)*α ≤ laplace_def (3/2) 1 α ∧
    laplace_def (3/2) 1 α ≤ (3/2)*α*(1+4*α^2) ∧
    (15/8)*α^2 ≤ laplace_def (3/2) 2 α ∧
    laplace_def (3/2) 2 α ≤ (15/8)*α^2*(1+4*α^2) := by
  have h1 := laplace_bounds_aux (k := 1) le_rfl hα hα1
  have h2 := laplace_bounds_aux (k := 2) (by norm_num) hα hα1
  have e1 : laplaceTerm (3/2) 1 0 α = (3/2) * α := by
    simp [laplaceTerm, poch]
  have e2 : laplaceTerm (3/2) 2 0 α = (15/8) * α^2 := by
    simp [laplaceTerm, poch, Finset.prod_range_succ]; norm_num
  rw [e1] at h1; rw [e2] at h2
  exact ⟨by simpa using h1.1, by simpa using h1.2, by simpa using h2.1, by simpa using h2.2⟩

end Nondegeneracy
end KAM.Planetary
