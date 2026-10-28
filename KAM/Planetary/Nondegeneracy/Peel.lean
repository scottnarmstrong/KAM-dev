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

theorem formula69 (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j)
    (hα : a i/a j ≤ 1/2) :
    ∃ θ θ' : ℝ, θ ∈ Icc 0 (4*(a i/a j)^2) ∧ θ' ∈ Icc 0 (4*(a i/a j)^2) ∧
      pairA D a i j = (3/8)*D.G*D.m i*D.m j*(a i/a j)^2/a j*(1+θ) ∧
      pairB D a i j = (15/32)*D.G*D.m i*D.m j*(a i/a j)^3/a j*(1+θ') := by
  have hi := ha.1 i
  have hj := ha.1 j
  have hα0 : 0 < a i / a j := div_pos hi hj
  obtain ⟨b1, b2, b3, b4⟩ := laplace_bounds hα0.le hα
  set α := a i / a j with hαdef
  refine ⟨laplace_def (3/2) 1 α / ((3/2)*α) - 1, laplace_def (3/2) 2 α / ((15/8)*α^2) - 1,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; nlinarith
  · rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; nlinarith
  · simp only [pairA, min_eq_left hij.le, max_eq_right hij.le]
    rw [← hαdef]
    field_simp
    rw [hαdef]
    field_simp
    ring
  · simp only [pairB, min_eq_left hij.le, max_eq_right hij.le]
    rw [← hαdef]
    field_simp
    rw [hαdef]
    field_simp
    ring

def outerData (D : Data (n+1)) (hn : 0 < n) : Data n :=
  ⟨D.G,D.m0,(fun i => D.m i.succ),D.hG,D.hm0,(fun i => D.hm i.succ),hn⟩
def peelError (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) : Mat (n+1) :=
  fun i j => coeffs D a i j - Fin.cases 0
    (fun i' => Fin.cases 0 (fun j' => coeffs (outerData D hn) (fun k => a k.succ) i' j') j) i

theorem pairA_bounds (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j)
    (hα : a i/a j ≤ 1/2) :
    0 ≤ pairA D a i j ∧ pairA D a i j ≤ (3/4)*D.G*D.m i*D.m j*a i^2/a j^3 := by
  obtain ⟨θ, θ', ⟨h1, h2⟩, -, hA, -⟩ := formula69 D ha hij hα
  have hi := ha.1 i
  have hj := ha.1 j
  have hα0 : 0 < a i / a j := div_pos hi hj
  have hG := D.hG
  have hmi := D.hm i
  have hmj := D.hm j
  have hsq : (a i / a j)^2 ≤ 1/4 := by nlinarith
  rw [hA]
  refine ⟨by positivity, ?_⟩
  have e : (3/8)*D.G*D.m i*D.m j*(a i/a j)^2/a j = (3/8) * (D.G*D.m i*D.m j*a i^2/a j^3) := by
    field_simp
  rw [e]
  have hP : 0 ≤ D.G*D.m i*D.m j*a i^2/a j^3 := by positivity
  have : (1 + θ) ≤ 2 := by nlinarith
  have e2 : (3/4)*D.G*D.m i*D.m j*a i^2/a j^3 = (3/4) * (D.G*D.m i*D.m j*a i^2/a j^3) := by ring
  rw [e2]
  nlinarith

theorem pairB_bounds (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j)
    (hα : a i/a j ≤ 1/2) :
    0 ≤ pairB D a i j ∧ pairB D a i j ≤ (15/16)*D.G*D.m i*D.m j*a i^3/a j^4 := by
  obtain ⟨θ, θ', -, ⟨h1, h2⟩, -, hB⟩ := formula69 D ha hij hα
  have hi := ha.1 i
  have hj := ha.1 j
  have hα0 : 0 < a i / a j := div_pos hi hj
  have hG := D.hG
  have hmi := D.hm i
  have hmj := D.hm j
  have hsq : (a i / a j)^2 ≤ 1/4 := by nlinarith
  rw [hB]
  refine ⟨by positivity, ?_⟩
  have e : (15/32)*D.G*D.m i*D.m j*(a i/a j)^3/a j = (15/32) * (D.G*D.m i*D.m j*a i^3/a j^4) := by
    field_simp
  rw [e]
  have hP : 0 ≤ D.G*D.m i*D.m j*a i^3/a j^4 := by positivity
  have : (1 + θ') ≤ 2 := by nlinarith
  have e2 : (15/16)*D.G*D.m i*D.m j*a i^3/a j^4 = (15/16) * (D.G*D.m i*D.m j*a i^3/a j^4) := by
    ring
  rw [e2]
  nlinarith

theorem sqrt_action (D : Data n) {a : Vec n} {i : Fin n} (hi : 0 < a i) :
    √(action D a i) = √(D.m i) * (D.G*D.m0)^((1:ℝ)/4) * (a i)^((1:ℝ)/4) := by
  have hk : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have h : 0 ≤ D.G * D.m0 * a i := by positivity
  unfold action
  rw [Real.sqrt_mul (D.hm i).le, Real.sqrt_eq_rpow (√(D.G * D.m0 * a i)),
    Real.sqrt_eq_rpow (D.G * D.m0 * a i), ← Real.rpow_mul h, Real.mul_rpow hk.le hi.le]
  norm_num
  ring

theorem action_pos (D : Data n) {a : Vec n} {i : Fin n} (hi : 0 < a i) : 0 < action D a i :=
  mul_pos (D.hm i) (Real.sqrt_pos.2 (by have := D.hG; have := D.hm0; positivity))

/-- Reindexing under `Fin.succ`: the outer system has the same coefficients. -/
theorem action_outer (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) (i : Fin n) :
    action (outerData D hn) (fun k => a k.succ) i = action D a i.succ := rfl

theorem pairA_outer (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) (i j : Fin n) :
    pairA (outerData D hn) (fun k => a k.succ) i j = pairA D a i.succ j.succ := by
  simp only [pairA, outerData, (Fin.strictMono_succ.monotone).map_min,
    (Fin.strictMono_succ.monotone).map_max]

theorem pairB_outer (D : Data (n+1)) (hn : 0 < n) (a : Vec (n+1)) (i j : Fin n) :
    pairB (outerData D hn) (fun k => a k.succ) i j = pairB D a i.succ j.succ := by
  simp only [pairB, outerData, (Fin.strictMono_succ.monotone).map_min,
    (Fin.strictMono_succ.monotone).map_max]

theorem pairA_comm (D : Data n) (a : Vec n) (i j : Fin n) : pairA D a i j = pairA D a j i := by
  simp only [pairA, min_comm i j, max_comm i j]

end Nondegeneracy
end KAM.Planetary
