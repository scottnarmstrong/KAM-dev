/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic

/-!
# Secular spectrum: Euclidean norms, sorted spectrum, rotations

Blueprint P, Part 9 (`bpP:p9:conv#data`, `bpP:p9:norm-compare`): the explicit Euclidean length
`length2` on `Fin n → ℝ`, the Euclidean operator norm `op2`, the max-norm operator norm `opMax`,
the Frobenius norm, the decreasingly sorted spectrum `sorted` of a Hermitian matrix and the
predicate `isSO`; the comparison lemmas `norm_compare` and `norm_compare_operator`.
The ambient Pi norm stays the max norm.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}
/-- Euclidean norms as explicit functions on the required Pi carriers. -/
def length2 (x : Vec n) : ℝ := √(∑ i, x i^2)
def op2 (M : Mat n) : ℝ := sSup {r | ∃ x : Vec n, length2 x = 1 ∧ r = length2 (M.mulVec x)}
def frobenius (M : Mat n) : ℝ := √(∑ i, ∑ j, M i j^2)
def sorted (M : Mat n) (hM : M.IsHermitian) (i : Fin n) : ℝ :=
  hM.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i.rev)
def isSO (R : Mat n) : Prop := R.transpose * R = 1 ∧ R.det = 1
def opMax (M : Mat n) : ℝ := sSup {r | ∃ x : Vec n, ‖x‖ = 1 ∧ r = ‖M.mulVec x‖}

lemma length2_nonneg (x : Vec n) : 0 ≤ length2 x := Real.sqrt_nonneg _

lemma length2_eq_zero {x : Vec n} (h : length2 x = 0) : x = 0 := by
  have h0 : ∑ i, x i ^ 2 = 0 := by
    have := (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg (x i))).1 h
    exact this
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 h0 i (Finset.mem_univ i)
  simpa using this

lemma length2_smul (c : ℝ) (x : Vec n) : length2 (c • x) = |c| * length2 x := by
  unfold length2
  have : ∑ i, (c • x) i ^ 2 = c ^ 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp [mul_pow]
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma norm_le_length2 (x : Vec n) : ‖x‖ ≤ length2 x := by
  refine (pi_norm_le_iff_of_nonneg (length2_nonneg x)).2 fun i => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt
    (Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i))

lemma length2_le_sqrt_mul_norm (x : Vec n) : length2 x ≤ √n * ‖x‖ := by
  unfold length2
  rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg n)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [← sq_abs (x i)]
        exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using norm_le_pi_norm x i) 2
    _ = n * ‖x‖ ^ 2 := by simp

lemma length2_mulVec_le (M : Mat n) (x : Vec n) :
    length2 (M.mulVec x) ≤ frobenius M * length2 x := by
  unfold length2 frobenius
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (M i j))]
  refine Real.sqrt_le_sqrt ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => by
    simpa [Matrix.mulVec, dotProduct] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) x

lemma op2_bddAbove (M : Mat n) :
    BddAbove {r | ∃ x : Vec n, length2 x = 1 ∧ r = length2 (M.mulVec x)} :=
  ⟨frobenius M, by
    rintro r ⟨x, hx, rfl⟩
    simpa [hx] using length2_mulVec_le M x⟩

lemma op2_nonneg (M : Mat n) : 0 ≤ op2 M :=
  Real.sSup_nonneg (by rintro r ⟨x, -, rfl⟩; exact length2_nonneg _)

lemma length2_mulVec_le_op2 (M : Mat n) (x : Vec n) :
    length2 (M.mulVec x) ≤ op2 M * length2 x := by
  by_cases h : length2 x = 0
  · rw [length2_eq_zero h]; simp [length2]
  have hp : 0 < length2 x := lt_of_le_of_ne (length2_nonneg x) (Ne.symm h)
  have h1 : length2 ((length2 x)⁻¹ • x) = 1 := by
    rw [length2_smul, abs_of_pos (inv_pos.2 hp), inv_mul_cancel₀ h]
  have := le_csSup (op2_bddAbove M) ⟨_, h1, rfl⟩
  rw [Matrix.mulVec_smul, length2_smul, abs_of_pos (inv_pos.2 hp)] at this
  have h2 := mul_le_mul_of_nonneg_left this hp.le
  rwa [← mul_assoc, mul_inv_cancel₀ h, one_mul, mul_comm] at h2

theorem norm_compare (x : Vec n) (M : Mat n) :
    ‖x‖ ≤ length2 x ∧ length2 x ≤ √n * ‖x‖ ∧ op2 M ≤ frobenius M := by
  refine ⟨norm_le_length2 x, length2_le_sqrt_mul_norm x, ?_⟩
  refine Real.sSup_le ?_ (Real.sqrt_nonneg _)
  rintro r ⟨y, hy, rfl⟩
  simpa [hy] using length2_mulVec_le M y

lemma opMax_bddAbove (M : Mat n) :
    BddAbove {r | ∃ x : Vec n, ‖x‖ = 1 ∧ r = ‖M.mulVec x‖} :=
  ⟨frobenius M * √n, by
    rintro r ⟨x, hx, rfl⟩
    calc ‖M.mulVec x‖ ≤ length2 (M.mulVec x) := norm_le_length2 _
      _ ≤ frobenius M * length2 x := length2_mulVec_le M x
      _ ≤ frobenius M * √n := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        simpa [hx] using length2_le_sqrt_mul_norm x⟩

lemma opMax_nonneg (M : Mat n) : 0 ≤ opMax M :=
  Real.sSup_nonneg (by rintro r ⟨x, -, rfl⟩; exact norm_nonneg _)

lemma norm_mulVec_le_opMax (M : Mat n) (x : Vec n) :
    ‖M.mulVec x‖ ≤ opMax M * ‖x‖ := by
  by_cases h : ‖x‖ = 0
  · rw [norm_eq_zero.1 h]; simp
  have hp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm h)
  have h1 : ‖(‖x‖)⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]
  have := le_csSup (opMax_bddAbove M) ⟨_, h1, rfl⟩
  rw [Matrix.mulVec_smul, norm_smul, norm_inv, norm_norm] at this
  have h2 := mul_le_mul_of_nonneg_left this hp.le
  rwa [← mul_assoc, mul_inv_cancel₀ h, one_mul, mul_comm] at h2

theorem norm_compare_operator (M : Mat n) :
    opMax M ≤ √n * op2 M ∧ op2 M ≤ √n * opMax M := by
  constructor
  · refine Real.sSup_le ?_ (mul_nonneg (Real.sqrt_nonneg _) (op2_nonneg M))
    rintro r ⟨x, hx, rfl⟩
    calc ‖M.mulVec x‖ ≤ length2 (M.mulVec x) := norm_le_length2 _
      _ ≤ op2 M * length2 x := length2_mulVec_le_op2 M x
      _ ≤ op2 M * √n := by
        refine mul_le_mul_of_nonneg_left ?_ (op2_nonneg M)
        simpa [hx] using length2_le_sqrt_mul_norm x
      _ = √n * op2 M := mul_comm _ _
  · refine Real.sSup_le ?_ (mul_nonneg (Real.sqrt_nonneg _) (opMax_nonneg M))
    rintro r ⟨x, hx, rfl⟩
    calc length2 (M.mulVec x) ≤ √n * ‖M.mulVec x‖ := length2_le_sqrt_mul_norm _
      _ ≤ √n * (opMax M * ‖x‖) :=
        mul_le_mul_of_nonneg_left (norm_mulVec_le_opMax M x) (Real.sqrt_nonneg _)
      _ ≤ √n * (opMax M * 1) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (opMax_nonneg M))
          (Real.sqrt_nonneg _)
        simpa using (norm_le_length2 x).trans_eq hx
      _ = √n * opMax M := by rw [mul_one]

end SecularSpectrum

end KAM.Planetary
