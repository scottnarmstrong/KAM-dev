/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Secular spectrum: the Hadamard identity

Blueprint P, Part 9 (`bpP:p9:l75`, `stepP:p9:l75`): `dominance` and the expansion identity `l75`
for the quadratic form of a symmetric matrix, with its consequence `l75_bound`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

def dominance (M : Mat n) (j : Fin n) : ℝ := -M j j - ∑ k ∈ Finset.univ.erase j, M j k

lemma erase_eq_union (i : Fin n) :
    Finset.univ.erase i = Finset.univ.filter (i < ·) ∪ Finset.univ.filter (· < i) := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter]
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne']
  · simp [h]
  · simp [h, h.ne]

lemma sum_erase_split (h : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, h i j =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (h i j + h j i) := by
  have hd : ∀ i : Fin n, Disjoint (Finset.univ.filter (i < ·)) (Finset.univ.filter (· < i)) :=
    fun i => Finset.disjoint_filter.2 fun j _ h1 h2 => (lt_asymm h1 h2).elim
  have h1 : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, h i j =
      ∑ j ∈ Finset.univ.filter (i < ·), h i j + ∑ j ∈ Finset.univ.filter (· < i), h i j :=
    fun i => by rw [erase_eq_union, Finset.sum_union (hd i)]
  have hc : ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (· < i), h i j =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), h j i := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, hc, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib.symm

lemma sum_sum_split (f : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, f i j = ∑ i, f i i +
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (f i j + f j i) := by
  rw [← sum_erase_split]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]

/-- Algebraic identity; positivity only needed for its subsequent inequalities. -/
theorem l75 (M : Mat n) (hM : M.IsHermitian) (x : Vec n) :
    quad M x = -(∑ j, dominance M j * x j^2) -
      ∑ j, ∑ k ∈ Finset.univ.filter (j < ·), M j k * (x j-x k)^2 := by
  have hs : ∀ i j, M j i = M i j := fun i j => by
    have := congrFun (congrFun hM.eq i) j
    simpa [Matrix.conjTranspose_apply] using this
  unfold quad
  rw [sum_sum_split]
  have e1 : ∑ j, dominance M j * x j ^ 2 =
      -(∑ j, M j j * x j ^ 2) - ∑ j, ∑ k ∈ Finset.univ.erase j, M j k * x j ^ 2 := by
    simp only [dominance, sub_mul, neg_mul, Finset.sum_mul, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
  have e2 := sum_erase_split (fun j k => M j k * x j ^ 2)
  rw [e1, e2]
  have this : ∀ (j k : Fin n), M j k * x j ^ 2 + M k j * x k ^ 2 - M j k * (x j - x k) ^ 2 =
      x j * M j k * x k + x k * M k j * x j := fun j k => by rw [hs j k]; ring
  have hdiag : ∑ i, x i * M i i * x i = ∑ j, M j j * x j ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have hoff : ∑ j, ∑ k ∈ Finset.univ.filter (j < ·), (x j * M j k * x k + x k * M k j * x j) =
      ∑ j, ∑ k ∈ Finset.univ.filter (j < ·), (M j k * x j ^ 2 + M k j * x k ^ 2) -
      ∑ j, ∑ k ∈ Finset.univ.filter (j < ·), M j k * (x j - x k) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => (this j k).symm
  rw [hdiag, hoff]
  linarith

theorem l75_bound (M : Mat n) (hM : M.IsHermitian)
    (hOff : ∀ i j, i ≠ j → 0 ≤ M i j) {c : ℝ}
    (hc : ∀ j, c ≤ dominance M j) (x : Vec n) :
    quad M x ≤ -c * length2 x^2 := by
  rw [l75 M hM x]
  have h1 : c * length2 x ^ 2 ≤ ∑ j, dominance M j * x j ^ 2 := by
    rw [length2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i)), Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc j) (sq_nonneg _)
  have h2 : 0 ≤ ∑ j, ∑ k ∈ Finset.univ.filter (j < ·), M j k * (x j - x k) ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k hk =>
      mul_nonneg (hOff j k (Finset.mem_filter.1 hk).2.ne) (sq_nonneg _)
  linarith

end SecularSpectrum

end KAM.Planetary
