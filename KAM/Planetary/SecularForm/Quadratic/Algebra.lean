/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularForm.AnalyticGeometry

/-!
# Quadratic part: the quadratic form as a sum over pairs

Blueprint P, Part 8, `stepP:p8:qf-assembly` (package S8-Q). The quadratic form
`ξᵀ Q ξ + ηᵀ Q η`, `Q = coeffs D a`, is the sum over pairs `i < j` of
`-(pairA/Λᵢ)|uᵢ|² - (pairA/Λⱼ)|uⱼ|² + 2 Qᵢⱼ uᵢ·uⱼ`, `uᵢ = (ξᵢ, ηᵢ)`.
-/

@[expose] public noncomputable section
open Set Filter Function
open scoped BigOperators
namespace KAM.Planetary
namespace SecularForm
variable {n : ℕ}

theorem sum_erase_split (f : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, f j =
      ∑ j ∈ Finset.univ.filter (i < ·), f j + ∑ j ∈ Finset.univ.filter (· < i), f j := by
  rw [← Finset.sum_union]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
      true_and]
    constructor
    · intro h; rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact h.ne'
      · exact h.ne
  · rw [Finset.disjoint_filter]
    intro j _ h1 h2
    exact absurd (h1.trans h2) (lt_irrefl _)

theorem sum_offdiag (f : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f i j =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (f i j + f j i) := by
  have h1 : ∑ i, ∑ j ∈ Finset.univ.filter (· < i), f i j =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), f j i :=
    Finset.sum_comm' (by intro i j; simp)
  simp only [sum_erase_split, Finset.sum_add_distrib, h1]

theorem pairA_comm (D : Data n) (a : Vec n) (i j : Fin n) : pairA D a i j = pairA D a j i := by
  simp only [pairA, min_comm i j, max_comm i j]

/-- `ξᵀ Q ξ + ηᵀ Q η` as a sum over the pairs `i < j`. -/
theorem quad_pair_sum (D : Data n) {a : Vec n} (ha : a ∈ axes n) (ξ η : Vec n) :
    quad (coeffs D a) ξ + quad (coeffs D a) η =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        ((-pairA D a i j / action D a i) * (ξ i ^ 2 + η i ^ 2) +
          (-pairA D a i j / action D a j) * (ξ j ^ 2 + η j ^ 2) +
          2 * coeffs D a i j * (ξ i * ξ j + η i * η j)) := by
  have hpos : ∀ i, 0 < action D a i := action_pos D ha
  have hrt : ∀ i, √(action D a i) * √(action D a i) = action D a i := fun i =>
    Real.mul_self_sqrt (hpos i).le
  have hsym : ∀ i j, coeffs D a j i = coeffs D a i j := fun i j => by
    have := (coeffs_hermitian D a).apply i j
    simpa using this
  have hdiag : ∀ i, coeffs D a i i =
      (-∑ k ∈ Finset.univ.erase i, pairA D a i k) / action D a i := fun i => by
    unfold coeffs qhat
    simp [hrt]
  have hq : quad (coeffs D a) ξ + quad (coeffs D a) η =
      ∑ i, ∑ j, coeffs D a i j * (ξ i * ξ j + η i * η j) := by
    unfold quad
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hq]
  have hsplit : ∀ i, ∑ j, coeffs D a i j * (ξ i * ξ j + η i * η j) =
      coeffs D a i i * (ξ i ^ 2 + η i ^ 2) +
        ∑ j ∈ Finset.univ.erase i, coeffs D a i j * (ξ i * ξ j + η i * η j) := fun i => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  have hd2 : ∑ i, coeffs D a i i * (ξ i ^ 2 + η i ^ 2) =
      ∑ i, ∑ k ∈ Finset.univ.erase i, (-pairA D a i k / action D a i) * (ξ i ^ 2 + η i ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdiag, ← Finset.sum_neg_distrib, Finset.sum_div, Finset.sum_mul]
  calc ∑ i, ∑ j, coeffs D a i j * (ξ i * ξ j + η i * η j)
      = ∑ i, (coeffs D a i i * (ξ i ^ 2 + η i ^ 2) +
        ∑ j ∈ Finset.univ.erase i, coeffs D a i j * (ξ i * ξ j + η i * η j)) :=
        Finset.sum_congr rfl fun i _ => hsplit i
    _ = ∑ i, coeffs D a i i * (ξ i ^ 2 + η i ^ 2) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, coeffs D a i j * (ξ i * ξ j + η i * η j) :=
        Finset.sum_add_distrib
    _ = ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), ((-pairA D a i j / action D a i) *
          (ξ i ^ 2 + η i ^ 2) + (-pairA D a j i / action D a j) * (ξ j ^ 2 + η j ^ 2)) +
        ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (coeffs D a i j * (ξ i * ξ j + η i * η j) +
          coeffs D a j i * (ξ j * ξ i + η j * η i)) := by
        rw [hd2, sum_offdiag (fun i k => (-pairA D a i k / action D a i) * (ξ i ^ 2 + η i ^ 2)),
          sum_offdiag (fun i j => coeffs D a i j * (ξ i * ξ j + η i * η j))]
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsym i j, pairA_comm D a j i]
        ring

end SecularForm
end KAM.Planetary
end
