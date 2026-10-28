/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.LocalAnalytic.Sorted
public import KAM.Planetary.SecularSpectrum.Norms
public import KAM.Planetary.SecularForm.Basic

/-!
# Good axes: sorted spectra and the bordered matrix `0 ⊕ Q`

Helper results for `bpP:p10:sorted-analytic` and `bpP:p10:good-point`: a monotone list of roots is
determined by its characteristic product, the sorted spectrum of a matrix `0 ⊕ Q` with `Q ≤ 0`
spectrum is the sorted spectrum of `Q` followed by `0` (`stepP:p10:gp-loc`), and
`nr4` follows from the non-vanishing of its sums over `k4`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-- Two monotone families with the same characteristic product agree. -/
lemma eq_of_monotone_prod {s t : Fin m → ℝ} (hs : Monotone s) (ht : Monotone t)
    (h : ∏ i, (X - C (s i) : ℝ[X]) = ∏ i, (X - C (t i))) : s = t := by
  have hprod : ∀ f : Fin m → ℝ, ∏ i, (X - C (f i) : ℝ[X]) =
      ((Finset.univ.val.map f).map fun a => X - C a).prod := fun f => by
    simp [Finset.prod, Function.comp_def]
  rw [hprod, hprod] at h
  have hr := congrArg Polynomial.roots h
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_eq_coe] at hr
  exact List.ofFn_injective (hr.eq_of_sortedLE hs.sortedLE_ofFn ht.sortedLE_ofFn)

/-- The matrix `0 ⊕ Q`: first row and column vanish, the rest is `Q`. -/
def blockZero (Q : Mat n) : Mat (n+1) :=
  fun i j => Fin.cases 0 (fun i' => Fin.cases 0 (fun j' => Q i' j') j) i

@[simp] lemma blockZero_zero_left (Q : Mat n) (j : Fin (n+1)) : blockZero Q 0 j = 0 := rfl

@[simp] lemma blockZero_zero_right (Q : Mat n) (i : Fin (n+1)) : blockZero Q i 0 = 0 := by
  refine Fin.cases rfl (fun _ => rfl) i

@[simp] lemma blockZero_succ_succ (Q : Mat n) (i j : Fin n) :
    blockZero Q i.succ j.succ = Q i j := rfl

lemma blockZero_isHermitian {Q : Mat n} (hQ : Q.IsHermitian) : (blockZero Q).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hs : Q.transpose = Q := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.eq
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.transpose_apply]
  simpa [Matrix.transpose_apply] using congrFun (congrFun hs i') j'

lemma charpoly_blockZero (Q : Mat n) : (blockZero Q).charpoly = X * Q.charpoly := by
  let e : Fin (n+1) ≃ Fin n ⊕ PUnit.{1} := (finSuccEquiv n).trans (Equiv.optionEquivSumPUnit _)
  have h : blockZero Q = Matrix.reindex e.symm e.symm
      (Matrix.fromBlocks Q 0 0 (0 : Matrix PUnit.{1} PUnit.{1} ℝ)) := by
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [e, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [h, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_zero]
  simp [mul_comm]

lemma snoc_zero_monotone {s : Fin n → ℝ} (hs : Monotone s) (h0 : ∀ j, s j ≤ 0) :
    Monotone (Fin.snoc s (0 : ℝ) : Fin (n+1) → ℝ) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    have : j = Fin.last n := le_antisymm (Fin.le_last j) hij
    subst this; exact le_rfl
  | cast i' =>
    induction j using Fin.lastCases with
    | last => simpa using h0 i'
    | cast j' =>
      have : i' ≤ j' := by simpa using hij
      simpa using hs this

/-- `stepP:p10:gp-loc`: the sorted spectrum of `0 ⊕ Q` when `Q` has non-positive spectrum. -/
lemma sorted_blockZero {Q : Mat n} (hQ : Q.IsHermitian) (h0 : ∀ j, sorted Q hQ j ≤ 0) :
    sorted (blockZero Q) (blockZero_isHermitian hQ) = Fin.snoc (sorted Q hQ) (0 : ℝ) := by
  refine eq_of_monotone_prod (sorted_monotone _) (snoc_zero_monotone (sorted_monotone hQ) h0) ?_
  rw [← charpoly_eq_prod_sorted, charpoly_blockZero, charpoly_eq_prod_sorted hQ,
    Fin.prod_univ_castSucc]
  simp [mul_comm]

end Nondegeneracy
end KAM.Planetary
end
