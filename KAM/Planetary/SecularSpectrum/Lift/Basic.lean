/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Secular spectrum: the action-dependent lift, definitions and algebra

Blueprint P, Part 9 (`bpP:p9:lift`): the explicit lift `liftMap R` of an action-dependent
rotation `R`, its inverse `liftInv R`, and the algebraic parts of `lift` (`stepP:p9:lift-bij`):
mutual inverseness, preservation of the action block and of the Euclidean lengths of the slow
blocks, and equivariance under fast-angle translations.  The full derivative of `R` enters the
angle shift; none of the algebra below needs differentiability.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

/-- Explicit action-dependent lift; full derivative of R is indispensable. -/
def liftMap (R : Vec n → Mat n) (w : Phase (n+n)) : Phase (n+n) :=
  let I : Vec n := fast w.2
  let ξ : Vec n := slow w.1
  let η : Vec n := slow w.2
  let θ : Vec n := fun l => fast w.1 l -
    ∑ i, η i * ((fderiv ℝ R I (Pi.single l 1) * (R I).transpose).mulVec ξ) i
  assemble I θ ((R I).transpose.mulVec η) ((R I).transpose.mulVec ξ)
def liftInv (R : Vec n → Mat n) (w : Phase (n+n)) : Phase (n+n) :=
  let I : Vec n := fast w.2
  let ξ : Vec n := slow w.1
  let η : Vec n := slow w.2
  let θ : Vec n := fun l => fast w.1 l +
    ∑ i, η i * (((R I).transpose * fderiv ℝ R I (Pi.single l 1)).mulVec ξ) i
  assemble I θ ((R I).mulVec η) ((R I).mulVec ξ)
def liftDomain (W : Set (Vec n)) : Set (Phase (n+n)) := {w | fast w.2 ∈ W}

section Algebra

lemma fast_fst_assemble (I φ p q : Vec n) : fast (assemble I φ p q).1 = φ := by
  funext i; simp [assemble, fast]

lemma slow_fst_assemble (I φ p q : Vec n) : slow (assemble I φ p q).1 = q := by
  funext i; simp [assemble, slow]

lemma fast_snd_assemble (I φ p q : Vec n) : fast (assemble I φ p q).2 = I := by
  funext i; simp [assemble, fast]

lemma slow_snd_assemble (I φ p q : Vec n) : slow (assemble I φ p q).2 = p := by
  funext i; simp [assemble, slow]

lemma assemble_eta (w : Phase (n+n)) :
    assemble (fast w.2) (fast w.1) (slow w.2) (slow w.1) = w := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
      simp [assemble, fast, slow]

lemma length2_eq_dotProduct (x : Vec n) : length2 x = √(x ⬝ᵥ x) := by
  simp [length2, dotProduct, sq]

lemma length2_mulVec_of_orth {M : Mat n} (h : M.transpose * M = 1) (x : Vec n) :
    length2 (M.mulVec x) = length2 x := by
  rw [length2_eq_dotProduct, length2_eq_dotProduct]
  congr 1
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

lemma isSO_mul_transpose {R : Mat n} (h : isSO R) : R * R.transpose = 1 :=
  mul_eq_one_comm.1 h.1

lemma isSO_transpose_mul {R : Mat n} (h : isSO R) : R.transpose * R = 1 := h.1

lemma sum_transpose_mulVec_mul {R : Mat n} (h : R * R.transpose = 1) (a y : Vec n) :
    ∑ x, (R.transpose.mulVec a) x * (R.transpose.mulVec y) x = ∑ i, a i * y i := by
  change (R.transpose.mulVec a) ⬝ᵥ (R.transpose.mulVec y) = a ⬝ᵥ y
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

lemma liftInv_liftMap_of_isSO {R : Vec n → Mat n} {w : Phase (n+n)} (h : isSO (R (fast w.2))) :
    liftInv R (liftMap R w) = w := by
  have h1 := isSO_mul_transpose h
  have h2 := isSO_transpose_mul h
  conv_rhs => rw [← assemble_eta w]
  simp only [liftInv, liftMap, fast_fst_assemble, slow_fst_assemble, fast_snd_assemble,
    slow_snd_assemble, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  congr 1
  funext l
  rw [show ((R (fast w.2)).transpose * fderiv ℝ R (fast w.2) (Pi.single l 1) *
      (R (fast w.2)).transpose).mulVec
      (slow w.1) = (R (fast w.2)).transpose.mulVec
        ((fderiv ℝ R (fast w.2) (Pi.single l 1) * (R (fast w.2)).transpose).mulVec (slow w.1)) by
    rw [Matrix.mul_assoc, Matrix.mulVec_mulVec], sum_transpose_mulVec_mul h1]
  ring

lemma sum_mulVec_mul (R : Mat n) (a y : Vec n) :
    ∑ x, (R.mulVec a) x * y x = ∑ i, a i * (R.transpose.mulVec y) i := by
  change (R.mulVec a) ⬝ᵥ y = a ⬝ᵥ (R.transpose.mulVec y)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

lemma liftMap_liftInv_of_isSO {R : Vec n → Mat n} {w : Phase (n+n)} (h : isSO (R (fast w.2))) :
    liftMap R (liftInv R w) = w := by
  have h2 := isSO_transpose_mul h
  conv_rhs => rw [← assemble_eta w]
  simp only [liftInv, liftMap, fast_fst_assemble, slow_fst_assemble, fast_snd_assemble,
    slow_snd_assemble, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  congr 1
  funext l
  rw [sum_mulVec_mul, show ((fderiv ℝ R (fast w.2) (Pi.single l 1) *
      (R (fast w.2)).transpose) * R (fast w.2)).mulVec (slow w.1) =
      (fderiv ℝ R (fast w.2) (Pi.single l 1)).mulVec (slow w.1) by
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]]
  rw [Matrix.mulVec_mulVec]
  ring

lemma fast_snd_liftMap (R : Vec n → Mat n) (w : Phase (n+n)) :
    fast (liftMap R w).2 = fast w.2 := by
  simp only [liftMap, fast_snd_assemble]

lemma length2_slow_fst_liftMap {R : Vec n → Mat n} {w : Phase (n+n)} (h : isSO (R (fast w.2))) :
    length2 (slow (liftMap R w).1) = length2 (slow w.1) := by
  simp only [liftMap, slow_fst_assemble]
  exact length2_mulVec_of_orth (by simpa using isSO_mul_transpose h) _

lemma length2_slow_snd_liftMap {R : Vec n → Mat n} {w : Phase (n+n)} (h : isSO (R (fast w.2))) :
    length2 (slow (liftMap R w).2) = length2 (slow w.2) := by
  simp only [liftMap, slow_snd_assemble]
  exact length2_mulVec_of_orth (by simpa using isSO_mul_transpose h) _

lemma assemble_add_append (I φ p q c : Vec n) :
    assemble I φ p q + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ)) =
      assemble I (φ + c) p q := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;>
      simp [assemble]

lemma liftMap_add_append (R : Vec n → Mat n) (w : Phase (n+n)) (c : Vec n) :
    liftMap R (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))) =
      liftMap R w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ)) := by
  have hf : fast (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))).2 =
      fast w.2 := by funext i; simp [fast]
  have hs : slow (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))).2 =
      slow w.2 := by funext i; simp [slow]
  have hs1 : slow (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))).1 =
      slow w.1 := by funext i; simp [slow]
  have hf1 : fast (w + ((Fin.append c (0 : Vec n) : Fin (n+n) → ℝ), (0 : Fin (n+n) → ℝ))).1 =
      fast w.1 + c := by funext i; simp [fast]
  rw [liftMap, liftMap, assemble_add_append]
  simp only [hf, hs, hs1, hf1]
  congr 1
  funext l
  simp only [Pi.add_apply]
  ring

end Algebra

end SecularSpectrum

end KAM.Planetary

end
