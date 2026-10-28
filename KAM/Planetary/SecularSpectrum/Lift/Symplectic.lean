/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Lift.Core
public import KAM.Planetary.SecularSpectrum.Lift.Deriv

/-!
# Secular spectrum: the lift is symplectic

Blueprint P, Part 9 (`stepP:p9:lift-form`, `stepP:p9:lift-mc`): `IsSymplecticOn 1 (liftMap R)` on
`liftDomain W`.  The derivative `dLift R z u` is paired against itself with the frozen
`symplecticForm`; the terms with second derivatives of `R` cancel by the symmetry of `hess`, and
the remaining first-derivative terms cancel by `core_identity` (the Maurer–Cartan relation).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Symplectic

lemma symplecticForm_split (x y : Phase (n+n)) :
    symplecticForm x y = ∑ j, (fast x.2 j * fast y.1 j - fast x.1 j * fast y.2 j) +
      ∑ j, (slow x.2 j * slow y.1 j - slow x.1 j * slow y.2 j) := by
  unfold symplecticForm
  rw [Fin.sum_univ_add]
  rfl

lemma sum_mul_dot (F : Fin n → Mat n) (x a c : Vec n) (M : Mat n) :
    ∑ j, x j * (a ⬝ᵥ ((F j * M).mulVec c)) = a ⬝ᵥ (((∑ j, x j • F j) * M).mulVec c) := by
  simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.sum_mulVec, Matrix.smul_mulVec,
    dotProduct_sum, dotProduct_smul, smul_eq_mul]

lemma sum_dTheta (R : Vec n → Mat n) (z : Phase (n+n)) (u v : Phase (n+n)) :
    ∑ j, fast u.2 j * dTheta R z v j = ∑ j, fast u.2 j * fast v.1 j -
      (slow v.2 ⬝ᵥ ((fderiv ℝ R (fast z.2) (fast u.2) * (R (fast z.2)).transpose).mulVec
          (slow z.1)) +
        slow z.2 ⬝ᵥ (((hess R (fast z.2) (fast v.2) (fast u.2) * (R (fast z.2)).transpose +
            fderiv ℝ R (fast z.2) (fast u.2) * (fderiv ℝ R (fast z.2) (fast v.2)).transpose).mulVec
            (slow z.1)) +
          (fderiv ℝ R (fast z.2) (fast u.2) * (R (fast z.2)).transpose).mulVec (slow v.1))) := by
  have hD := fderiv_eq_sum R (fast z.2) (fast u.2)
  have hH := hess_eq_sum R (fast z.2) (fast v.2) (fast u.2)
  simp only [dTheta, mul_sub, Finset.sum_sub_distrib, Matrix.add_mulVec, dotProduct_add, mul_add,
    Finset.sum_add_distrib]
  rw [sum_mul_dot (fun l => fderiv ℝ R (fast z.2) (Pi.single l 1)),
    sum_mul_dot (fun l => hess R (fast z.2) (fast v.2) (Pi.single l 1)),
    sum_mul_dot (fun l => fderiv ℝ R (fast z.2) (Pi.single l 1)),
    sum_mul_dot (fun l => fderiv ℝ R (fast z.2) (Pi.single l 1)), ← hD, ← hH]

theorem symplecticForm_dLift {W : Set (Vec n)} (hW : IsOpen W) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I)) {z : Phase (n+n)}
    (hz : z ∈ liftDomain W) (u v : Phase (n+n)) :
    symplecticForm (dLift R z u) (dLift R z v) = symplecticForm u v := by
  have hI : fast z.2 ∈ W := hz
  rw [symplecticForm_split, symplecticForm_split u v]
  simp only [dLift, fast_fst_assemble, slow_fst_assemble, fast_snd_assemble, slow_snd_assemble]
  have e1 : ∀ a b c d : Vec n, ∑ j, (a j * b j - c j * d j) = a ⬝ᵥ b - c ⬝ᵥ d := by
    intro a b c d
    simp [dotProduct, Finset.sum_sub_distrib]
  have e2 : ∀ a b c d : Vec n, ∑ j, (a j * b j - c j * d j) =
      ∑ j, a j * b j - ∑ j, d j * c j := by
    intro a b c d
    simp only [Finset.sum_sub_distrib, mul_comm (c _)]
  rw [e2 (fast u.2) (dTheta R z v) (dTheta R z u) (fast v.2), sum_dTheta R z u v,
    sum_dTheta R z v u, e1]
  have hRR := isSO_mul_transpose (hR _ hI)
  have hu : fderiv ℝ R (fast z.2) (fast u.2) * (R (fast z.2)).transpose +
      R (fast z.2) * (fderiv ℝ R (fast z.2) (fast u.2)).transpose = 0 :=
    deriv_orth hW hAn hR hI _
  have hv : fderiv ℝ R (fast z.2) (fast v.2) * (R (fast z.2)).transpose +
      R (fast z.2) * (fderiv ℝ R (fast z.2) (fast v.2)).transpose = 0 :=
    deriv_orth hW hAn hR hI _
  have hc := core_identity (R (fast z.2)) (fderiv ℝ R (fast z.2) (fast u.2))
    (fderiv ℝ R (fast z.2) (fast v.2)) (hess R (fast z.2) (fast v.2) (fast u.2)) hRR
    (eq_neg_of_add_eq_zero_right hu)
    (eq_neg_of_add_eq_zero_right hv)
    (slow z.2) (slow z.1) (slow u.2) (slow v.2) (slow u.1) (slow v.1)
  rw [hess_symm hAn hI (fast u.2) (fast v.2),
    e1 (slow u.2) (slow v.1) (slow u.1) (slow v.2), Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun j _ => mul_comm (fast v.2 j) (fast u.1 j))]
  simp only [dP, dQ]
  linarith

end Symplectic

end SecularSpectrum

end KAM.Planetary

end
