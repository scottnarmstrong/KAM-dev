/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Basic

/-!
# Planar quartic torsion: characters are polynomials of degree at most four

Blueprint P, Part 11b (`bpP:p11b:char`): the explicit polynomial `charFcPoly` representing the
one-plane Fourier coefficient, with the total-degree bound read off the coefficients of the
expansion polynomial `charQ`, and the resulting polynomial representation of the full character.
-/

@[expose] public noncomputable section

open Set Real Polynomial
open scoped Polynomial

namespace KAM.Planetary.PlanarCharacters

/-- Every coefficient of `P` has total degree at most `d`. -/
def CoeffDeg (d : ℕ) (P : (MvPolynomial (Fin 2) ℂ)[X]) : Prop :=
  ∀ n, (P.coeff n).totalDegree ≤ d

lemma CoeffDeg.mono {P : (MvPolynomial (Fin 2) ℂ)[X]} {a b : ℕ} (h : CoeffDeg a P) (hab : a ≤ b) :
    CoeffDeg b P := fun n => (h n).trans hab

lemma CoeffDeg.mul {P Q : (MvPolynomial (Fin 2) ℂ)[X]} {a b : ℕ} (hP : CoeffDeg a P)
    (hQ : CoeffDeg b Q) : CoeffDeg (a + b) (P * Q) := by
  intro n
  rw [Polynomial.coeff_mul]
  refine MvPolynomial.totalDegree_finsetSum_le fun ij _ => ?_
  exact (MvPolynomial.totalDegree_mul _ _).trans (add_le_add (hP _) (hQ _))

lemma CoeffDeg.one : CoeffDeg 0 (1 : (MvPolynomial (Fin 2) ℂ)[X]) := by
  intro n
  rw [Polynomial.coeff_one]
  split_ifs <;> simp

lemma CoeffDeg.pow {P : (MvPolynomial (Fin 2) ℂ)[X]} (h : CoeffDeg 1 P) (m : ℕ) :
    CoeffDeg m (P ^ m) := by
  induction m with
  | zero => simpa using CoeffDeg.one
  | succ m ih => rw [pow_succ]; exact (ih.mul h).mono (le_refl _)

lemma charW_deg : charW.totalDegree ≤ 1 := by
  unfold charW
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.totalDegree_X _).le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_C,
      MvPolynomial.totalDegree_X])

lemma charWb_deg : charWb.totalDegree ≤ 1 := by
  unfold charWb
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.totalDegree_X _).le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_C,
      MvPolynomial.totalDegree_X])

lemma coeff_deg_aux (c : ℂ) (w : MvPolynomial (Fin 2) ℂ) (hw : w.totalDegree ≤ 1) :
    (MvPolynomial.C c * w).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_C, hw])

lemma charUP_deg : CoeffDeg 1 charUP := by
  intro n
  have h1 := coeff_deg_aux (1 / 2) charWb charWb_deg
  have h2 := coeff_deg_aux (1 / 2) charW charW_deg
  unfold charUP
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_) <;> split_ifs <;>
      first | exact h1 | exact h2 | simp

lemma charVP_deg : CoeffDeg 1 charVP := by
  intro n
  have h1 := coeff_deg_aux (Complex.I / 2) charWb charWb_deg
  have h2 := coeff_deg_aux (Complex.I / 2) charW charW_deg
  unfold charVP
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_) <;> split_ifs <;>
      first | exact h1 | exact h2 | simp

lemma charQ_deg (p q : ℕ) : CoeffDeg (p + q) (charQ p q) :=
  ((charUP_deg.pow p).mul (charVP_deg.pow q))

/-- The polynomial in `(x, y)` representing the one-plane Fourier coefficient. -/
def charFcPoly (p q : ℕ) (k : ℤ) : MvPolynomial (Fin 2) ℂ :=
  ∑ n ∈ Finset.range (2 * (p + q) + 1),
    if (n : ℤ) = k + ((p + q : ℕ) : ℤ) then (charQ p q).coeff n else 0

lemma charFcPoly_deg (p q : ℕ) (k : ℤ) : (charFcPoly p q k).totalDegree ≤ p + q := by
  refine MvPolynomial.totalDegree_finsetSum_le fun n _ => ?_
  split_ifs
  · exact charQ_deg p q n
  · simp

lemma charFcPoly_eval (p q : ℕ) (k : ℤ) (x y : ℝ) :
    MvPolynomial.eval ![(x : ℂ), (y : ℂ)] (charFcPoly p q k) = charFc p q x y k := by
  rw [charFc_eq, charFcPoly, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs
  · rw [charQc, Polynomial.coeff_map]
  · simp

end KAM.Planetary.PlanarCharacters

end
