/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Nondegeneracy.SymmetricRelation.Defs

/-!
# Symmetric relation product: analyticity

Blueprint P, Part 10 (`bpP:p10:Fc-analytic`, `stepP:p10:Fc-poly`): the product
`∏_π (X + ∑_j c''_j σ_{π j}) ∈ ℝ[X][σ]` is symmetric in `σ`, hence (fundamental theorem of
symmetric polynomials over `ℝ[X]`) a polynomial in the elementary symmetric functions of `σ`,
which are, up to sign, the characteristic coefficients of the secular matrix.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-- The universal symmetric product, with coefficients in `ℝ[X]`. -/
def relationPoly (n : ℕ) (c : Vec n) : MvPolynomial (Fin n) ℝ[X] :=
  ∏ p : Equiv.Perm (Fin n), (MvPolynomial.C (Polynomial.X : ℝ[X]) +
    ∑ j, MvPolynomial.C (Polynomial.C (c j)) * MvPolynomial.X (p j))

lemma eval₂_relationPoly (c : Vec n) (x : ℝ) (s : Vec n) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom x) s (relationPoly n c) =
      ∏ p : Equiv.Perm (Fin n), (x + ∑ j, c j * s (p j)) := by
  simp [relationPoly, MvPolynomial.eval₂_prod, MvPolynomial.eval₂_sum]

lemma relationPoly_isSymmetric (c : Vec n) : (relationPoly n c).IsSymmetric := by
  intro e
  simp only [relationPoly, map_prod, map_add, map_sum, map_mul, MvPolynomial.rename_C,
    MvPolynomial.rename_X]
  exact Fintype.prod_equiv (Equiv.mulLeft e) _ _ fun p => by simp

/-- Elementary symmetric functions of the sorted spectrum are characteristic coefficients. -/
lemma esymm_sorted (M : Mat n) (hM : M.IsHermitian) (i : Fin n) :
    MvPolynomial.eval (sorted M hM) (MvPolynomial.esymm (Fin n) ℝ (i.val + 1)) =
      (-1 : ℝ) ^ (i.val + 1) * M.charpoly.coeff (Fin.rev i).val := by
  set s := sorted M hM with hs
  have hch : M.charpoly =
      ((Finset.univ.val.map s).map fun t => Polynomial.X - Polynomial.C t).prod := by
    rw [charpoly_eq_prod_sorted hM, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [show MvPolynomial.eval s (MvPolynomial.esymm (Fin n) ℝ (i.val + 1)) =
    MvPolynomial.aeval s (MvPolynomial.esymm (Fin n) ℝ (i.val + 1)) from rfl,
    MvPolynomial.aeval_esymm_eq_multiset_esymm]
  have hk : (Fin.rev i).val ≤ Multiset.card (Finset.univ.val.map s) := by
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin,
      Fin.val_rev]
    have := i.2; omega
  rw [hch, Multiset.prod_X_sub_C_coeff _ hk]
  have hc : Multiset.card (Finset.univ.val.map s) - (Fin.rev i).val = i.val + 1 := by
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin,
      Fin.val_rev]
    have := i.2; omega
  rw [hc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- A polynomial in `X` and the elementary symmetric functions computes the symmetric product. -/
lemma exists_relation_poly (c : Vec n) : ∃ P : MvPolynomial (Fin n) ℝ[X],
    ∀ (x : ℝ) (s : Vec n), ∏ p : Equiv.Perm (Fin n), (x + ∑ j, c j * s (p j)) =
      MvPolynomial.eval₂ (Polynomial.evalRingHom x)
        (fun i : Fin n => MvPolynomial.eval s (MvPolynomial.esymm (Fin n) ℝ (i.val + 1))) P := by
  obtain ⟨P, hP⟩ := (MvPolynomial.esymmAlgEquiv (Fin n) ℝ[X] (Fintype.card_fin n)).surjective
    ⟨relationPoly n c, relationPoly_isSymmetric c⟩
  have hP' : MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.esymm (Fin n) ℝ[X] (i.val + 1)) P = relationPoly n c := by
    have := congrArg Subtype.val hP
    simpa [MvPolynomial.esymmAlgEquiv_apply, MvPolynomial.esymmAlgHom_apply] using this
  refine ⟨P, fun x s => ?_⟩
  rw [← eval₂_relationPoly, ← hP']
  set ψ := MvPolynomial.eval₂Hom (Polynomial.evalRingHom x) s with hψ
  have key : ψ (MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.esymm (Fin n) ℝ[X] (i.val + 1)) P) =
      MvPolynomial.eval₂ (Polynomial.evalRingHom x)
        (fun i : Fin n => MvPolynomial.eval s (MvPolynomial.esymm (Fin n) ℝ (i.val + 1))) P := by
    have : ψ.comp (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.esymm (Fin n) ℝ[X] (i.val + 1))).toRingHom =
        MvPolynomial.eval₂Hom (Polynomial.evalRingHom x)
          (fun i : Fin n => MvPolynomial.eval s (MvPolynomial.esymm (Fin n) ℝ (i.val + 1))) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [hψ]
      · simp [hψ, MvPolynomial.esymm, MvPolynomial.eval₂_sum]
    exact congrArg (fun f => f P) this
  exact key

end Nondegeneracy
end KAM.Planetary
end
