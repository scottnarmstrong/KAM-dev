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

lemma analyticAt_nu_action (D : Data n) {a : Vec n} (ha : a ∈ axes n) (i : Fin n) :
    AnalyticAt ℝ (fun b : Vec n => nu D (action D b) i) a := by
  have h0 : 0 < D.G * D.m0 * a i := mul_pos (mul_pos D.hG D.hm0) (ha.1 i)
  have hin : AnalyticAt ℝ (fun b : Vec n => D.G * D.m0 * b i) a :=
    analyticAt_const.mul (analyticAt_pi_iff.1 analyticAt_id i)
  have h1 : AnalyticAt ℝ (fun b : Vec n => action D b i) a :=
    analyticAt_const.mul (hin.contDiffAt.sqrt h0.ne').analyticAt
  have hne : action D a i ≠ 0 := (mul_pos (D.hm i) (Real.sqrt_pos.2 h0)).ne'
  have := analyticAt_const (v := (D.G * D.m0) ^ 2 * D.m i ^ 3) |>.div (h1.pow 3)
    (pow_ne_zero 3 hne)
  exact this

/-- The symmetric product `∏_π L_{c,π}` is analytic on all of `axes n`. -/
theorem fc_analytic_aux (D : Data n) (c : Vec n × Vec n) :
    AnalyticOnNhd ℝ (fc_def D c) (axes n) := by
  obtain ⟨P, hP⟩ := exists_relation_poly c.2
  intro a ha
  set x : Vec n → ℝ := fun b => ∑ i, c.1 i * nu D (action D b) i with hx
  have hxa : AnalyticAt ℝ x a :=
    Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (analyticAt_nu_action D ha i)
  have hfc : fc_def D c = fun b => MvPolynomial.eval₂ (Polynomial.evalRingHom (x b))
      (fun i : Fin n => (-1 : ℝ) ^ (i.val + 1) * (coeffs D b).charpoly.coeff (Fin.rev i).val) P := by
    funext b
    have h1 := hP (x b) (sigma D b)
    have h2 : (fun i : Fin n => MvPolynomial.eval (sigma D b)
        (MvPolynomial.esymm (Fin n) ℝ (i.val + 1))) =
        fun i : Fin n => (-1 : ℝ) ^ (i.val + 1) * (coeffs D b).charpoly.coeff (Fin.rev i).val :=
      funext fun i => esymm_sorted (coeffs D b) (coeffs_hermitian D b) i
    rw [h2] at h1
    rw [← h1]
    simp only [fc_def, relation, hx, Finset.prod_congr rfl]
  have hE : ∀ i : Fin n, AnalyticAt ℝ
      (fun b : Vec n => (-1 : ℝ) ^ (i.val + 1) * (coeffs D b).charpoly.coeff (Fin.rev i).val) a :=
    fun i => analyticAt_const.mul
      (analyticAt_charpoly_coeff (coeffs_analytic D a ha) (Fin.rev i).val)
  rw [hfc]
  simp_rw [MvPolynomial.eval₂_eq']
  refine Finset.analyticAt_fun_sum _ fun d _ => ?_
  refine AnalyticAt.mul ?_ ?_
  · have := hxa.aeval_polynomial (A := ℝ) (P.coeff d)
    simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using this
  · exact Finset.analyticAt_fun_prod _ fun i _ => (hE i).pow _

end Nondegeneracy
end KAM.Planetary
end
