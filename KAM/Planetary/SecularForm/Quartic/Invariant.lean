/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.InvariantPolynomial
public import KAM.Planetary.SecularForm.Quartic.Defs

/-!
# Secular form: the quartic jet of an `O(2)`-invariant function of two planar vectors

Blueprint P, Part 8, `stepP:p8:q4-str`: the fourth derivative of a function of two planar vectors
that is invariant under simultaneous orthogonal transformations is a combination of the six
monomials `quarticMonomials`, by the polynomial representation of the fourth derivative and the
invariant-polynomial reduction `quartic_invariant`.
-/

@[expose] public noncomputable section
open Set Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

/-- Planar pairs as a function on `Fin 2 → Fin 2 → ℝ`. -/
abbrev PairVec := Fin 2 → Fin 2 → ℝ

/-- The fourth derivative of any function is a homogeneous quartic polynomial in the
coordinates. -/
theorem exists_poly_of_multilinear
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => PairVec) ℝ) :
    ∃ P : MvPolynomial (Fin 2 × Fin 2) ℝ, P.IsHomogeneous 4 ∧
      ∀ u : PairVec, M (fun _ => u) = MvPolynomial.eval (fun ic => u ic.1 ic.2) P := by
  classical
  let e : Fin 2 × Fin 2 → PairVec := fun ic => Pi.single ic.1 (Pi.single ic.2 1)
  refine ⟨∑ r : Fin 4 → Fin 2 × Fin 2,
    MvPolynomial.C (M fun k => e (r k)) * ∏ k, MvPolynomial.X (r k), ?_, fun u => ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun r _ => ?_
    have h1 : (∏ k : Fin 4, (MvPolynomial.X (r k) : MvPolynomial (Fin 2 × Fin 2) ℝ)).IsHomogeneous
        (∑ _k : Fin 4, 1) :=
      MvPolynomial.IsHomogeneous.prod _ _ _ fun k _ => MvPolynomial.isHomogeneous_X _ _
    have := (MvPolynomial.isHomogeneous_C (Fin 2 × Fin 2) (M fun k => e (r k))).mul h1
    simpa using this
  · have hu : u = ∑ ic : Fin 2 × Fin 2, u ic.1 ic.2 • e ic := by
      ext p q
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, Fintype.sum_prod_type]
      fin_cases p <;> fin_cases q <;> simp
    have hu' : (fun _ : Fin 4 => u) = fun _ => ∑ ic : Fin 2 × Fin 2, u ic.1 ic.2 • e ic := by
      rw [← hu]
    rw [hu', ContinuousMultilinearMap.map_sum
      (g := fun (_ : Fin 4) (ic : Fin 2 × Fin 2) => u ic.1 ic.2 • e ic)]
    simp only [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, map_sum, map_mul,
      MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring

/-- If the diagonal of a continuous multilinear map is invariant under simultaneous orthogonal
transformations, it is a combination of the six quartic monomials. -/
theorem quartic_form_of_invariant
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => PairVec) ℝ)
    (hinv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 → ∀ u : PairVec,
      M (fun _ => fun p => R.mulVec (u p)) = M (fun _ => u)) :
    ∃ c : Fin 6 → ℝ, ∀ u : PairVec,
      M (fun _ => u) = ∑ k, c k * quarticMonomials (u 0) (u 1) k := by
  obtain ⟨P, hP, hPM⟩ := exists_poly_of_multilinear M
  obtain ⟨c, hc⟩ := Weyl.quartic_invariant P hP fun R hR u => by
    have h1 := hPM (fun p => R.mulVec (u p))
    have h2 := hPM u
    rw [← h1, ← h2]
    exact hinv R hR u
  exact ⟨c, fun u => by rw [hPM u, hc u]; rfl⟩

end SecularForm
end KAM.Planetary
end
