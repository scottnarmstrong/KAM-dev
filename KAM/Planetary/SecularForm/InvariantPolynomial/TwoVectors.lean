/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.InvariantPolynomial.Homogeneous

/-!
# Quadratic and quartic invariants of two planar vectors

`bpP:p8:quadratic-form` (`qf-pair`) and `bpP:p8:quartic` (`q4-str`): an `O(2)`-invariant
homogeneous polynomial of degree two (resp. four) in a pair of planar vectors `(u, v)` is a linear
combination of `|u|², |v|², u·v` (resp. of the six monomials
`|u|⁴, |v|⁴, |u|²|v|², (u·v)², |u|²(u·v), |v|²(u·v)`).
-/

@[expose] public noncomputable section
open MvPolynomial
namespace KAM.Planetary
namespace SecularForm
namespace Weyl

/-- The three quadratic invariants of a pair of planar vectors. -/
def quadraticTerms (u v : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![planeSq u, planeSq v, planeDot u v]

/-- The six quartic invariants of a pair of planar vectors. -/
def quarticTerms (u v : Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![planeSq u ^ 2, planeSq v ^ 2, planeSq u * planeSq v, planeDot u v ^ 2,
    planeSq u * planeDot u v, planeSq v * planeDot u v]

theorem planeDot_self (v : Fin 2 → ℝ) : planeDot v v = planeSq v := by
  simp [planeDot, planeSq, Fin.sum_univ_two, sq]

theorem planeDot_comm (v w : Fin 2 → ℝ) : planeDot v w = planeDot w v := by
  simp [planeDot, Fin.sum_univ_two]; ring

/-- A homogeneous polynomial in the four dot products of two vectors, as a sum over monomials. -/
theorem eval_dots_eq (Q : MvPolynomial (Fin 2 × Fin 2) ℝ) (u : Fin 2 → Fin 2 → ℝ) :
    MvPolynomial.eval (fun ij => planeDot (u ij.1) (u ij.2)) Q =
      ∑ s ∈ Q.support, Q.coeff s *
        (planeSq (u 0) ^ s (0, 0) * planeSq (u 1) ^ s (1, 1) *
          planeDot (u 0) (u 1) ^ (s (0, 1) + s (1, 0))) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two, planeDot_self, pow_add]
  rw [planeDot_comm (u 1) (u 0)]
  ring

theorem sum_degree_eq {Q : MvPolynomial (Fin 2 × Fin 2) ℝ} {D : ℕ} (hQ : Q.IsHomogeneous D)
    {s : Fin 2 × Fin 2 →₀ ℕ} (hs : s ∈ Q.support) :
    s (0, 0) + s (1, 1) + (s (0, 1) + s (1, 0)) = D := by
  have h := hQ.degree_eq_sum_deg_support hs
  rw [Finset.sum_subset (Finset.subset_univ s.support) (fun i _ hi => by simpa using hi),
    Fintype.sum_prod_type] at h
  simp only [Fin.sum_univ_two] at h
  omega

/-- The span of the quadratic invariants. -/
def quadraticSpan : Submodule ℝ ((Fin 2 → Fin 2 → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range fun i : Fin 3 => fun u : Fin 2 → Fin 2 → ℝ =>
    quadraticTerms (u 0) (u 1) i)

/-- The span of the quartic invariants. -/
def quarticSpan : Submodule ℝ ((Fin 2 → Fin 2 → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range fun i : Fin 6 => fun u : Fin 2 → Fin 2 → ℝ =>
    quarticTerms (u 0) (u 1) i)

theorem quadratic_monomial_mem (a d e : ℕ) (h : a + d + e = 1) :
    (fun u : Fin 2 → Fin 2 → ℝ =>
      planeSq (u 0) ^ a * planeSq (u 1) ^ d * planeDot (u 0) (u 1) ^ e) ∈ quadraticSpan := by
  have : (a = 1 ∧ d = 0 ∧ e = 0) ∨ (a = 0 ∧ d = 1 ∧ e = 0) ∨ (a = 0 ∧ d = 0 ∧ e = 1) := by omega
  rcases this with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Submodule.subset_span ⟨0, by funext u; simp [quadraticTerms]⟩
  · exact Submodule.subset_span ⟨1, by funext u; simp [quadraticTerms]⟩
  · exact Submodule.subset_span ⟨2, by funext u; simp [quadraticTerms]⟩

theorem quartic_monomial_mem (a d e : ℕ) (h : a + d + e = 2) :
    (fun u : Fin 2 → Fin 2 → ℝ =>
      planeSq (u 0) ^ a * planeSq (u 1) ^ d * planeDot (u 0) (u 1) ^ e) ∈ quarticSpan := by
  have : (a = 2 ∧ d = 0 ∧ e = 0) ∨ (a = 0 ∧ d = 2 ∧ e = 0) ∨ (a = 1 ∧ d = 1 ∧ e = 0) ∨
      (a = 0 ∧ d = 0 ∧ e = 2) ∨ (a = 1 ∧ d = 0 ∧ e = 1) ∨ (a = 0 ∧ d = 1 ∧ e = 1) := by omega
  rcases this with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Submodule.subset_span ⟨0, by funext u; simp [quarticTerms]⟩
  · exact Submodule.subset_span ⟨1, by funext u; simp [quarticTerms]⟩
  · exact Submodule.subset_span ⟨2, by funext u; simp [quarticTerms]⟩
  · exact Submodule.subset_span ⟨3, by funext u; simp [quarticTerms]⟩
  · exact Submodule.subset_span ⟨4, by funext u; simp [quarticTerms]⟩
  · exact Submodule.subset_span ⟨5, by funext u; simp [quarticTerms]⟩

/-- An `O(2)`-invariant quadratic form in a pair of planar vectors is a combination of
`|u|²`, `|v|²`, `u·v`. -/
theorem quadratic_invariant (P : MvPolynomial (Fin 2 × Fin 2) ℝ) (hP : P.IsHomogeneous 2)
    (hInv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 →
      ∀ u : Fin 2 → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => (R.mulVec (u ic.1)) ic.2) P =
        MvPolynomial.eval (fun ic => u ic.1 ic.2) P) :
    ∃ c : Fin 3 → ℝ, ∀ u : Fin 2 → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => u ic.1 ic.2) P = ∑ k, c k * quadraticTerms (u 0) (u 1) k := by
  obtain ⟨Q, hQ, hPQ⟩ := exists_homogeneous_dot_poly P 1 hInv
    (fun r u => by simpa using eval_smul_of_isHomogeneous hP r (fun ic => u ic.1 ic.2))
  have hmem : (fun u : Fin 2 → Fin 2 → ℝ =>
      MvPolynomial.eval (fun ij => planeDot (u ij.1) (u ij.2)) Q) ∈ quadraticSpan := by
    have : (fun u : Fin 2 → Fin 2 → ℝ =>
        MvPolynomial.eval (fun ij => planeDot (u ij.1) (u ij.2)) Q) =
        ∑ s ∈ Q.support, Q.coeff s • (fun u : Fin 2 → Fin 2 → ℝ =>
          planeSq (u 0) ^ s (0, 0) * planeSq (u 1) ^ s (1, 1) *
            planeDot (u 0) (u 1) ^ (s (0, 1) + s (1, 0))) := by
      funext u; rw [eval_dots_eq]; simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _
      (quadratic_monomial_mem _ _ _ (sum_degree_eq hQ hs))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  refine ⟨c, fun u => ?_⟩
  rw [hPQ u]
  have := congrFun hc u
  simpa [Finset.sum_apply] using this.symm

/-- An `O(2)`-invariant quartic form in a pair of planar vectors is a combination of the six
monomials `|u|⁴, |v|⁴, |u|²|v|², (u·v)², |u|²(u·v), |v|²(u·v)`. -/
theorem quartic_invariant (P : MvPolynomial (Fin 2 × Fin 2) ℝ) (hP : P.IsHomogeneous 4)
    (hInv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 →
      ∀ u : Fin 2 → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => (R.mulVec (u ic.1)) ic.2) P =
        MvPolynomial.eval (fun ic => u ic.1 ic.2) P) :
    ∃ c : Fin 6 → ℝ, ∀ u : Fin 2 → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => u ic.1 ic.2) P = ∑ k, c k * quarticTerms (u 0) (u 1) k := by
  obtain ⟨Q, hQ, hPQ⟩ := exists_homogeneous_dot_poly P 2 hInv
    (fun r u => by simpa using eval_smul_of_isHomogeneous hP r (fun ic => u ic.1 ic.2))
  have hmem : (fun u : Fin 2 → Fin 2 → ℝ =>
      MvPolynomial.eval (fun ij => planeDot (u ij.1) (u ij.2)) Q) ∈ quarticSpan := by
    have : (fun u : Fin 2 → Fin 2 → ℝ =>
        MvPolynomial.eval (fun ij => planeDot (u ij.1) (u ij.2)) Q) =
        ∑ s ∈ Q.support, Q.coeff s • (fun u : Fin 2 → Fin 2 → ℝ =>
          planeSq (u 0) ^ s (0, 0) * planeSq (u 1) ^ s (1, 1) *
            planeDot (u 0) (u 1) ^ (s (0, 1) + s (1, 0))) := by
      funext u; rw [eval_dots_eq]; simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _
      (quartic_monomial_mem _ _ _ (sum_degree_eq hQ hs))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  refine ⟨c, fun u => ?_⟩
  rw [hPQ u]
  have := congrFun hc u
  simpa [Finset.sum_apply] using this.symm

end Weyl
end SecularForm
end KAM.Planetary
