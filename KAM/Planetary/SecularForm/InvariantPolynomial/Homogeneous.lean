/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.InvariantPolynomial.Weyl
public import KAM.Frozen.Planetary.Defs.PlaneSq

/-!
# Homogeneous invariant polynomials

A homogeneous `O(2)`-invariant polynomial of degree `2k` in `n` planar vectors is a homogeneous
polynomial of degree `k` in the dot products (`exists_homogeneous_dot_poly`).  For two vectors
this yields the three invariants of the quadratic form (`quadratic_invariant`) and the six
invariants of the quartic form (`quartic_invariant`), which are the structural steps `qf-pair` and
`q4-str` of `bpP:p8:quadratic-form` and `bpP:p8:quartic`.
-/

@[expose] public noncomputable section
open MvPolynomial
namespace KAM.Planetary
namespace SecularForm
namespace Weyl

theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {φ : MvPolynomial σ ℝ} {m : ℕ}
    (hφ : φ.IsHomogeneous m) (r : ℝ) (g : σ → ℝ) :
    MvPolynomial.eval (fun i => r * g i) φ = r ^ m * MvPolynomial.eval g φ := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    rw [← Finset.sum_subset (Finset.subset_univ d.support) (fun i _ hi => by simpa using hi)]
    exact (hφ.degree_eq_sum_deg_support hd).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {n : ℕ}

/-- A homogeneous invariant of degree `2k` is a homogeneous polynomial of degree `k` in the dot
products. -/
theorem exists_homogeneous_dot_poly (P : MvPolynomial (Fin n × Fin 2) ℝ) (k : ℕ)
    (hInv : ∀ R : Matrix (Fin 2) (Fin 2) ℝ, R.transpose * R = 1 →
      ∀ u : Fin n → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => (R.mulVec (u ic.1)) ic.2) P =
        MvPolynomial.eval (fun ic => u ic.1 ic.2) P)
    (hscale : ∀ (r : ℝ) (u : Fin n → Fin 2 → ℝ),
      MvPolynomial.eval (fun ic => r * u ic.1 ic.2) P =
        r ^ (2 * k) * MvPolynomial.eval (fun ic => u ic.1 ic.2) P) :
    ∃ Q : MvPolynomial (Fin n × Fin n) ℝ, Q.IsHomogeneous k ∧ ∀ u : Fin n → Fin 2 → ℝ,
      MvPolynomial.eval (fun ic => u ic.1 ic.2) P =
        MvPolynomial.eval (fun ij => planeDot (u ij.1) (u ij.2)) Q := by
  obtain ⟨Q0, hQ0⟩ := e_weyl P hInv
  refine ⟨homogeneousComponent k Q0, homogeneousComponent_isHomogeneous k Q0, fun u => ?_⟩
  set g : Fin n × Fin n → ℝ := fun ij => planeDot (u ij.1) (u ij.2) with hg
  set T := Q0.totalDegree with hT
  let p : Polynomial ℝ := ∑ j ∈ Finset.range (T + 1),
    Polynomial.C (MvPolynomial.eval g (homogeneousComponent j Q0)) * Polynomial.X ^ (2 * j)
  have hp : ∀ r : ℝ, p.eval r = r ^ (2 * k) * MvPolynomial.eval (fun ic => u ic.1 ic.2) P := by
    intro r
    have h1 : MvPolynomial.eval (fun ij => r ^ 2 * g ij) Q0 =
        r ^ (2 * k) * MvPolynomial.eval (fun ic => u ic.1 ic.2) P := by
      rw [← hscale r u, hQ0 (fun i c => r * u i c)]
      refine congrArg (fun f => MvPolynomial.eval f Q0) ?_
      funext ij
      simp [hg, planeDot, Fin.sum_univ_two]; ring
    rw [← h1]
    have h2 : MvPolynomial.eval (fun ij => r ^ 2 * g ij) Q0 =
        ∑ j ∈ Finset.range (T + 1), (r ^ 2) ^ j * MvPolynomial.eval g (homogeneousComponent j Q0) := by
      conv_lhs => rw [← sum_homogeneousComponent (φ := Q0)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ =>
        eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous j Q0) (r ^ 2) g
    rw [h2]
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.sum_congr rfl fun j _ => by rw [← pow_mul]; ring
  have hpoly : p = Polynomial.C (MvPolynomial.eval (fun ic => u ic.1 ic.2) P) *
      Polynomial.X ^ (2 * k) := by
    apply Polynomial.funext
    intro r
    rw [hp r]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  have hcoef := congrArg (fun q => q.coeff (2 * k)) hpoly
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    mul_ite, mul_one, mul_zero, Polynomial.coeff_C_mul] at hcoef
  by_cases hk : k ≤ T
  · rw [Finset.sum_eq_single k] at hcoef
    · simpa using hcoef.symm
    · intro j _ hjk
      have : 2 * k ≠ 2 * j := by omega
      simp [this]
    · intro hk'
      exact absurd (Finset.mem_range.mpr (by omega)) hk'
  · replace hk : T < k := not_le.mp hk
    rw [homogeneousComponent_eq_zero k Q0 hk]
    have : ∑ j ∈ Finset.range (T + 1),
        (if 2 * k = 2 * j then MvPolynomial.eval g (homogeneousComponent j Q0) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have : 2 * k ≠ 2 * j := by
        have := Finset.mem_range.mp hj; omega
      simp [this]
    rw [this] at hcoef
    simpa using hcoef.symm

end Weyl
end SecularForm
end KAM.Planetary
