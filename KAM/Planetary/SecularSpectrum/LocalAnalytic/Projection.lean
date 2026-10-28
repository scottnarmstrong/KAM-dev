/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Secular spectrum: eigenprojections of a simple-spectrum symmetric matrix

Blueprint P, Part 9 (`stepP:p9:la-adj`).  For a symmetric matrix `M` whose characteristic
polynomial is `∏ (X - σ k)` with `σ` injective, the Lagrange polynomial `L_j(M)` is the orthogonal
rank-one eigenprojection onto the `σ j`-eigenspace.  It is a polynomial in `M`, hence analytic in
any analytic family; this is the form of the adjugate projection `adj(σ_j - M) / p'(σ_j)` used
below (the two coincide).  Here we collect the pointwise algebra: symmetry, idempotence,
`M Π_j = σ_j Π_j`, `Π_j Π_l = 0` and positivity of a diagonal entry of `Π_j`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Polynomial
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

/-- The Lagrange spectral projection `L_j(M)` for the nodes `σ`. -/
def eigProj (M : Mat n) (σ : Vec n) (j : Fin n) : Mat n :=
  aeval M (Lagrange.basis Finset.univ σ j)

section Algebra
variable {M : Mat n} {σ : Vec n}

lemma aeval_eq_zero_of_forall_eval (hσ : Function.Injective σ)
    (hch : M.charpoly = ∏ k, (X - C (σ k))) {q : ℝ[X]} (hq : ∀ m, q.eval (σ m) = 0) :
    aeval M q = 0 := by
  have hcop : Set.Pairwise (↑(Finset.univ : Finset (Fin n)))
      (IsCoprime on fun i => (X - C (σ i) : ℝ[X])) :=
    fun i _ j _ hij => Polynomial.pairwise_coprime_X_sub_C hσ hij
  have hdvd : M.charpoly ∣ q := by
    rw [hch]
    exact Finset.prod_dvd_of_coprime hcop fun i _ => dvd_iff_isRoot.2 (hq i)
  obtain ⟨c, rfl⟩ := hdvd
  rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]

lemma aeval_mulVec_of_eigen (p : ℝ[X]) {u : Vec n} {c : ℝ} (hu : M.mulVec u = c • u) :
    (aeval M p).mulVec u = p.eval c • u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, Matrix.add_mulVec, hp, hq, add_smul]
  | monomial k a =>
    have : ∀ k : ℕ, (M ^ k).mulVec u = c ^ k • u := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hu, smul_smul, pow_succ]
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, this, mul_smul]

lemma transpose_aeval (hM : M.transpose = M) (p : ℝ[X]) : (aeval M p).transpose = aeval M p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, Matrix.transpose_add, hp, hq]
  | monomial k a =>
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul,
      Matrix.transpose_pow, hM]

lemma eigProj_transpose (hM : M.transpose = M) (j : Fin n) :
    (eigProj M σ j).transpose = eigProj M σ j := transpose_aeval hM _

variable (hσ : Function.Injective σ) (hch : M.charpoly = ∏ k, (X - C (σ k)))
include hσ hch

lemma eigProj_mul (j l : Fin n) :
    eigProj M σ j * eigProj M σ l = if j = l then eigProj M σ j else 0 := by
  have := aeval_eq_zero_of_forall_eval hσ hch
    (q := Lagrange.basis Finset.univ σ j * Lagrange.basis Finset.univ σ l -
      if j = l then Lagrange.basis Finset.univ σ j else 0) (by
    intro m
    have hi := hσ.injOn (s := (Finset.univ : Finset (Fin n)))
    by_cases hjm : j = m <;> by_cases hlm : l = m
    · subst hjm; subst hlm
      simp [Lagrange.eval_basis_self hi (Finset.mem_univ _)]
    · subst hjm
      have : j ≠ l := fun h => hlm h.symm
      simp [this, Lagrange.eval_basis_of_ne hlm (Finset.mem_univ _)]
    · subst hlm
      have : j ≠ l := fun h => hjm h
      simp [this, Lagrange.eval_basis_of_ne hjm (Finset.mem_univ _)]
    · by_cases hjl : j = l
      · subst hjl; simp [Lagrange.eval_basis_of_ne hjm (Finset.mem_univ _)]
      · simp [hjl, Lagrange.eval_basis_of_ne hjm (Finset.mem_univ _)])
  unfold eigProj
  split_ifs with h
  · simpa [map_sub, h, sub_eq_zero] using this
  · simpa [map_sub, h, sub_eq_zero] using this

lemma mul_eigProj (j : Fin n) : M * eigProj M σ j = σ j • eigProj M σ j := by
  have := aeval_eq_zero_of_forall_eval hσ hch
    (q := X * Lagrange.basis Finset.univ σ j - C (σ j) * Lagrange.basis Finset.univ σ j) (by
    intro m
    have hi := hσ.injOn (s := (Finset.univ : Finset (Fin n)))
    by_cases hjm : j = m
    · subst hjm; simp [Lagrange.eval_basis_self hi (Finset.mem_univ _)]
    · simp [Lagrange.eval_basis_of_ne hjm (Finset.mem_univ _)])
  unfold eigProj
  rw [map_sub, sub_eq_zero, map_mul, map_mul, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at this
  exact this

omit hσ in
lemma exists_eigenvector (j : Fin n) : ∃ u : Vec n, u ≠ 0 ∧ M.mulVec u = σ j • u := by
  have hdet : (Matrix.scalar (Fin n) (σ j) - M).det = 0 := by
    rw [← Matrix.eval_charpoly, hch, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  obtain ⟨u, hu, hu0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨u, hu, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hu0
  simpa [Matrix.scalar_apply, Matrix.mulVec_diagonal] using hu0.symm

omit hch in
lemma eigProj_mulVec_eigenvector (j : Fin n) {u : Vec n} (hu : M.mulVec u = σ j • u) :
    (eigProj M σ j).mulVec u = u := by
  have h := aeval_mulVec_of_eigen (Lagrange.basis Finset.univ σ j) hu
  rw [Lagrange.eval_basis_self (hσ.injOn) (Finset.mem_univ _), one_smul] at h
  exact h

/-- Some diagonal entry of the eigenprojection is positive. -/
lemma exists_eigProj_diag_pos (hM : M.transpose = M) (j : Fin n) :
    ∃ k, 0 < eigProj M σ j k k := by
  set L := eigProj M σ j with hL
  have hLt : L.transpose = L := eigProj_transpose hM j
  have hLL : L * L = L := by simpa using eigProj_mul hσ hch j j
  obtain ⟨u, hu0, hu⟩ := exists_eigenvector hch j
  have hLu : L.mulVec u = u := eigProj_mulVec_eigenvector hσ j hu
  have hne : ∃ a b, L a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu0
    rw [← hLu]
    have : L = 0 := by ext a b; exact hcon a b
    simp [this]
  obtain ⟨a, b, hab⟩ := hne
  have hdiag : ∀ k, (L * L) k k = ∑ i, L k i ^ 2 := by
    intro k
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : L i k = L k i := by
      have := congrFun (congrFun hLt k) i
      simpa [Matrix.transpose_apply] using this
    rw [this, sq]
  by_contra hcon
  push Not at hcon
  have h1 : ∑ k, L k k ≤ 0 := Finset.sum_nonpos fun k _ => hcon k
  have h2 : ∑ k, L k k = ∑ k, ∑ i, L k i ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hdiag k, hLL]
  have h3 : 0 < ∑ k, ∑ i, L k i ^ 2 := by
    refine lt_of_lt_of_le (b := ∑ i, L a i ^ 2) ?_
      (Finset.single_le_sum (f := fun k => ∑ i, L k i ^ 2)
        (fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.mem_univ a))
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
      (f := fun i => L a i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ b))
  linarith

end Algebra

end SecularSpectrum

end KAM.Planetary
