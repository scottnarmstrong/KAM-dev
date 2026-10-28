/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Weyl's inequality for the sorted spectrum

Blueprint P, Part 10 (`bpP:p10:weyl`, `stepP:p10:weyl-mm`, `stepP:p10:weyl-pert`): the sorted
eigenvalues of Hermitian matrices move by at most the Euclidean operator norm of the perturbation.

The min-max step is a direct subspace-counting argument (`sorted_le_of_quad_le`): `n - 1` linear
conditions on `Fin n → ℝ` have a nonzero solution, which lies in the top eigenspace span of one
matrix and the bottom eigenspace span of the other.  Everything is stated with explicit
Euclidean quantities on `Fin n → ℝ`.  The spectral input is Mathlib's `eigenvectorUnitary` matrix.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

/-- Orthonormal eigenframe indexed by the sorted index: Parseval and the diagonal quadratic form. -/
lemma exists_eigenframe (M : Mat n) (hM : M.IsHermitian) :
    ∃ v : Fin n → Vec n, ∀ x : Vec n,
      (∑ j, (v j ⬝ᵥ x) ^ 2 = x ⬝ᵥ x) ∧
      (x ⬝ᵥ M.mulVec x = ∑ j, sorted M hM j * (v j ⬝ᵥ x) ^ 2) := by
  let U : Mat n := (hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hU1 : U.transpose * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self (hM.eigenvectorUnitary))
  have hU2 : U * U.transpose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      (Unitary.coe_mul_star_self (hM.eigenvectorUnitary))
  have hspec : M = U * Matrix.diagonal hM.eigenvalues * U.transpose := by
    have := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [U, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  let τ : Fin n ≃ Fin n :=
    Fin.revPerm.trans ((finCongr (Fintype.card_fin n).symm).trans e)
  have hτ : ∀ i, sorted M hM i = hM.eigenvalues (τ i) := by
    intro i
    simp [sorted, Matrix.IsHermitian.eigenvalues, τ, e]
  refine ⟨fun j i => U i (τ j), fun x => ?_⟩
  have hv : ∀ j, (fun i => U i (τ j)) ⬝ᵥ x = (U.transpose.mulVec x) (τ j) := fun j => by
    simp [Matrix.mulVec, dotProduct]
  have hUy : U.mulVec (U.transpose.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec]
  have hdot : ∀ w : Vec n, x ⬝ᵥ U.mulVec w = (U.transpose.mulVec x) ⬝ᵥ w := fun w => by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  simp only [hv]
  constructor
  · rw [Equiv.sum_comp τ (fun k => (U.transpose.mulVec x) k ^ 2)]
    have hxx : x ⬝ᵥ x = (U.transpose.mulVec x) ⬝ᵥ (U.transpose.mulVec x) := by
      rw [← hdot, hUy]
    rw [hxx]
    simp [dotProduct, sq]
  · conv_lhs => rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdot]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    rw [← Equiv.sum_comp τ]
    exact Finset.sum_congr rfl fun j _ => by rw [hτ]; ring

lemma sorted_mono (M : Mat n) (hM : M.IsHermitian) : Monotone (sorted M hM) := by
  intro i j hij
  exact hM.eigenvalues₀_antitone (Fin.rev_le_rev.2 hij |> fun h => by simpa using h)

/-- The Rayleigh quotient of a symmetric perturbation is controlled by `op2`. -/
lemma abs_dot_mulVec_le (E : Mat n) (x : Vec n) :
    |x ⬝ᵥ E.mulVec x| ≤ op2 E * (x ⬝ᵥ x) := by
  have hx : length2 x ^ 2 = x ⬝ᵥ x := by
    unfold length2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
    simp [dotProduct, sq]
  have hy : length2 (E.mulVec x) ^ 2 = E.mulVec x ⬝ᵥ E.mulVec x := by
    unfold length2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [dotProduct, sq]
  have hcs : |x ⬝ᵥ E.mulVec x| ≤ length2 x * length2 (E.mulVec x) := by
    rw [← Real.sqrt_sq_eq_abs]
    unfold length2
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    simpa [dotProduct, sq] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (E.mulVec x)
  calc |x ⬝ᵥ E.mulVec x| ≤ length2 x * length2 (E.mulVec x) := hcs
    _ ≤ length2 x * (op2 E * length2 x) :=
      mul_le_mul_of_nonneg_left (length2_mulVec_le_op2 E x) (length2_nonneg x)
    _ = op2 E * (x ⬝ᵥ x) := by rw [← hx]; ring

/-- Min-max step: a quadratic-form bound with slack `t` bounds the sorted spectra. -/
theorem sorted_le_of_quad_le (B C : Mat n) (hB : B.IsHermitian) (hC : C.IsHermitian) (t : ℝ)
    (h : ∀ x : Vec n, x ⬝ᵥ B.mulVec x ≤ x ⬝ᵥ C.mulVec x + t * (x ⬝ᵥ x)) (i : Fin n) :
    sorted B hB i ≤ sorted C hC i + t := by
  obtain ⟨w, hw⟩ := exists_eigenframe B hB
  obtain ⟨u, hu⟩ := exists_eigenframe C hC
  let f : Vec n →ₗ[ℝ] ({j : Fin n // j ≠ i} → ℝ) :=
    { toFun := fun x j => if j.1 < i then w j.1 ⬝ᵥ x else u j.1 ⬝ᵥ x
      map_add' := fun x y => by
        funext j; by_cases hj : j.1 < i <;> simp [hj, dotProduct_add]
      map_smul' := fun c x => by
        funext j; by_cases hj : j.1 < i <;> simp [hj, dotProduct_smul] }
  have hlt : Module.finrank ℝ ({j : Fin n // j ≠ i} → ℝ) < Module.finrank ℝ (Vec n) := by
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl]
    have : 0 < n := Fin.pos i
    omega
  obtain ⟨x, hxk, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (f.ker_ne_bot_of_finrank_lt hlt)
  have hf : ∀ j : Fin n, ∀ hj : j ≠ i, (if j < i then w j ⬝ᵥ x else u j ⬝ᵥ x) = 0 := fun j hj =>
    congr_fun (LinearMap.mem_ker.1 hxk) ⟨j, hj⟩
  have hpos : 0 < x ⬝ᵥ x := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)) fun h0 => hx0 ?_
    funext j
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).1
      h0.symm j (Finset.mem_univ j)
    simpa using this
  have hB' : sorted B hB i * (x ⬝ᵥ x) ≤ x ⬝ᵥ B.mulVec x := by
    rw [(hw x).2, ← (hw x).1, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_trichotomy j i with hj | rfl | hj
    · have := hf j hj.ne
      simp [hj] at this
      simp [this]
    · exact le_of_eq (by ring)
    · exact mul_le_mul_of_nonneg_right (sorted_mono B hB hj.le) (sq_nonneg _)
  have hC' : x ⬝ᵥ C.mulVec x ≤ sorted C hC i * (x ⬝ᵥ x) := by
    rw [(hu x).2, ← (hu x).1, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_trichotomy j i with hj | rfl | hj
    · exact mul_le_mul_of_nonneg_right (sorted_mono C hC hj.le) (sq_nonneg _)
    · exact le_of_eq (by ring)
    · have := hf j hj.ne'
      simp [not_lt.2 hj.le] at this
      simp [this]
  have := h x
  nlinarith

end SecularSpectrum

namespace Nondegeneracy
open SecularForm SecularSpectrum
variable {n d m : ℕ}

/-- **Weyl's inequality** (`bpP:p10:weyl`). -/
theorem weyl (A E : Mat n) (hA : A.IsHermitian) (hE : E.IsHermitian)
    (hAE : (A+E).IsHermitian) :
    ∀ i, |sorted (A+E) hAE i - sorted A hA i| ≤ op2 E := by
  intro i
  have hq : ∀ x : Vec n, x ⬝ᵥ (A + E).mulVec x = x ⬝ᵥ A.mulVec x + x ⬝ᵥ E.mulVec x := fun x => by
    rw [Matrix.add_mulVec, dotProduct_add]
  have h1 := sorted_le_of_quad_le (A + E) A hAE hA (op2 E) (fun x => by
    rw [hq]; linarith [(abs_le.1 (abs_dot_mulVec_le E x)).2]) i
  have h2 := sorted_le_of_quad_le A (A + E) hA hAE (op2 E) (fun x => by
    rw [hq]; linarith [(abs_le.1 (abs_dot_mulVec_le E x)).1]) i
  exact abs_le.2 ⟨by linarith, by linarith⟩

end Nondegeneracy
end KAM.Planetary
end
