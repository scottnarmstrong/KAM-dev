/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Matrix.Norms
public import KAM.Frozen.Defs.DotC
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Defs.TorsionAverage
public import KAM.Strip.Averages

/-!
# Matrix norms in Part 4

Blueprint Part 4, `bp:p4:matrix-norms` (its proof step `step:p4:mn-rowsum` is the proof of the
individual items below). Matrices carry the row-sum norm, the norm of `open scoped
Matrix.Norms.Operator`, as in `KAM/Matrix/Norms.lean`; `2n` rows or columns are indexed by
`Fin n ⊕ Fin n`, the first block being the angles.

* `KAM.Head.frameL0` and `KAM.Head.frameN0` are `L⁰ = (Id; 0)` and `N⁰ = (0; Id)`, the tangent and
  normal frames of the unperturbed torus (computed directly; the unperturbed-torus lemma is not
  used).
* (i) `KAM.norm_eq_iSup_rowSum`, `KAM.norm_toContinuousLinearMap_mulVecLin`,
  `Matrix.linfty_opNorm_mul` and `KAM.norm_continuousLinearMap_eq_norm_toMatrix'` (from
  `KAM/Matrix/Norms.lean`).
* (ii) `KAM.matrix_norm_transpose`.
* (iii) `KAM.Head.norm_frameL0` and its companions.
* (iv) `KAM.Head.dotℂ_omegaZero`, `KAM.Head.omegaZeroMatrix_transpose_mul_self`,
  `KAM.omegaZeroMatrix_mul_self`, `KAM.Head.ofReal_symplecticForm`.
* (v) `KAM.Head.norm_matrixAverage_le`, for the entrywise unit-cube average
  `KAM.Head.matrixAverage`, which is the shape of the frozen `KAM.torsionAverage`
  (`KAM.Head.torsionAverage_eq_matrixAverage`).
* `KAM.Head.matrix_norms_cor` bundles (i)-(v).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

namespace KAM.Head

/-! ### The frames `L⁰` and `N⁰` -/

section Frames

variable {n : ℕ}

/-- `L⁰ = (Id; 0)`, the `2n × n` matrix of `v ↦ (v, 0)`: the derivative of the unperturbed torus
`θ ↦ (θ, ι I_*)`. -/
def frameL0 (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := Matrix.fromRows 1 0

/-- `N⁰ = (0; Id)`, the `2n × n` matrix of `v ↦ (0, v)`: the normal frame of the unperturbed
torus. -/
def frameN0 (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ := Matrix.fromRows 0 1

/-- The normal frame of the unperturbed torus is `N⁰ = Ω₀ L⁰`. -/
theorem omegaZeroMatrix_mul_frameL0 : omegaZeroMatrix n * frameL0 n = frameN0 n := by
  unfold omegaZeroMatrix frameL0 frameN0
  rw [Matrix.fromBlocks_mul_fromRows]
  simp

/-- A matrix whose absolute row sums are at most `1`, with one equal to `1`, has norm `1`. -/
theorem norm_eq_one_of_rowSum {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k ℂ)
    (h : ∀ i, ∑ j, ‖M i j‖ ≤ 1) (i₀ : m) (h₀ : ∑ j, ‖M i₀ j‖ = 1) : ‖M‖ = 1 :=
  le_antisymm ((norm_le_iff_forall_rowSum zero_le_one).2 h) (h₀ ▸ rowSum_le_norm M i₀)

/-- `‖L⁰‖ = 1` for `n ≥ 1` (the empty matrix has norm `0`). -/
theorem norm_frameL0 (hn : 0 < n) : ‖frameL0 n‖ = 1 := by
  refine norm_eq_one_of_rowSum _ ?_ (Sum.inl ⟨0, hn⟩) ?_
  · rintro (i | i) <;> simp [frameL0, Matrix.one_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, apply_ite norm]
  · simp [frameL0, Matrix.one_apply, apply_ite norm]

/-- `‖(L⁰)ᵀ‖ = 1` for `n ≥ 1`. -/
theorem norm_frameL0_transpose (hn : 0 < n) : ‖(frameL0 n).transpose‖ = 1 := by
  refine norm_eq_one_of_rowSum _ ?_ ⟨0, hn⟩ ?_
  · intro j
    rw [Fintype.sum_sum_type]
    simp [frameL0, Matrix.one_apply, apply_ite norm]
  · rw [Fintype.sum_sum_type]
    simp [frameL0, Matrix.one_apply, apply_ite norm]

/-- `‖N⁰‖ = 1` for `n ≥ 1`. -/
theorem norm_frameN0 (hn : 0 < n) : ‖frameN0 n‖ = 1 := by
  refine norm_eq_one_of_rowSum _ ?_ (Sum.inr ⟨0, hn⟩) ?_
  · rintro (i | i) <;> simp [frameN0, Matrix.one_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, apply_ite norm]
  · simp [frameN0, Matrix.one_apply, apply_ite norm]

/-- `‖(N⁰)ᵀ‖ = 1` for `n ≥ 1`. -/
theorem norm_frameN0_transpose (hn : 0 < n) : ‖(frameN0 n).transpose‖ = 1 := by
  refine norm_eq_one_of_rowSum _ ?_ ⟨0, hn⟩ ?_
  · intro j
    rw [Fintype.sum_sum_type]
    simp [frameN0, Matrix.one_apply, apply_ite norm]
  · rw [Fintype.sum_sum_type]
    simp [frameN0, Matrix.one_apply, apply_ite norm]

end Frames

/-! ### The bilinear dot product and the symplectic form (item (iv)) -/

section Bilinear

variable {n : ℕ}

/-- The frozen bilinear `dotℂ` is the dot product `uᵀ v` of the vectors indexed by
`Fin n ⊕ Fin n`. -/
theorem dotℂ_eq_dotProduct (u v : (Fin n → ℂ) × (Fin n → ℂ)) :
    dotℂ u v = (Equiv.sumArrowEquivProdArrow _ _ _).symm u ⬝ᵥ
      (Equiv.sumArrowEquivProdArrow _ _ _).symm v := by
  simp only [dotℂ, dotProduct, Fintype.sum_sum_type, Finset.sum_add_distrib]
  rfl

/-- Blueprint `bp:p4:matrix-norms` (iv): `dotℂ(x, Ω₀ y) = xᵀ Ω₀ y`. -/
theorem dotℂ_omegaZero (x y : (Fin n → ℂ) × (Fin n → ℂ)) :
    dotℂ x (omegaZero y) = (Equiv.sumArrowEquivProdArrow _ _ _).symm x ⬝ᵥ
      (omegaZeroMatrix n).mulVec ((Equiv.sumArrowEquivProdArrow _ _ _).symm y) := by
  rw [omegaZeroMatrix_mulVec, dotℂ_eq_dotProduct]

/-- Blueprint `bp:p4:matrix-norms` (iv): `Ω₀ᵀ Ω₀ = Id`. -/
theorem omegaZeroMatrix_transpose_mul_self :
    (omegaZeroMatrix n).transpose * omegaZeroMatrix n = 1 := by
  rw [omegaZeroMatrix_transpose, neg_mul, omegaZeroMatrix_mul_self, neg_neg]

/-- Blueprint `bp:p4:matrix-norms` (iv): for real `x, y`, the frozen `symplecticForm x y` is
`(ι x)ᵀ Ω₀ (ι y)`, where `ι` is the real inclusion and the real number is read in `ℂ`. -/
theorem ofReal_symplecticForm (x y : (Fin n → ℝ) × (Fin n → ℝ)) :
    ((symplecticForm x y : ℝ) : ℂ) =
      (Equiv.sumArrowEquivProdArrow _ _ _).symm
          ((fun i => (x.1 i : ℂ), fun i => (x.2 i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ)) ⬝ᵥ
        (omegaZeroMatrix n).mulVec ((Equiv.sumArrowEquivProdArrow _ _ _).symm
          ((fun i => (y.1 i : ℂ), fun i => (y.2 i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ))) := by
  rw [← dotℂ_omegaZero]
  simp only [symplecticForm, dotℂ, omegaZero, Pi.neg_apply, Complex.ofReal_sum,
    Complex.ofReal_sub, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Bilinear

/-! ### Averages of matrix-valued functions (item (v)) -/

section Average

variable {n p q : ℕ}

/-- The entrywise average over the unit cube `[0,1]ⁿ` of a matrix-valued function; the shape of the
frozen `KAM.torsionAverage`. -/
def matrixAverage (A : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun i j => torusAverage fun x => A x i j

/-- The frozen `torsionAverage` is the entrywise average of the torsion over the real torus. -/
theorem torsionAverage_eq_matrixAverage (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) :
    torsionAverage h K ω = matrixAverage fun x => torsion h K ω (fun l => (x l : ℂ)) := rfl

/-- Blueprint `bp:p4:matrix-norms` (v): if `A : [0,1]ⁿ → ℂ^{p×q}` is continuous and `‖A‖ ≤ S`
on the cube, then `‖∫ A‖ ≤ S`. -/
theorem norm_matrixAverage_le {A : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ} {S : ℝ}
    (hA : ContinuousOn A (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    (hS : ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), ‖A x‖ ≤ S) :
    ‖matrixAverage A‖ ≤ S := by
  set cube : Set (Fin n → ℝ) := Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1 with hcube
  have hS0 : 0 ≤ S := by
    have h0 : (0 : Fin n → ℝ) ∈ cube := fun i _ => ⟨le_rfl, zero_le_one⟩
    exact (norm_nonneg _).trans (hS 0 h0)
  have hint : ∀ i j, IntegrableOn (fun x => A x i j) cube := by
    intro i j
    refine ContinuousOn.integrableOn_compact ?_ ?_
    · rw [hcube, Set.pi_univ_Icc]
      exact isCompact_Icc
    · exact continuousOn_pi.1 (continuousOn_pi.1 hA i) j
  -- the bound on `M v` for `‖v‖ ≤ 1`
  obtain ⟨v, hv, hMv⟩ := (isGreatest_norm_mulVec (matrixAverage A)).1
  have hv1 : ‖v‖ ≤ 1 := by simpa using hv
  rw [← hMv]
  refine (pi_norm_le_iff_of_nonneg hS0).2 fun i => ?_
  have hcomp : (matrixAverage A).mulVec v i = torusAverage fun x => (A x).mulVec v i := by
    simp only [matrixAverage, torusAverage, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
    · exact fun j _ => (hint i j).mul_const _
  rw [hcomp]
  refine norm_torusAverage_le (fun x hx => ?_)
  calc ‖(A x).mulVec v i‖ ≤ ‖(A x).mulVec v‖ := norm_le_pi_norm _ i
    _ ≤ ‖A x‖ * ‖v‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ S * 1 := mul_le_mul (hS x hx) hv1 (norm_nonneg _) hS0
    _ = S := mul_one S

end Average

/-! ### The corollary -/

/-- Blueprint `bp:p4:matrix-norms`. With the row-sum norm `‖A‖ = max_i ∑_j |A_ij|` on matrices:

1. `‖A‖` is the supremum of the row sums and the operator norm of `v ↦ A v` for the max norms;
   it is submultiplicative; and for a linear map `ℓ : ℂ^q → ℂ^p` (such as `fderiv` of `K`) the
   operator norm `‖ℓ‖` is the row-sum norm of its matrix.
2. `‖Aᵀ‖ ≤ p ‖A‖` for `A ∈ ℂ^{p×q}`.
3. For `n ≥ 1`: `‖Ω₀‖ = ‖L⁰‖ = ‖(L⁰)ᵀ‖ = ‖N⁰‖ = ‖(N⁰)ᵀ‖ = 1`.
4. `dotℂ(x, Ω₀ y) = xᵀ Ω₀ y`, `Ω₀ᵀ Ω₀ = Id`, `Ω₀² = -Id`, and for real `x, y`,
   `symplecticForm x y = (ι x)ᵀ Ω₀ (ι y)`.
5. For `A : [0,1]ⁿ → ℂ^{p×q}` continuous with `‖A‖ ≤ S` on the cube, `‖∫ A‖ ≤ S` (entrywise
   integral, as in the frozen `torsionAverage`).

The hypothesis `0 < n` in item 3 is Part 0's standing convention `n ≥ 2` (for `n = 0` the matrices
are empty and have norm `0`). -/
theorem matrix_norms_cor :
    ((∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q) ℂ),
        ‖A‖ = ⨆ i, ∑ j, ‖A i j‖ ∧
          ‖LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)‖ = ‖A‖) ∧
      (∀ (p q r : ℕ) (A : Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin q) (Fin r) ℂ),
        ‖A * B‖ ≤ ‖A‖ * ‖B‖) ∧
      (∀ (p q : ℕ) (ℓ : (Fin q → ℂ) →L[ℂ] (Fin p → ℂ)),
        ‖ℓ‖ = ‖LinearMap.toMatrix' (ℓ : (Fin q → ℂ) →ₗ[ℂ] (Fin p → ℂ))‖)) ∧
    (∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q) ℂ), ‖A.transpose‖ ≤ p * ‖A‖) ∧
    (∀ n : ℕ, 0 < n →
      ‖omegaZeroMatrix n‖ = 1 ∧ ‖frameL0 n‖ = 1 ∧ ‖(frameL0 n).transpose‖ = 1 ∧
        ‖frameN0 n‖ = 1 ∧ ‖(frameN0 n).transpose‖ = 1) ∧
    ((∀ (n : ℕ) (x y : (Fin n → ℂ) × (Fin n → ℂ)),
        dotℂ x (omegaZero y) = (Equiv.sumArrowEquivProdArrow _ _ _).symm x ⬝ᵥ
          (omegaZeroMatrix n).mulVec ((Equiv.sumArrowEquivProdArrow _ _ _).symm y)) ∧
      (∀ n : ℕ, (omegaZeroMatrix n).transpose * omegaZeroMatrix n = 1) ∧
      (∀ n : ℕ, omegaZeroMatrix n * omegaZeroMatrix n = -1) ∧
      (∀ (n : ℕ) (x y : (Fin n → ℝ) × (Fin n → ℝ)),
        ((symplecticForm x y : ℝ) : ℂ) =
          (Equiv.sumArrowEquivProdArrow _ _ _).symm
              ((fun i => (x.1 i : ℂ), fun i => (x.2 i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ)) ⬝ᵥ
            (omegaZeroMatrix n).mulVec ((Equiv.sumArrowEquivProdArrow _ _ _).symm
              ((fun i => (y.1 i : ℂ), fun i => (y.2 i : ℂ)) : (Fin n → ℂ) × (Fin n → ℂ))))) ∧
    (∀ (n p q : ℕ) (A : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ) (S : ℝ),
      ContinuousOn A (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) →
      (∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), ‖A x‖ ≤ S) →
      ‖matrixAverage A‖ ≤ S) :=
  ⟨⟨fun _ _ A => ⟨norm_eq_iSup_rowSum A, norm_toContinuousLinearMap_mulVecLin A⟩,
      fun _ _ _ A B => Matrix.linfty_opNorm_mul A B,
      fun _ _ ℓ => norm_continuousLinearMap_eq_norm_toMatrix' ℓ⟩,
    fun p q A => (matrix_norm_transpose p q A).2,
    fun _ hn => ⟨norm_omegaZeroMatrix hn, norm_frameL0 hn, norm_frameL0_transpose hn,
      norm_frameN0 hn, norm_frameN0_transpose hn⟩,
    ⟨fun _ => dotℂ_omegaZero, fun _ => omegaZeroMatrix_transpose_mul_self,
      fun _ => omegaZeroMatrix_mul_self, fun _ => ofReal_symplecticForm⟩,
    fun _ _ _ _ _ hA hS => norm_matrixAverage_le hA hS⟩

end KAM.Head

end
