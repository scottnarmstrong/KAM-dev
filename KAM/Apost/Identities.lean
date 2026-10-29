/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Hamiltonian
public import KAM.Torus.FrozenAgreement
public import KAM.Matrix.Calculus
import KAM.Matrix.Inverse

/-!
# Frame identities

Blueprint Part 2, Lemma `bp:p2:frame-identities` (`KAM.Apost.frame_identities`). Let `K` be
holomorphic on `T_r`, with `K(T_r) ⊆ 𝔅` and `det G` a unit on `T_r`. Then, on `T_r`, with
`L = DK`, `N = Ω₀ L B`, `P = (L N)`, `Q = -Ω₀ Pᵀ Ω₀`:

* (a) `Lᵀ Ω₀ N = -I`, `Nᵀ Ω₀ L = I`, `Nᵀ Ω₀ N = B Ω_K B`;
* (b) `Pᵀ Ω₀ P = Ω₀ + E_sym`, `E_sym = diag(Ω_K, B Ω_K B)`;
* (c) `∂_ω L = A L - DE`;
* (d) `∂_ω Ω_K = -(DE)ᵀ Ω₀ L - Lᵀ Ω₀ DE`;
* (e) `Q (A P - ∂_ω P) = Λ + E_red`;
* (f) `Q P = I - Ω₀ E_sym` and `Q E = -η`.

The proof follows the blueprint step by step. All helper lemmas live in the namespace
`KAM.Apost.Identities`; the matrix algebra is done at the level of whole matrices
(`Matrix.fromCols`, `Matrix.fromRows_mul_fromCols`, `Matrix.fromBlocks_multiply`), never entrywise
on `2n × 2n` products.

Blueprint steps and their Lean lemmas (`alg_*` are the abstract matrix identities):

* `step:p2:fi-products`: `alg_LtON`, `alg_NtOL`, `alg_NtON`; `fi_LtON`, `fi_NtOL`, `fi_NtON`;
* `step:p2:fi-sym`: `alg_PtOP`, `alg_symDefect`; `fi_PtOP`, `fi_symDefect`;
* `step:p2:fi-dl`: `fderiv_tangentMat_apply`, `fderiv_tangent_column_omega`, `fi_dL`;
* `step:p2:fi-domegak`: `alg_dLagrange`, `fi_dLagrange`;
* `step:p2:fi-blocks`: `alg_reduced`, `fi_reduced`;
* `step:p2:fi-22`: `fi_dLtON`, `alg_LtOXN`, `fi_LtOXN`;
* `step:p2:fi-q`: `fi_QP`, `fi_QE`.

The derivative steps use the symmetry of mixed second derivatives of the holomorphic `K`
(`KAM.fderiv_apply_comm_of_differentiableOn`, from `bp:p1:holomorphic-regularity`), the product
and transpose rules of `KAM/Matrix/Calculus.lean`, and `Aᵀ Ω₀ + Ω₀ A = 0` for `A = DX_h ∘ K`
(`KAM.Apost.hamiltonian`(d)). The torsion enters through `KAM.Torus.torsion_eq_mat`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Apost.Identities

open KAM.Torus

section Algebra

variable {n : ℕ}

/-- `Ω₀ (Ω₀ M) = -M`. -/
theorem omega_mul_omega_mul {ι : Type*} [Fintype ι] (M : Matrix (Fin n ⊕ Fin n) ι ℂ) :
    omegaZeroMatrix n * (omegaZeroMatrix n * M) = -M := by
  rw [← Matrix.mul_assoc, omegaZeroMatrix_mul_self, Matrix.neg_mul, Matrix.one_mul]

variable {L : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) ℂ}

/-- Step `step:p2:fi-products`: `Lᵀ Ω₀ N = -I` for `N = Ω₀ L B` with `Lᵀ L B = I`. -/
theorem alg_LtON (hLB : Lᵀ * L * B = 1) :
    Lᵀ * omegaZeroMatrix n * (omegaZeroMatrix n * L * B) = -1 := by
  simp only [Matrix.mul_assoc, omega_mul_omega_mul, Matrix.mul_neg]
  rw [← Matrix.mul_assoc, hLB]

/-- Step `step:p2:fi-products`: `Nᵀ Ω₀ L = I` for `N = Ω₀ L B` with `B Lᵀ L = I`, `Bᵀ = B`. -/
theorem alg_NtOL (hBL : B * (Lᵀ * L) = 1) (hB : Bᵀ = B) :
    (omegaZeroMatrix n * L * B)ᵀ * omegaZeroMatrix n * L = 1 := by
  simp only [Matrix.transpose_mul, omegaZeroMatrix_transpose, hB, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, omega_mul_omega_mul, neg_neg]
  exact hBL

/-- Step `step:p2:fi-products`: `Nᵀ Ω₀ N = B (Lᵀ Ω₀ L) B` for `N = Ω₀ L B`, `Bᵀ = B`. -/
theorem alg_NtON (hB : Bᵀ = B) :
    (omegaZeroMatrix n * L * B)ᵀ * omegaZeroMatrix n * (omegaZeroMatrix n * L * B) =
      B * (Lᵀ * omegaZeroMatrix n * L) * B := by
  simp only [Matrix.transpose_mul, omegaZeroMatrix_transpose, hB, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, omega_mul_omega_mul, neg_neg]

/-- Step `step:p2:fi-sym`: the block form of `Pᵀ Ω₀ P` for `P = (L N)`, `N = Ω₀ L B`. -/
theorem alg_PtOP (hLB : Lᵀ * L * B = 1) (hBL : B * (Lᵀ * L) = 1) (hB : Bᵀ = B) :
    (Matrix.fromCols L (omegaZeroMatrix n * L * B))ᵀ * omegaZeroMatrix n *
        Matrix.fromCols L (omegaZeroMatrix n * L * B) =
      Matrix.fromBlocks (Lᵀ * omegaZeroMatrix n * L) (-1) 1
        (B * (Lᵀ * omegaZeroMatrix n * L) * B) := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
    alg_LtON hLB, alg_NtOL hBL hB, alg_NtON hB]

/-- Step `step:p2:fi-sym`, subtracting `Ω₀`: `Pᵀ Ω₀ P - Ω₀ = diag(Lᵀ Ω₀ L, B (Lᵀ Ω₀ L) B)`. -/
theorem alg_symDefect (hLB : Lᵀ * L * B = 1) (hBL : B * (Lᵀ * L) = 1) (hB : Bᵀ = B) :
    (Matrix.fromCols L (omegaZeroMatrix n * L * B))ᵀ * omegaZeroMatrix n *
        Matrix.fromCols L (omegaZeroMatrix n * L * B) - omegaZeroMatrix n =
      Matrix.fromBlocks (Lᵀ * omegaZeroMatrix n * L) 0 0
        (B * (Lᵀ * omegaZeroMatrix n * L) * B) := by
  rw [alg_PtOP hLB hBL hB, sub_eq_iff_eq_add, omegaZeroMatrix, Matrix.fromBlocks_add]
  simp

variable {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {DE N Y : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ}

/-- Step `step:p2:fi-domegak`: the derivative of `Lᵀ Ω₀ L` along `ω`, given
`∂_ω L = A L - DE` and `Aᵀ Ω₀ + Ω₀ A = 0`. -/
theorem alg_dLagrange (hA : Aᵀ * omegaZeroMatrix n + omegaZeroMatrix n * A = 0) :
    (A * L - DE)ᵀ * omegaZeroMatrix n * L + Lᵀ * omegaZeroMatrix n * (A * L - DE) =
      -(DEᵀ * omegaZeroMatrix n * L) - Lᵀ * omegaZeroMatrix n * DE := by
  have h1 : (A * L - DE)ᵀ * omegaZeroMatrix n * L + Lᵀ * omegaZeroMatrix n * (A * L - DE) =
      Lᵀ * (Aᵀ * omegaZeroMatrix n + omegaZeroMatrix n * A) * L -
        DEᵀ * omegaZeroMatrix n * L - Lᵀ * omegaZeroMatrix n * DE := by
    rw [Matrix.transpose_sub, Matrix.transpose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [h1, hA]
  simp

/-- Step `step:p2:fi-22`: `Lᵀ Ω₀ (A N - Y) = -(DE)ᵀ Ω₀ N`, given the differentiated identity
`(A L - DE)ᵀ Ω₀ N + Lᵀ Ω₀ Y = 0` and `Aᵀ Ω₀ + Ω₀ A = 0`. -/
theorem alg_LtOXN (hA : Aᵀ * omegaZeroMatrix n + omegaZeroMatrix n * A = 0)
    (h0 : (A * L - DE)ᵀ * omegaZeroMatrix n * N + Lᵀ * omegaZeroMatrix n * Y = 0) :
    Lᵀ * omegaZeroMatrix n * (A * N - Y) = -(DEᵀ * omegaZeroMatrix n * N) := by
  have hY : Lᵀ * omegaZeroMatrix n * Y = -((A * L - DE)ᵀ * omegaZeroMatrix n * N) :=
    eq_neg_of_add_eq_zero_right h0
  have h1 : Lᵀ * omegaZeroMatrix n * (A * N - Y) =
      Lᵀ * (Aᵀ * omegaZeroMatrix n + omegaZeroMatrix n * A) * N -
        DEᵀ * omegaZeroMatrix n * N := by
    rw [Matrix.mul_sub, hY, sub_neg_eq_add, Matrix.transpose_sub, Matrix.transpose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  rw [h1, hA]
  simp

end Algebra

/-! ### Items (a), (b), (f): pointwise matrix algebra -/

section Pointwise

variable {n : ℕ} (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
  (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) {θ : Fin n → ℂ}

/-- `G⁻¹` is symmetric (`G = Lᵀ L` is). -/
theorem gram_inv_transpose : ((gramMatrix K θ)⁻¹)ᵀ = (gramMatrix K θ)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, gramMatrix_eq_tangentMat_transpose_mul]
  simp

theorem tangent_gram_inv (hG : IsUnit (gramMatrix K θ).det) :
    (tangentMat K θ)ᵀ * tangentMat K θ * (gramMatrix K θ)⁻¹ = 1 := by
  rw [← gramMatrix_eq_tangentMat_transpose_mul]
  exact gramMatrix_mul_inv K hG

theorem gram_inv_tangent (hG : IsUnit (gramMatrix K θ).det) :
    (gramMatrix K θ)⁻¹ * ((tangentMat K θ)ᵀ * tangentMat K θ) = 1 := by
  rw [← gramMatrix_eq_tangentMat_transpose_mul]
  exact inv_gramMatrix_mul K hG

/-- Step `step:p2:fi-products`, first identity of (a): `Lᵀ Ω₀ N = -I`. -/
theorem fi_LtON (hG : IsUnit (gramMatrix K θ).det) :
    (tangentMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ = -1 :=
  alg_LtON (tangent_gram_inv K hG)

/-- Step `step:p2:fi-products`, second identity of (a): `Nᵀ Ω₀ L = I`. -/
theorem fi_NtOL (hG : IsUnit (gramMatrix K θ).det) :
    (normalMat K θ)ᵀ * omegaZeroMatrix n * tangentMat K θ = 1 :=
  alg_NtOL (gram_inv_tangent K hG) (gram_inv_transpose K)

/-- Step `step:p2:fi-products`, third identity of (a): `Nᵀ Ω₀ N = B Ω_K B`. -/
theorem fi_NtON :
    (normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ =
      (gramMatrix K θ)⁻¹ * lagrangeMat K θ * (gramMatrix K θ)⁻¹ :=
  alg_NtON (gram_inv_transpose K)

/-- Step `step:p2:fi-sym`, first half of (b): `Pᵀ Ω₀ P = Ω₀ + E_sym` (the definition of
`E_sym`). -/
theorem fi_PtOP : (frameMat K θ)ᵀ * omegaZeroMatrix n * frameMat K θ =
    omegaZeroMatrix n + symDefect K θ := by
  rw [symDefect]
  abel

/-- Step `step:p2:fi-sym`, second half of (b): `E_sym = diag(Ω_K, B Ω_K B)`. -/
theorem fi_symDefect (hG : IsUnit (gramMatrix K θ).det) :
    symDefect K θ = Matrix.fromBlocks (lagrangeMat K θ) 0 0
      ((gramMatrix K θ)⁻¹ * lagrangeMat K θ * (gramMatrix K θ)⁻¹) :=
  alg_symDefect (tangent_gram_inv K hG) (gram_inv_tangent K hG) (gram_inv_transpose K)

/-- Step `step:p2:fi-q`, first half of (f): `Q P = I - Ω₀ E_sym`. -/
theorem fi_QP : reducer K θ * frameMat K θ = 1 - omegaZeroMatrix n * symDefect K θ := by
  have h1 : reducer K θ * frameMat K θ =
      -(omegaZeroMatrix n * ((frameMat K θ)ᵀ * omegaZeroMatrix n * frameMat K θ)) := by
    simp only [reducer, Matrix.neg_mul, Matrix.mul_assoc]
  rw [h1, fi_PtOP, Matrix.mul_add, omegaZeroMatrix_mul_self]
  simp [sub_eq_add_neg, add_comm]

/-- Step `step:p2:fi-q`, second half of (f): `Q E = -η`. -/
theorem fi_QE : reducer K θ *ᵥ sumVec n (invarianceError h K ω θ) = -eta h K ω θ := by
  rw [reducer, eta, Matrix.neg_mulVec]

end Pointwise


/-! ### Items (c), (d): the derivatives of `L` and `Ω_K` along `ω` -/

section Derivatives

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ} {θ : Fin n → ℂ}

/-- The entries of `colMat U`: column `j` is `sumVec (U e_j)`. -/
theorem colMat_apply {q : ℕ} (U : (Fin q → ℂ) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ)) (s : Fin n ⊕ Fin n)
    (j : Fin q) : colMat U s j = sumVec n (U (Pi.single j 1)) s := by
  have h := congrFun (colMat_mulVec U (Pi.single j 1)) s
  simpa [Matrix.mulVec_single_one] using h

/-- A directional derivative of a holomorphic `K` is differentiable on the strip. -/
theorem differentiableAt_fderiv_apply (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hθ : θ ∈ complexStrip n r) (v : Fin n → ℂ) :
    DifferentiableAt ℂ (fun y => fderiv ℂ K y v) θ :=
  ((holomorphic_regularity (isOpen_complexStrip n r) hK).1.differentiableAt
    ((isOpen_complexStrip n r).mem_nhds hθ)).clm_apply (differentiableAt_const v)

/-- `X_h ∘ K` is differentiable at the points of the strip. -/
theorem differentiableAt_ham_comp (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) (hθ : θ ∈ complexStrip n r) :
    DifferentiableAt ℂ (fun y => hamiltonianVectorFieldℂ h (K y)) θ :=
  ((differentiableOn_ham hS).differentiableAt (hS.isOpen.mem_nhds (hK𝔅 θ hθ))).comp θ
    (hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ))

/-- The invariance error is differentiable at the points of the strip. -/
theorem differentiableAt_invarianceError (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) (hθ : θ ∈ complexStrip n r) :
    DifferentiableAt ℂ (invarianceError h K ω) θ :=
  (differentiableAt_ham_comp hS hK hK𝔅 hθ).sub (differentiableAt_fderiv_apply hK hθ _)

/-- The entries of `D L v`: column `j` is the derivative of the `j`-th column of `DK`. -/
theorem fderiv_tangentMat_apply (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hθ : θ ∈ complexStrip n r) (v : Fin n → ℂ) (s : Fin n ⊕ Fin n) (j : Fin n) :
    fderiv ℂ (tangentMat K) θ v s j =
      sumVec n (fderiv ℂ (fun y => fderiv ℂ K y (Pi.single j 1)) θ v) s := by
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  rw [← fderiv_matrix_apply hL s j v]
  have hfun : (fun y => tangentMat K y s j) =
      fun y => sumVec n (fderiv ℂ K y (Pi.single j 1)) s :=
    funext fun y => tangentMat_apply K y s j
  rw [hfun, fderiv_sumVec_coord (differentiableAt_fderiv_apply hK hθ _) s v]

/-- Step `step:p2:fi-dl`: `∂_ω ∂_{θ_j} K = ∂_{θ_j}(X_h ∘ K - E)`, by the symmetry of mixed partial
derivatives and `L ω = X_h ∘ K - E`. -/
theorem fderiv_tangent_column_omega (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hθ : θ ∈ complexStrip n r) (j : Fin n) :
    fderiv ℂ (fun y => fderiv ℂ K y (Pi.single j 1)) θ (fun l => (ω l : ℂ)) =
      fderiv ℂ (fun y => hamiltonianVectorFieldℂ h (K y) - invarianceError h K ω y) θ
        (Pi.single j 1) := by
  rw [fderiv_apply_comm_of_differentiableOn (isOpen_complexStrip n r) hK hθ]
  have hfun : (fun y => fderiv ℂ K y (fun l => (ω l : ℂ))) =
      fun y => hamiltonianVectorFieldℂ h (K y) - invarianceError h K ω y :=
    funext fun y => by simp [invarianceError]
  rw [hfun]

/-- Step `step:p2:fi-dl`, item (c): `∂_ω L = A L - DE`. -/
theorem fi_dL (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) (hθ : θ ∈ complexStrip n r) :
    fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) =
      linMat h K θ * tangentMat K θ - errDerivMat h K ω θ := by
  have hX := (differentiableOn_ham hS).differentiableAt (hS.isOpen.mem_nhds (hK𝔅 θ hθ))
  have hKd := hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hcomp : fderiv ℂ (fun y => hamiltonianVectorFieldℂ h (K y)) θ =
      (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ)).comp (fderiv ℂ K θ) :=
    (hX.hasFDerivAt.comp θ hKd.hasFDerivAt).fderiv
  ext s j
  have hA : sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ) (fderiv ℂ K θ (Pi.single j 1)))
      = linMat h K θ *ᵥ fun t => tangentMat K θ t j := by
    rw [linMat, ← sqMat_mulVec]
    congr 1
  rw [Matrix.sub_apply, fderiv_tangentMat_apply hK hθ, fderiv_tangent_column_omega (h := h) hK hθ j,
    fderiv_fun_sub (differentiableAt_ham_comp hS hK hK𝔅 hθ)
      (differentiableAt_invarianceError hS hK hK𝔅 hθ), hcomp, errDerivMat, colMat_apply]
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, map_sub,
    Pi.sub_apply, hA]
  rfl

/-- Step `step:p2:fi-domegak`, item (d): `∂_ω Ω_K = -(DE)ᵀ Ω₀ L - Lᵀ Ω₀ DE`. -/
theorem fi_dLagrange (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) (hθ : θ ∈ complexStrip n r) :
    fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) =
      -((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * tangentMat K θ) -
        (tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ := by
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hLt : DifferentiableAt ℂ (fun y => (tangentMat K y)ᵀ) θ := hL.matrix_transpose
  have hLtO : DifferentiableAt ℂ (fun y => (tangentMat K y)ᵀ * omegaZeroMatrix n) θ :=
    hLt.matrix_mul (differentiableAt_const _)
  have hfun : lagrangeMat K =
      fun y => ((tangentMat K y)ᵀ * omegaZeroMatrix n) * tangentMat K y := rfl
  have hA : (linMat h K θ)ᵀ * omegaZeroMatrix n + omegaZeroMatrix n * linMat h K θ = 0 :=
    (ham_symplectic hS (K θ) (hK𝔅 θ hθ)).2.2
  rw [hfun, fderiv_matrix_mul_apply hLtO hL, fderiv_matrix_mul_const_apply hLt,
    fderiv_matrix_transpose_apply, fi_dL hS hK hK𝔅 hθ]
  exact alg_dLagrange hA

end Derivatives

/-! ### Item (e): the reduced field -/

section Reduced

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ} {θ : Fin n → ℂ}

/-- Subtraction of matrices partitioned by columns. -/
theorem fromCols_sub_fromCols {m : Type*} (A₁ B₁ : Matrix m (Fin n) ℂ)
    (A₂ B₂ : Matrix m (Fin n) ℂ) :
    Matrix.fromCols A₁ A₂ - Matrix.fromCols B₁ B₂ = Matrix.fromCols (A₁ - B₁) (A₂ - B₂) := by
  ext i (j | j) <;> simp

/-- The frame `P = (L N)` is holomorphic on the strip. -/
theorem differentiableOn_frameMat (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (frameMat K) (complexStrip n r) := by
  have hL := differentiableOn_matrix_iff_entries.1 (differentiableOn_tangentMat hK)
  have hN := differentiableOn_matrix_iff_entries.1 (differentiableOn_normalMat hK hG)
  rw [differentiableOn_matrix_iff_entries]
  rintro i (j | j)
  · simpa only [frameMat, Matrix.fromCols_apply_inl] using hL i j
  · simpa only [frameMat, Matrix.fromCols_apply_inr] using hN i j

/-- The derivative of the frame is the frame of the derivatives: `∂ P = (∂ L  ∂ N)`. -/
theorem fderiv_frameMat (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (hθ : θ ∈ complexStrip n r)
    (v : Fin n → ℂ) :
    fderiv ℂ (frameMat K) θ v =
      Matrix.fromCols (fderiv ℂ (tangentMat K) θ v) (fderiv ℂ (normalMat K) θ v) := by
  have hnhds := (isOpen_complexStrip n r).mem_nhds hθ
  have hP : DifferentiableAt ℂ (frameMat K) θ :=
    (differentiableOn_frameMat hK hG).differentiableAt hnhds
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt hnhds
  have hN : DifferentiableAt ℂ (normalMat K) θ :=
    (differentiableOn_normalMat hK hG).differentiableAt hnhds
  ext i (j | j)
  · rw [Matrix.fromCols_apply_inl, ← fderiv_matrix_apply hP, ← fderiv_matrix_apply hL]
    congr 1
  · rw [Matrix.fromCols_apply_inr, ← fderiv_matrix_apply hP, ← fderiv_matrix_apply hN]
    congr 1

/-- Step `step:p2:fi-22`: differentiating the constant identity `Lᵀ Ω₀ N = -I` along `ω` gives
`(∂_ω L)ᵀ Ω₀ N + Lᵀ Ω₀ ∂_ω N = 0`. -/
theorem fi_dLtON (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (hθ : θ ∈ complexStrip n r)
    (v : Fin n → ℂ) :
    (fderiv ℂ (tangentMat K) θ v)ᵀ * omegaZeroMatrix n * normalMat K θ +
      (tangentMat K θ)ᵀ * omegaZeroMatrix n * fderiv ℂ (normalMat K) θ v = 0 := by
  have hnhds := (isOpen_complexStrip n r).mem_nhds hθ
  have hL : DifferentiableAt ℂ (tangentMat K) θ :=
    (differentiableOn_tangentMat hK).differentiableAt hnhds
  have hN : DifferentiableAt ℂ (normalMat K) θ :=
    (differentiableOn_normalMat hK hG).differentiableAt hnhds
  have hLt : DifferentiableAt ℂ (fun y => (tangentMat K y)ᵀ) θ := hL.matrix_transpose
  have hLtO : DifferentiableAt ℂ (fun y => (tangentMat K y)ᵀ * omegaZeroMatrix n) θ :=
    hLt.matrix_mul (differentiableAt_const _)
  have hconst : (fun y => (tangentMat K y)ᵀ * omegaZeroMatrix n * normalMat K y)
      =ᶠ[nhds θ] fun _ => (-1 : Matrix (Fin n) (Fin n) ℂ) := by
    filter_upwards [hnhds] with y hy
    exact fi_LtON K (hG y hy)
  have h0 : fderiv ℂ (fun y => (tangentMat K y)ᵀ * omegaZeroMatrix n * normalMat K y) θ v = 0 := by
    rw [hconst.fderiv_eq]
    simp
  rwa [fderiv_matrix_mul_apply hLtO hN, fderiv_matrix_mul_const_apply hLt,
    fderiv_matrix_transpose_apply] at h0

/-- Step `step:p2:fi-22`: `Lᵀ Ω₀ X_N = -(DE)ᵀ Ω₀ N`. -/
theorem fi_LtOXN (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (hθ : θ ∈ complexStrip n r) :
    (tangentMat K θ)ᵀ * omegaZeroMatrix n * normalFieldMat h K ω θ =
      -((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ) := by
  have hA : (linMat h K θ)ᵀ * omegaZeroMatrix n + omegaZeroMatrix n * linMat h K θ = 0 :=
    (ham_symplectic hS (K θ) (hK𝔅 θ hθ)).2.2
  have h0 := fi_dLtON hK hG hθ (fun l => (ω l : ℂ))
  rw [fi_dL hS hK hK𝔅 hθ] at h0
  exact alg_LtOXN hA h0

/-- Left multiplication of a block matrix by `Ω₀`: `Ω₀ (a b; c d) = (-c -d; a b)`. -/
theorem omega_mul_fromBlocks {p q : Type*} (a : Matrix (Fin n) p ℂ) (b : Matrix (Fin n) q ℂ)
    (c : Matrix (Fin n) p ℂ) (d : Matrix (Fin n) q ℂ) :
    omegaZeroMatrix n * Matrix.fromBlocks a b c d = Matrix.fromBlocks (-c) (-d) a b := by
  rw [omegaZeroMatrix, Matrix.fromBlocks_multiply]
  simp

/-- Step `step:p2:fi-blocks`: `Q (X_L  X_N) = ((NᵀΩ₀X_L, NᵀΩ₀X_N), (-LᵀΩ₀X_L, -LᵀΩ₀X_N))`. -/
theorem alg_reduced (L N XL XN : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) :
    -(omegaZeroMatrix n * (Matrix.fromCols L N)ᵀ * omegaZeroMatrix n) *
        Matrix.fromCols XL XN =
      Matrix.fromBlocks (Nᵀ * omegaZeroMatrix n * XL) (Nᵀ * omegaZeroMatrix n * XN)
        (-(Lᵀ * omegaZeroMatrix n * XL)) (-(Lᵀ * omegaZeroMatrix n * XN)) := by
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.fromCols L N)ᵀ,
    Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
    omega_mul_fromBlocks, Matrix.fromBlocks_neg]
  simp

/-- Steps `step:p2:fi-blocks` and `step:p2:fi-22`, item (e):
`Q (A P - ∂_ω P) = Λ + E_red`. -/
theorem fi_reduced (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (hθ : θ ∈ complexStrip n r) :
    reducer K θ * (linMat h K θ * frameMat K θ - fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))) =
      triangularMat (torsion h K ω θ) + redDefect h K ω θ := by
  have hN : DifferentiableAt ℂ (normalMat K) θ :=
    (differentiableOn_normalMat hK hG).differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hXP : linMat h K θ * frameMat K θ - fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ)) =
      Matrix.fromCols (errDerivMat h K ω θ) (normalFieldMat h K ω θ) := by
    rw [fderiv_frameMat hK hG hθ, frameMat, Matrix.mul_fromCols, fromCols_sub_fromCols,
      fi_dL hS hK hK𝔅 hθ, sub_sub_cancel, normalFieldMat]
  rw [hXP, reducer, frameMat, alg_reduced, torsion_eq_mat h K ω hN, fi_LtOXN hS hK hK𝔅 hG hθ,
    triangularMat, redDefect, Matrix.fromBlocks_add]
  simp

end Reduced

end KAM.Apost.Identities

namespace KAM.Apost

open KAM.Torus KAM.Apost.Identities

section Lemma

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- Blueprint `bp:p2:frame-identities`, items (a)–(f). -/
theorem frame_identities (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    ∀ θ ∈ complexStrip n r,
      ((tangentMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ = -1 ∧
        (normalMat K θ)ᵀ * omegaZeroMatrix n * tangentMat K θ = 1 ∧
        (normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ =
          (gramMatrix K θ)⁻¹ * lagrangeMat K θ * (gramMatrix K θ)⁻¹) ∧
      ((frameMat K θ)ᵀ * omegaZeroMatrix n * frameMat K θ = omegaZeroMatrix n + symDefect K θ ∧
        symDefect K θ = Matrix.fromBlocks (lagrangeMat K θ) 0 0
          ((gramMatrix K θ)⁻¹ * lagrangeMat K θ * (gramMatrix K θ)⁻¹)) ∧
      fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) =
        linMat h K θ * tangentMat K θ - errDerivMat h K ω θ ∧
      fderiv ℂ (lagrangeMat K) θ (fun l => (ω l : ℂ)) =
        -((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * tangentMat K θ) -
          (tangentMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ ∧
      reducer K θ * (linMat h K θ * frameMat K θ - fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))) =
        triangularMat (torsion h K ω θ) + redDefect h K ω θ ∧
      (reducer K θ * frameMat K θ = 1 - omegaZeroMatrix n * symDefect K θ ∧
        reducer K θ *ᵥ sumVec n (invarianceError h K ω θ) = -eta h K ω θ) := by
  -- `0 < r` is the strip-width convention; no item needs it.
  have _hr : 0 < r := hr
  intro θ hθ
  exact ⟨⟨fi_LtON K (hG θ hθ), fi_NtOL K (hG θ hθ), fi_NtON K⟩,
    ⟨fi_PtOP K, fi_symDefect K (hG θ hθ)⟩, fi_dL hS hK hK𝔅 hθ, fi_dLagrange hS hK hK𝔅 hθ,
    fi_reduced hS hK hK𝔅 hG hθ, fi_QP K, fi_QE h K ω⟩

end Lemma

end KAM.Apost

end
