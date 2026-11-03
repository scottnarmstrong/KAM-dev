/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChart.Inverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The Jacobian matrix of the base map and its inverse transpose (track B, B5-CHART)

`torusChartJac u φ` is the matrix of `Dx φ` in the standard basis, `torusChartInvT u φ` its
inverse transpose `(Dx φ)^{-T}`. Entries of the inverse transpose are as smooth as those of the
Jacobian (Cramer's rule: the determinant and the adjugate are polynomial in the entries).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Matrix

variable {n : ℕ}

/-- The matrix `(Dx φ)_{ij} = (Dx φ e_j)_i` of the derivative of the base map. -/
def torusChartJac (u : (Fin n → ℝ) → (Fin n → ℝ)) (φ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ (torusChartX u) φ (Pi.single j 1) i

/-- The inverse transpose `(Dx φ)^{-T}`. -/
def torusChartInvT (u : (Fin n → ℝ) → (Fin n → ℝ)) (φ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (torusChartJac u φ)ᵀ⁻¹

/-- A continuous linear map of `Fin n → ℝ` acts by its matrix. -/
theorem clm_apply_eq_mulVec (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (y : Fin n → ℝ) :
    L y = (Matrix.of fun i j => L (Pi.single j 1) i) *ᵥ y := by
  have hy : y = ∑ j, y j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  funext i
  conv_lhs => rw [hy]
  simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]

theorem torusChartJac_mulVec (u : (Fin n → ℝ) → (Fin n → ℝ)) (φ y : Fin n → ℝ) :
    torusChartJac u φ *ᵥ y = fderiv ℝ (torusChartX u) φ y :=
  (clm_apply_eq_mulVec _ y).symm

variable {u : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}

theorem torusChartJac_det_ne (h : TorusBaseData u κ) (φ : Fin n → ℝ) :
    (torusChartJac u φ).det ≠ 0 := by
  intro hd
  obtain ⟨y, hy, hy0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  rw [torusChartJac_mulVec] at hy0
  have := torusChartDx_lower h φ y
  rw [hy0, norm_zero] at this
  have h1 : 0 < 1 - κ := by linarith [h.baseContract]
  exact hy (norm_le_zero_iff.mp (by nlinarith [norm_nonneg y]))

theorem torusChartJac_isUnit (h : TorusBaseData u κ) (φ : Fin n → ℝ) :
    IsUnit (torusChartJac u φ).det := (torusChartJac_det_ne h φ).isUnit

theorem torusChartInvT_det_isUnit (h : TorusBaseData u κ) (φ : Fin n → ℝ) :
    IsUnit (torusChartJac u φ)ᵀ.det := by
  rw [det_transpose]; exact torusChartJac_isUnit h φ

/-- `(Dx)^{-T}` transposed times `Dx` is the identity, in entries. -/
theorem torusChartInvT_entry (h : TorusBaseData u κ) (φ : Fin n → ℝ) (k l : Fin n) :
    ∑ i, torusChartInvT u φ i k * torusChartJac u φ i l = if k = l then 1 else 0 := by
  have hm : (torusChartInvT u φ)ᵀ * torusChartJac u φ = 1 := by
    unfold torusChartInvT
    rw [← transpose_nonsing_inv, transpose_transpose]
    exact nonsing_inv_mul _ (torusChartJac_isUnit h φ)
  have := congrFun (congrFun hm k) l
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

/-- `Dx · (Dx)^{-1}` : `Dxᵀ (Dx)^{-T} J = J`. -/
theorem torusChartJacT_invT_mulVec (h : TorusBaseData u κ) (φ J : Fin n → ℝ) :
    (torusChartJac u φ)ᵀ *ᵥ (torusChartInvT u φ *ᵥ J) = J := by
  rw [Matrix.mulVec_mulVec]
  unfold torusChartInvT
  rw [Matrix.mul_nonsing_inv _ (torusChartInvT_det_isUnit h φ), Matrix.one_mulVec]

theorem torusChartInvT_jacT_mulVec (h : TorusBaseData u κ) (φ p : Fin n → ℝ) :
    torusChartInvT u φ *ᵥ ((torusChartJac u φ)ᵀ *ᵥ p) = p := by
  rw [Matrix.mulVec_mulVec]
  unfold torusChartInvT
  rw [Matrix.nonsing_inv_mul _ (torusChartInvT_det_isUnit h φ), Matrix.one_mulVec]

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : WithTop ℕ∞}

theorem contDiff_matrix_det {f : E → Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ i j, ContDiff ℝ m fun x => f x i j) : ContDiff ℝ m fun x => (f x).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => hf _ _

theorem contDiff_matrix_inv_entry {f : E → Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ i j, ContDiff ℝ m fun x => f x i j) (hd : ∀ x, (f x).det ≠ 0) (i j : Fin n) :
    ContDiff ℝ m fun x => (f x)⁻¹ i j := by
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    Matrix.adjugate_apply]
  refine (contDiff_matrix_det hf).inv hd |>.mul ?_
  refine contDiff_matrix_det fun a b => ?_
  simp only [Matrix.updateRow_apply]
  by_cases hab : a = j
  · simp only [hab, ite_true]
    exact contDiff_const
  · simp only [hab, ite_false]
    exact hf a b

end Smooth

theorem torusChartJac_contDiff (h : TorusBaseData u κ) (i j : Fin n) :
    ContDiff ℝ 2 fun φ => torusChartJac u φ i j := by
  have hd : ContDiff ℝ 2 (fderiv ℝ (torusChartX u)) :=
    (torusChartX_contDiff h).fderiv_right (m := 2) (by norm_num)
  exact ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single j 1))).contDiff.comp hd

theorem torusChartInvT_contDiff (h : TorusBaseData u κ) (i j : Fin n) :
    ContDiff ℝ 2 fun φ => torusChartInvT u φ i j := by
  unfold torusChartInvT
  refine contDiff_matrix_inv_entry (f := fun φ => (torusChartJac u φ)ᵀ)
    (fun a b => torusChartJac_contDiff h b a) (fun φ => ?_) i j
  rw [det_transpose]; exact torusChartJac_det_ne h φ

end KAM.EffectiveStability
