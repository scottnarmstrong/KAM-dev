/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Apost.Identities
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Part 1 (isoenergetic linear step): the linearized equation in the frame

Blueprint node `bpI:p1:reduced`.

For a frame `P = (L N)` of a torus `K` with reducer `Q = -Ω₀ Pᵀ Ω₀`, a holomorphic
`ξ = (ξᴸ, ξᴺ)` and a scalar `ξ^ω`, the correction is `ΔK = P ξ`, `Δω = -ω ξ^ω`, and the residual of
the linearized equation is `Res = A ΔK - ∂_ω ΔK + L ω ξ^ω + E` (`isoResidual`). The theorem
`reduced` collects:

* (a) `Q L = (I; -Ω_K)`;
* (b) the unconditional identity `Q Res = Λξ - ∂_ωξ + (ω; 0) ξ^ω - η + E_lin` (`bordOp`,
  `isoLinError`);
* (c) `Q Res = E_lin` when the bordered system `bordOp = η` holds, and the bound on `E_lin`;
* (d) if the frame `P` is invertible, `Res = Q⁻¹ E_lin` and `Res = 0 ↔ bordOp = η - E_lin`.

It is built from the `KAM.Apost` `frame_identities`
helpers (`fi_NtOL`, `fi_reduced`, `fi_QP`, `fi_QE`)
and the product rule for `y ↦ A y *ᵥ u y` (`fderiv_matrix_mulVec_apply`); nothing is entrywise on
`2n × 2n` products. The `Setting` is the Diophantine standing data of those helpers (the
source text says `ω ∈ ℝⁿ`, every use is at a Diophantine `ω`).
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost KAM.Apost.Identities

variable {n : ℕ}

section Algebra

/-- `Ω₀ (a; b) = (-b; a)` for a matrix stacked from two `n`-row blocks. -/
theorem omegaZeroMatrix_mul_fromRows {q : Type*} [Fintype q] (a b : Matrix (Fin n) q ℂ) :
    omegaZeroMatrix n * Matrix.fromRows a b = Matrix.fromRows (-b) a := by
  ext (i | i) j
  · simp [omegaZeroMatrix_mul_apply_inl]
  · simp [omegaZeroMatrix_mul_apply_inr]

/-- Item (a): `Q L = (I_n; -Ω_K)`, from `Nᵀ Ω₀ L = I` (frame identities (a)). -/
theorem reducer_mul_tangentMat (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {θ : Fin n → ℂ}
    (hG : IsUnit (gramMatrix K θ).det) :
    reducer K θ * tangentMat K θ = Matrix.fromRows 1 (-lagrangeMat K θ) := by
  have hPL : (frameMat K θ)ᵀ * (omegaZeroMatrix n * tangentMat K θ) =
      Matrix.fromRows (lagrangeMat K θ) 1 := by
    rw [frameMat, Matrix.transpose_fromCols, Matrix.fromRows_mul]
    congr 1
    · simp only [lagrangeMat, Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc]
      exact fi_NtOL K hG
  have hQ : reducer K θ * tangentMat K θ =
      -(omegaZeroMatrix n * ((frameMat K θ)ᵀ * (omegaZeroMatrix n * tangentMat K θ))) := by
    simp only [reducer, Matrix.neg_mul, Matrix.mul_assoc]
  rw [hQ, hPL, omegaZeroMatrix_mul_fromRows, Matrix.fromRows_neg]
  simp

/-- `Q` is invertible when the frame `P` is. -/
theorem isUnit_det_reducer (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) {θ : Fin n → ℂ}
    (hP : IsUnit (frameMat K θ).det) : IsUnit (reducer K θ).det := by
  have hΩ : IsUnit (omegaZeroMatrix n) :=
    IsUnit.of_mul_eq_one (-omegaZeroMatrix n) (by
      rw [Matrix.mul_neg, omegaZeroMatrix_mul_self, neg_neg])
  have hPt : IsUnit (frameMat K θ)ᵀ :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by rwa [Matrix.det_transpose])
  exact (Matrix.isUnit_iff_isUnit_det _).1 (((hΩ.mul hPt).mul hΩ).neg)

end Algebra

section Pointwise

variable {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r r' : ℝ}
  {ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ} {ξω : ℂ} {θ : Fin n → ℂ}

/-- The residual in the form `(A P - ∂_ω P) ξ - P ∂_ωξ + ξ^ω (L ω) + E` (product rule). -/
theorem isoResidual_eq (hP : DifferentiableAt ℂ (frameMat K) θ)
    (hξ : DifferentiableAt ℂ ξ θ) :
    isoResidual H K ω ξ ξω θ =
      (linMat H K θ * frameMat K θ - fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))) *ᵥ ξ θ -
        frameMat K θ *ᵥ fderiv ℂ ξ θ (fun l => (ω l : ℂ)) +
      ξω • (tangentMat K θ *ᵥ fun l => (ω l : ℂ)) + sumVec n (invarianceError H K ω θ) := by
  rw [isoResidual, fderiv_matrix_mulVec_apply hP hξ, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
  abel

/-- Item (b), pointwise: `Q Res = Λξ - ∂_ωξ + (ω; 0) ξ^ω - η + E_lin`. -/
theorem reducer_mulVec_isoResidual (hS : Setting n τ M σK σB σT D H ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hθ : θ ∈ complexStrip n r) (hP : DifferentiableAt ℂ (frameMat K) θ)
    (hξ : DifferentiableAt ℂ ξ θ) :
    reducer K θ *ᵥ isoResidual H K ω ξ ξω θ =
      bordOp H K ω ξ ξω θ - eta H K ω θ + isoLinError H K ω ξ ξω θ := by
  have hred := fi_reduced hS.toStanding hK hKD hG hθ
  have hQL := reducer_mul_tangentMat K (hG θ hθ)
  have hQP := fi_QP (K := K) (θ := θ)
  have hQE := fi_QE H K ω (θ := θ)
  set d := fderiv ℂ ξ θ (fun l => (ω l : ℂ)) with hd
  set ωc : Fin n → ℂ := fun l => (ω l : ℂ) with hωc
  have hQLω : reducer K θ *ᵥ (tangentMat K θ *ᵥ ωc) =
      Sum.elim ωc (0 : Fin n → ℂ) - Sum.elim (0 : Fin n → ℂ) (lagrangeMat K θ *ᵥ ωc) := by
    rw [Matrix.mulVec_mulVec, hQL, Matrix.fromRows_mulVec, Matrix.one_mulVec,
      Matrix.neg_mulVec]
    ext (i | i) <;> simp
  rw [isoResidual_eq hP hξ, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hred, hQP, hQLω, hQE,
    bordOp, isoLinError, triangularMat, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    smul_sub]
  module

/-- Item (c), the bound on the linearization error `E_lin` (no hypothesis is needed). -/
theorem norm_isoLinError_le (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ)
    (ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ) (ξω : ℂ) (θ : Fin n → ℂ) :
    ‖isoLinError H K ω ξ ξω θ‖ ≤ ‖redDefect H K ω θ‖ * ‖ξ θ‖ +
      ‖symDefect K θ‖ * ‖fderiv ℂ ξ θ (fun l => (ω l : ℂ))‖ +
        ‖lagrangeMat K θ‖ * ‖ω‖ * ‖ξω‖ := by
  have h1 : ‖redDefect H K ω θ *ᵥ ξ θ‖ ≤ ‖redDefect H K ω θ‖ * ‖ξ θ‖ :=
    Matrix.linfty_opNorm_mulVec _ _
  have h2 : ‖(omegaZeroMatrix n * symDefect K θ) *ᵥ fderiv ℂ ξ θ (fun l => (ω l : ℂ))‖ ≤
      ‖symDefect K θ‖ * ‖fderiv ℂ ξ θ (fun l => (ω l : ℂ))‖ :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (by rw [norm_omegaZeroMatrix_mul])
  have hωc : ‖fun l => (ω l : ℂ)‖ ≤ ‖ω‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => by
      simpa using norm_le_pi_norm ω l
  have hv : ‖Sum.elim (0 : Fin n → ℂ) (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ))‖ ≤
      ‖lagrangeMat K θ‖ * ‖ω‖ :=
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => by
      rcases i with i | i
      · simp
      · exact norm_le_pi_norm (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ)) i :
        ‖Sum.elim (0 : Fin n → ℂ) (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ))‖ ≤
          ‖lagrangeMat K θ *ᵥ fun l => (ω l : ℂ)‖).trans
      ((Matrix.linfty_opNorm_mulVec _ _).trans
        (mul_le_mul_of_nonneg_left hωc (norm_nonneg _)))
  have h3 : ‖ξω • Sum.elim (0 : Fin n → ℂ) (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ))‖ ≤
      ‖lagrangeMat K θ‖ * ‖ω‖ * ‖ξω‖ := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right hv (norm_nonneg _)
  calc ‖isoLinError H K ω ξ ξω θ‖
      ≤ ‖redDefect H K ω θ *ᵥ ξ θ +
          (omegaZeroMatrix n * symDefect K θ) *ᵥ fderiv ℂ ξ θ (fun l => (ω l : ℂ))‖ +
        ‖ξω • Sum.elim (0 : Fin n → ℂ) (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ))‖ :=
        norm_sub_le _ _
    _ ≤ ‖redDefect H K ω θ *ᵥ ξ θ‖ +
          ‖(omegaZeroMatrix n * symDefect K θ) *ᵥ fderiv ℂ ξ θ (fun l => (ω l : ℂ))‖ +
        ‖ξω • Sum.elim (0 : Fin n → ℂ) (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ))‖ :=
        add_le_add_left (norm_add_le _ _) _
    _ ≤ _ := by linarith

/-- Item (d), pointwise: if `Q` is invertible, `Res = Q⁻¹ (Q Res)`. -/
theorem isoResidual_eq_inv_mulVec (hQ : IsUnit (reducer K θ).det) :
    isoResidual H K ω ξ ξω θ =
      (reducer K θ)⁻¹ *ᵥ (reducer K θ *ᵥ isoResidual H K ω ξ ξω θ) := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hQ, Matrix.one_mulVec]

end Pointwise

section Frame

variable {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}

/-- `bpI:p1:reduced` (a)–(d). -/
theorem reduced (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {r' : ℝ} (hr' : 0 < r')
    (hr'r : r' ≤ r) {ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ}
    (hξ : DifferentiableOn ℂ ξ (complexStrip n r')) (ξω : ℂ) :
    (∀ θ ∈ complexStrip n r', reducer K θ * tangentMat K θ = Matrix.fromRows 1 (-lagrangeMat K θ)) ∧
    (∀ θ ∈ complexStrip n r', reducer K θ *ᵥ isoResidual H K ω ξ ξω θ =
      bordOp H K ω ξ ξω θ - eta H K ω θ + isoLinError H K ω ξ ξω θ) ∧
    (∀ θ ∈ complexStrip n r', bordOp H K ω ξ ξω θ = eta H K ω θ →
      reducer K θ *ᵥ isoResidual H K ω ξ ξω θ = isoLinError H K ω ξ ξω θ) ∧
    (∀ θ ∈ complexStrip n r', ‖isoLinError H K ω ξ ξω θ‖ ≤ ‖redDefect H K ω θ‖ * ‖ξ θ‖ +
      ‖symDefect K θ‖ * ‖fderiv ℂ ξ θ (fun l => (ω l : ℂ))‖ + ‖lagrangeMat K θ‖ * ‖ω‖ * ‖ξω‖) ∧
    ((∀ θ ∈ complexStrip n r', IsUnit (frameMat K θ).det) → ∀ θ ∈ complexStrip n r',
      (bordOp H K ω ξ ξω θ = eta H K ω θ →
        isoResidual H K ω ξ ξω θ = (reducer K θ)⁻¹ *ᵥ isoLinError H K ω ξ ξω θ) ∧
      (isoResidual H K ω ξ ξω θ = 0 ↔
        bordOp H K ω ξ ξω θ = eta H K ω θ - isoLinError H K ω ξ ξω θ)) := by
  have _hr : 0 < r := hr
  have _hr' : 0 < r' := hr'
  have hsub : ∀ θ ∈ complexStrip n r', θ ∈ complexStrip n r := fun θ hθ i =>
    (hθ i).trans_le hr'r
  have hPd : ∀ θ ∈ complexStrip n r', DifferentiableAt ℂ (frameMat K) θ := fun θ hθ =>
    (Identities.differentiableOn_frameMat hK hG).differentiableAt
      ((isOpen_complexStrip n r).mem_nhds (hsub θ hθ))
  have hξd : ∀ θ ∈ complexStrip n r', DifferentiableAt ℂ ξ θ := fun θ hθ =>
    hξ.differentiableAt ((isOpen_complexStrip n r').mem_nhds hθ)
  have hb : ∀ θ ∈ complexStrip n r', reducer K θ *ᵥ isoResidual H K ω ξ ξω θ =
      bordOp H K ω ξ ξω θ - eta H K ω θ + isoLinError H K ω ξ ξω θ := fun θ hθ =>
    reducer_mulVec_isoResidual hS hK hKD hG (hsub θ hθ) (hPd θ hθ) (hξd θ hθ)
  have hc : ∀ θ ∈ complexStrip n r', bordOp H K ω ξ ξω θ = eta H K ω θ →
      reducer K θ *ᵥ isoResidual H K ω ξ ξω θ = isoLinError H K ω ξ ξω θ := fun θ hθ h =>
    by rw [hb θ hθ, h, sub_self, zero_add]
  refine ⟨fun θ hθ => reducer_mul_tangentMat K (hG θ (hsub θ hθ)), hb, hc,
    fun θ _ => norm_isoLinError_le H K ω ξ ξω θ, fun hP θ hθ => ?_⟩
  have hQ := isUnit_det_reducer K (hP θ hθ)
  refine ⟨fun h => ?_, ?_⟩
  · rw [isoResidual_eq_inv_mulVec hQ, hc θ hθ h]
  · constructor
    · intro h0
      have h1 := hb θ hθ
      rw [h0, Matrix.mulVec_zero] at h1
      have h2 : bordOp H K ω ξ ξω θ = (bordOp H K ω ξ ξω θ - eta H K ω θ +
          isoLinError H K ω ξ ξω θ) + (eta H K ω θ - isoLinError H K ω ξ ξω θ) := by abel
      rw [h2, ← h1, zero_add]
    · intro h0
      rw [isoResidual_eq_inv_mulVec hQ, hb θ hθ, h0]
      simp

end Frame

end KAM.Iso.Linear

end
