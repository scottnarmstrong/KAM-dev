/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.FullRange
public import KAM.Iso.Linear.Reduced
public import KAM.Iso.Linear.NoTwist

/-!
# Part 1 (isoenergetic linear step): the literal any-`ω` readings (package GAP-I1c)

The source states `bpI:p1:reduced` for `ω ∈ ℝⁿ` (any) and `bpI:p1:perturbation-noA5` for
`ω ∈ ℝⁿ`, `‖ω‖ ≤ Θ`, with no Diophantine condition on `ω`; the landed `reduced` and
`perturbation_noA5` take `ω` from a `Setting` (design departure D3). Here the standing data is a
`Setting` at a frequency `ω₀` (the setting's own frequency, used only for the `ω`-free
Hamiltonian facts: holomorphy, symplecticity and the Taylor bound of `X_H`), and the frequency
`ω` of the statement is arbitrary.

* `reduced_anyOmega` : literal `bpI:p1:reduced` (a)–(d) at an arbitrary `ω`.
* `perturbation_noA5_anyOmega` : literal `bpI:p1:perturbation-noA5` (a)–(e) at an arbitrary `ω`.

Nothing here replaces the landed statements; each `_anyOmega` proof is the landed proof with
the `ω`-free uses of the standing data supplied by `ω₀`.
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Linear.AnyOmega

open KAM KAM.Torus KAM.Apost KAM.Apost.Identities KAM.Iso.Linear

variable {n : ℕ} {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω₀ ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ} {θ : Fin n → ℂ}

section Reduced

/-- `bpI:p1:reduced`, step `fi-dl` at an arbitrary `ω`: `∂_ω L = A L - DE`. -/
theorem fi_dL_anyOmega (hS : Standing n τ M σK σB σT D H ω₀ γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) (hθ : θ ∈ complexStrip n r) :
    fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) =
      linMat H K θ * tangentMat K θ - errDerivMat H K ω θ := by
  have hX := (differentiableOn_ham hS).differentiableAt (hS.isOpen.mem_nhds (hKD θ hθ))
  have hKd := hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hcomp : fderiv ℂ (fun y => hamiltonianVectorFieldℂ H (K y)) θ =
      (fderiv ℂ (hamiltonianVectorFieldℂ H) (K θ)).comp (fderiv ℂ K θ) :=
    (hX.hasFDerivAt.comp θ hKd.hasFDerivAt).fderiv
  have hinv : DifferentiableAt ℂ (invarianceError H K ω) θ :=
    (differentiableAt_ham_comp hS hK hKD hθ).sub (differentiableAt_fderiv_apply hK hθ _)
  ext s j
  have hA : sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ H) (K θ)
      (fderiv ℂ K θ (Pi.single j 1))) = linMat H K θ *ᵥ fun t => tangentMat K θ t j := by
    rw [linMat, ← sqMat_mulVec]
    congr 1
  rw [Matrix.sub_apply, fderiv_tangentMat_apply hK hθ,
    fderiv_tangent_column_omega (h := H) hK hθ j,
    fderiv_fun_sub (differentiableAt_ham_comp hS hK hKD hθ) hinv, hcomp, errDerivMat,
    colMat_apply]
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, map_sub,
    Pi.sub_apply, hA]
  rfl

/-- Steps `fi-22` at an arbitrary `ω`: `Lᵀ Ω₀ X_N = -(DE)ᵀ Ω₀ N`. -/
theorem fi_LtOXN_anyOmega (hS : Standing n τ M σK σB σT D H ω₀ γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (hθ : θ ∈ complexStrip n r) :
    (tangentMat K θ)ᵀ * omegaZeroMatrix n * normalFieldMat H K ω θ =
      -((errDerivMat H K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ) := by
  have hA : (linMat H K θ)ᵀ * omegaZeroMatrix n + omegaZeroMatrix n * linMat H K θ = 0 :=
    (ham_symplectic hS (K θ) (hKD θ hθ)).2.2
  have h0 := fi_dLtON hK hG hθ (fun l => (ω l : ℂ))
  rw [fi_dL_anyOmega (ω := ω) hS hK hKD hθ] at h0
  exact alg_LtOXN hA h0

/-- Step `fi-blocks`, item (e), at an arbitrary `ω`: `Q (A P - ∂_ω P) = Λ + E_red`. -/
theorem fi_reduced_anyOmega (hS : Standing n τ M σK σB σT D H ω₀ γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (hθ : θ ∈ complexStrip n r) :
    reducer K θ * (linMat H K θ * frameMat K θ - fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))) =
      triangularMat (torsion H K ω θ) + redDefect H K ω θ := by
  have hN : DifferentiableAt ℂ (normalMat K) θ :=
    (differentiableOn_normalMat hK hG).differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hXP : linMat H K θ * frameMat K θ - fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ)) =
      Matrix.fromCols (errDerivMat H K ω θ) (normalFieldMat H K ω θ) := by
    rw [fderiv_frameMat hK hG hθ, frameMat, Matrix.mul_fromCols, fromCols_sub_fromCols,
      fi_dL_anyOmega (ω := ω) hS hK hKD hθ, sub_sub_cancel, normalFieldMat]
  rw [hXP, reducer, frameMat, alg_reduced, torsion_eq_mat H K ω hN,
    fi_LtOXN_anyOmega (ω := ω) hS hK hKD hG hθ, triangularMat, redDefect,
    Matrix.fromBlocks_add]
  simp

/-- Item (b), pointwise, at an arbitrary `ω`: `Q Res = Λξ - ∂_ωξ + (ω; 0) ξ^ω - η + E_lin`. -/
theorem reducer_mulVec_isoResidual_anyOmega (hS : Standing n τ M σK σB σT D H ω₀ γ)
    {ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ} {ξω : ℂ}
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hθ : θ ∈ complexStrip n r) (hP : DifferentiableAt ℂ (frameMat K) θ)
    (hξ : DifferentiableAt ℂ ξ θ) :
    reducer K θ *ᵥ isoResidual H K ω ξ ξω θ =
      bordOp H K ω ξ ξω θ - eta H K ω θ + isoLinError H K ω ξ ξω θ := by
  have hred := fi_reduced_anyOmega (ω := ω) hS hK hKD hG hθ
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

/-- `bpI:p1:reduced` (a)–(d) for an arbitrary frequency `ω ∈ ℝⁿ`, as in the source: the setting
data is a `Setting` at its own frequency `ω₀`, and `ω` carries no Diophantine condition. -/
theorem reduced_anyOmega (hS : Setting n τ M σK σB σT D H ω₀ γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (ω : Fin n → ℝ) {r' : ℝ}
    (hr' : 0 < r') (hr'r : r' ≤ r) {ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ}
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
    reducer_mulVec_isoResidual_anyOmega hS.toStanding hK hKD hG (hsub θ hθ) (hPd θ hθ)
      (hξd θ hθ)
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

end Reduced

section Perturbation

variable {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {δ β d : ℝ}

/-- `X̃_Ñ - X_N` on `T_{r-2δ}` at an arbitrary `ω` (`step:p2:pt-xn`). -/
theorem norm_normalField_sub_le_strip_anyOmega (hS : Standing n τ M σK σB σT D H ω₀ γ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd0 : 0 ≤ d) (hω : ‖ω‖ ≤ Theta n M σK σB σT)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hK' : DifferentiableOn ℂ K' (complexStrip n r))
    (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d) (hdβ : d < β)
    (hG' : ∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det)
    (hNN : ∀ θ ∈ complexStrip n (r - δ),
      ‖normalMat K' θ - normalMat K θ‖ ≤ C_DN n M σK σB σT * d / δ ∧
        ‖normalMat K' θ‖ ≤ 2 * mSize M σK σB σT ^ 2)
    (hAb : ∀ θ ∈ complexStrip n r, ‖linMat H K θ‖ ≤ mSize M σK σB σT) :
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖normalFieldMat H K' ω θ - normalFieldMat H K ω θ‖ ≤
        C_DX n M σK σB σT * d / δ ^ 2 := by
  have hsub : complexStrip n (r - δ) ⊆ complexStrip n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hN'd : DifferentiableOn ℂ (normalMat K') (complexStrip n (r - δ)) :=
    differentiableOn_normalMat (hK'.mono hsub) hG'
  have hNd : DifferentiableOn ℂ (normalMat K) (complexStrip n (r - δ)) :=
    differentiableOn_normalMat (hK.mono hsub) fun θ hθ => hG θ (hsub hθ)
  have hDω := PerturbationAux.norm_fderiv_normalDiff_le (K := K) (K' := K') (hN'd.sub hNd)
    (fun θ hθ => (hNN θ hθ).1) hδ hω
  intro θ hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hopen := (isOpen_complexStrip n (r - δ)).mem_nhds hθ1
  exact PerturbationAux.norm_normalField_sub_le hS.toParams hδ hδ1 hd0
    (hN'd.differentiableAt hopen) (hNd.differentiableAt hopen)
    (PerturbationAux.norm_linMat_sub_le hS (hball θ (hsub hθ1)) (hd θ (hsub hθ1)) hdβ)
    (hAb θ (hsub hθ1)) (hNN θ hθ1).2 (hNN θ hθ1).1 (hDω θ hθ) rfl

/-- `|T̃ - T| ≤ C_ΔT d/δ²` on `T_{r-2δ}` at an arbitrary `ω` (`step:p2:pt-torsion`). -/
theorem norm_torsion_sub_le_anyOmega (hS : Standing n τ M σK σB σT D H ω₀ γ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hω : ‖ω‖ ≤ Theta n M σK σB σT)
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hDK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hK' : DifferentiableOn ℂ K' (complexStrip n r))
    (hG' : ∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det)
    (hNN : ∀ θ ∈ complexStrip n (r - δ),
      ‖normalMat K' θ - normalMat K θ‖ ≤ C_DN n M σK σB σT * d / δ ∧
        ‖normalMat K' θ‖ ≤ 2 * mSize M σK σB σT ^ 2)
    (hXX : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖normalFieldMat H K' ω θ - normalFieldMat H K ω θ‖ ≤ C_DX n M σK σB σT * d / δ ^ 2) :
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖torsion H K' ω θ - torsion H K ω θ‖ ≤ C_DT n M σK σB σT * d / δ ^ 2 := by
  have hsub : complexStrip n (r - δ) ⊆ complexStrip n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hNd : DifferentiableOn ℂ (normalMat K) (complexStrip n r) :=
    differentiableOn_normalMat hK fun θ hθ => (hG θ hθ).1
  have hN'd : DifferentiableOn ℂ (normalMat K') (complexStrip n (r - δ)) :=
    differentiableOn_normalMat (hK'.mono hsub) hG'
  have hNb : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ mSize M σK σB σT ^ 2 := fun θ hθ =>
    FrameAux.norm_normalMat_le (hDK θ hθ) (hG θ hθ).2
  have hAb : ∀ θ ∈ complexStrip n r, ‖linMat H K θ‖ ≤ mSize M σK σB σT := fun θ hθ =>
    FrameAux.norm_linMat_le hS (hKD θ hθ)
  intro θ hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hθr : θ ∈ complexStrip n r := hsub hθ1
  have hX := FrameAux.norm_normalFieldMat_le (h := H) (ω := ω) hS.toParams hNd hNb hAb hω hδ
    hδ1 hθ1
  rw [torsion_eq_mat H K' ω (hN'd.differentiableAt ((isOpen_complexStrip n (r - δ)).mem_nhds hθ1)),
    torsion_eq_mat H K ω (hNd.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr))]
  have hNT : ‖(normalMat K' θ)ᵀ‖ ≤ 2 * n * (2 * mSize M σK σB σT ^ 2) :=
    (FrameAux.norm_transpose_le_two_mul _).trans
      (mul_le_mul_of_nonneg_left (hNN θ hθ1).2 (by positivity))
  have hNNT : ‖(normalMat K' θ - normalMat K θ)ᵀ‖ ≤ 2 * n * (C_DN n M σK σB σT * d / δ) :=
    (FrameAux.norm_transpose_le_two_mul _).trans
      (mul_le_mul_of_nonneg_left (hNN θ hθ1).1 (by positivity))
  refine (PerturbationAux.norm_torsion_combo_le _ _ _ _ hNT (hXX θ hθ) hNNT hX).trans
    (le_of_eq ?_)
  have hδ0 : δ ≠ 0 := hδ.ne'
  unfold C_DT
  field_simp
  ring

/-- `bpI:p1:perturbation-noA5` (a)–(e) for an arbitrary frequency `ω ∈ ℝⁿ` with `‖ω‖ ≤ Θ`, as
in the source: the setting data is a `Setting` at its own frequency `ω₀`, and `ω` carries no
Diophantine condition. -/
theorem perturbation_noA5_anyOmega (hS : Setting n τ M σK σB σT D H ω₀ γ) {r δ β d : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) (ω : Fin n → ℝ)
    (hω : ‖ω‖ ≤ Theta n M σK σB σT)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D)
    (hDK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hK' : DifferentiableOn ℂ K' (complexStrip n r)) (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d)
    (hdβ : d < β) (hsmall : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1) :
    (∀ θ ∈ complexStrip n r, Metric.ball (K' θ) (β - d) ⊆ D ∧
      ‖linMat H K' θ - linMat H K θ‖ ≤ mSize M σK σB σT * d) ∧
    (∀ θ ∈ complexStrip n (r - δ), ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ n * d / δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det ∧
      ‖(gramMatrix K' θ)⁻¹‖ ≤ 2 * mSize M σK σB σT ∧
      ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ C_B n M σK σB σT * d / δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), ‖normalMat K' θ - normalMat K θ‖ ≤ C_DN n M σK σB σT * d / δ ∧
      ‖normalMat K' θ‖ ≤ 2 * mSize M σK σB σT ^ 2 ∧
      ‖(normalMat K' θ)ᵀ‖ ≤ 4 * n * mSize M σK σB σT ^ 2) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖torsion H K' ω θ - torsion H K ω θ‖ ≤ C_DT n M σK σB σT * d / δ ^ 2) := by
  have _h2δ : 2 * δ < r := h2δ
  have hSt := hS.toStanding
  have hP := hSt.toParams
  have h0 : (0 : Fin n → ℂ) ∈ complexStrip n r := fun i => by simpa using hr
  have hd0 : 0 ≤ d := (norm_nonneg _).trans (hd 0 h0)
  have hβ : 0 < β := lt_of_le_of_lt hd0 hdβ
  have hsub : complexStrip n (r - δ) ⊆ complexStrip n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  have ha : ∀ θ ∈ complexStrip n r, Metric.ball (K' θ) (β - d) ⊆ D := fun θ hθ =>
    PerturbationAux.ball_subset_of_close (hball θ hθ) (hd θ hθ)
  obtain ⟨hb, hc, hdN⟩ := PerturbationAux.frame_items hP hδ hδ1 hd0 hK hDK hG hK' hd hsmall
  have hG' : ∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det :=
    fun θ hθ => (hc θ hθ).1
  have hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ => hball θ hθ (Metric.mem_ball_self hβ)
  have hAb : ∀ θ ∈ complexStrip n r, ‖linMat H K θ‖ ≤ mSize M σK σB σT := fun θ hθ =>
    FrameAux.norm_linMat_le hSt (hKD θ hθ)
  have hXX := norm_normalField_sub_le_strip_anyOmega (ω := ω) hSt hδ hδ1 hd0 hω hK hball
    (fun θ hθ => (hG θ hθ).1) hK' hd hdβ hG' hdN hAb
  have he := norm_torsion_sub_le_anyOmega (ω := ω) hSt hδ hδ1 hω hK hKD hDK hG hK' hG' hdN hXX
  refine ⟨fun θ hθ => ⟨ha θ hθ, PerturbationAux.norm_linMat_sub_le hSt (hball θ hθ) (hd θ hθ) hdβ⟩,
    hb, hc, fun θ hθ => ⟨(hdN θ hθ).1, (hdN θ hθ).2, ?_⟩, he⟩
  calc ‖(normalMat K' θ)ᵀ‖ ≤ 2 * n * ‖normalMat K' θ‖ := FrameAux.norm_transpose_le_two_mul _
    _ ≤ 2 * n * (2 * mSize M σK σB σT ^ 2) := by
        gcongr
        exact (hdN θ hθ).2
    _ = 4 * n * mSize M σK σB σT ^ 2 := by ring

end Perturbation

section Src

/-- `bpI:p1:reduced` (a)–(d) at an arbitrary `ω`, under the literal source setting `τ ≥ 0`
(`SettingSrc` at the source's own frequency `ω₀`, GAP-I1a ruling N1 option (i)). -/
theorem reduced_anyOmega_src (hS : SettingSrc n τ M D H ω₀ γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (ω : Fin n → ℝ) {r' : ℝ}
    (hr' : 0 < r') (hr'r : r' ≤ r) {ξ : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ}
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
        bordOp H K ω ξ ξω θ = eta H K ω θ - isoLinError H K ω ξ ξω θ)) :=
  reduced_anyOmega (hS.setting one_pos one_pos one_pos) hr hK hKD hG ω hr' hr'r hξ ξω

/-- `bpI:p1:perturbation-noA5` (a)–(e) at an arbitrary `ω` with `‖ω‖ ≤ Θ`, under the literal
source setting `τ ≥ 0` (`SettingSrc` at the source's own frequency `ω₀`), with free
`σK σB σT` (they enter the constants only through `𝔪`, unchanged by `σ ↦ max σ 1`). -/
theorem perturbation_noA5_anyOmega_src (hS : SettingSrc n τ M D H ω₀ γ) {r δ β d : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) (ω : Fin n → ℝ)
    {σK σB σT : ℝ} (hω : ‖ω‖ ≤ Theta n M σK σB σT)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ D)
    (hDK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB)
    (hK' : DifferentiableOn ℂ K' (complexStrip n r)) (hd : ∀ θ ∈ complexStrip n r, ‖K' θ - K θ‖ ≤ d)
    (hdβ : d < β) (hsmall : 2 * mSize M σK σB σT * C_DT n M σK σB σT * d / δ ^ 2 ≤ 1) :
    (∀ θ ∈ complexStrip n r, Metric.ball (K' θ) (β - d) ⊆ D ∧
      ‖linMat H K' θ - linMat H K θ‖ ≤ mSize M σK σB σT * d) ∧
    (∀ θ ∈ complexStrip n (r - δ), ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ n * d / δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), IsUnit (gramMatrix K' θ).det ∧
      ‖(gramMatrix K' θ)⁻¹‖ ≤ 2 * mSize M σK σB σT ∧
      ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ C_B n M σK σB σT * d / δ) ∧
    (∀ θ ∈ complexStrip n (r - δ), ‖normalMat K' θ - normalMat K θ‖ ≤ C_DN n M σK σB σT * d / δ ∧
      ‖normalMat K' θ‖ ≤ 2 * mSize M σK σB σT ^ 2 ∧
      ‖(normalMat K' θ)ᵀ‖ ≤ 4 * n * mSize M σK σB σT ^ 2) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖torsion H K' ω θ - torsion H K ω θ‖ ≤ C_DT n M σK σB σT * d / δ ^ 2) := by
  have hω' : ‖ω‖ ≤ Theta n M (max σK 1) (max σB 1) (max σT 1) := by
    simpa only [Theta, mSize_max_one] using hω
  have hsmall' : 2 * mSize M (max σK 1) (max σB 1) (max σT 1) *
      C_DT n M (max σK 1) (max σB 1) (max σT 1) * d / δ ^ 2 ≤ 1 := by
    simpa only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] using hsmall
  have h := perturbation_noA5_anyOmega (hS.setting (σK := max σK 1) (σB := max σB 1)
    (σT := max σT 1) (by positivity) (by positivity) (by positivity)) hr hδ hδ1 h2δ ω hω' hK
    hball (fun θ hθ => (hDK θ hθ).trans (le_max_left _ _))
    (fun θ hθ => ⟨(hG θ hθ).1, (hG θ hθ).2.trans (le_max_left _ _)⟩) hK' hd hdβ hsmall'
  simp only [C_DT, C_DX, C_DN, C_B, C_G, C_X, Theta, mSize_max_one] at h ⊢
  exact h

end Src

end KAM.Iso.Linear.AnyOmega

end
