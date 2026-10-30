/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Correction
public import KAM.Apost.NewtonError
import KAM.Strip.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The new invariance error, with the sharp constants

Blueprint `bp:p2s:newton-error` (`KAM.Sharp.newton_error_bounds`): under the hypotheses of
`bp:p2s:correction`, `C_ΔK ε/(γ² δ^{2κ}) < β` and `C_sym ε/(γ δ^{κ+1}) ≤ 1/2`, the Newton map
lies in
`𝔅`, `S = I - Ω₀ E_sym` is invertible with `|S⁻¹| ≤ 2`, `Ē = P S⁻¹ E_lin + Δ²X`, and
`|Ē| ≤ C_E ε²/(γ⁴ δ^{4κ})` on `T_{r-2δ}`.

The proof follows the blueprint:

* `step:p2s:ne-id`: the identity is re-assembled from the constant-free pieces of
  `KAM.Apost.newton_error` (`NewtonError.sMat_spec`, `newtonMap_mem`,
  `sumVec_invarianceError_newtonMap`, `alg_core`, `xi_equation`), with `|E_sym| ≤ 1/2` from
  `KAM.Sharp.geometry_sep`;
* `step:p2s:ne-lin`: `|E_lin| ≤ C_lin ε²/(γ² δ^{2κ+1})` (`NewtonError.norm_linError_le`,
  `lin_eq`);
* `step:p2s:ne-quad`: `|Δ²X| ≤ (M/2) |ΔK|²` by Taylor's formula (`norm_quadRemainder_half`);
* `step:p2s:ne-total`: `|P| ≤ σ_K (1 + σ_B)` and the absorption of `γ² δ^{2κ-1}` into `γ̄²`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

variable {n : ℕ} {κ cR M σK σB σT γb : ℝ}
variable {τ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ω : Fin n → ℝ} {γ : ℝ}

namespace NewtonErrorSharp

/-- Step `step:p2s:ne-quad`: `|Δ²X| ≤ (M/2) d²` if `|ΔK(θ)| ≤ d < β` and `B_β(K(θ)) ⊆ 𝔅`
(Taylor's formula, `bp:p1:taylor`). -/
theorem norm_quadRemainder_half (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {β d : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hball : Metric.ball (K θ) β ⊆ 𝔅) (hcorr : ‖correction h K ω θ‖ ≤ d) (hd : d < β) :
    ‖quadRemainder h K ω θ‖ ≤ M / 2 * d ^ 2 := by
  have hw : ‖correction h K ω θ‖ < β := lt_of_le_of_lt hcorr hd
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg _) hw
  have hzw : K θ + correction h K ω θ ∈ Metric.ball (K θ) β := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg : segment ℝ (K θ) (K θ + correction h K ω θ) ⊆ 𝔅 :=
    ((convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hzw).trans hball
  have h1 := taylor_iteratedFDeriv hS.isOpen (differentiableOn_ham hS) (A := M)
    (fun x hx => (hS.bounds x hx).2.2) hseg
  calc ‖quadRemainder h K ω θ‖ ≤ M / 2 * ‖correction h K ω θ‖ ^ 2 := h1
    _ ≤ M / 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcorr 2)
          (by linarith [hS.M_pos])

/-- Step `step:p2s:ne-lin`, constants:
`(C_red ε/δ)(C_ξ ε/(γ² δ^{2κ})) + (C_sym ε/(γ δ^{κ+1}))(C_∂ξ ε/(γ δ^κ))
= C_lin ε²/(γ² δ^{2κ+1})`. -/
theorem lin_eq {n : ℕ} {cR M σK σB σT γb γ δ ε : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    cRed n σK σB * ε / δ * (cXi n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) +
        cSym n cR σK σB * ε / (γ * δ ^ (κ + 1)) * (cDXi n cR M σK σB σT γb * ε / (γ * δ ^ κ)) =
      cLin n cR M σK σB σT γb * ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)) := by
  have hδκ : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  rw [Real.rpow_add_one hδ.ne', Real.rpow_add_one hδ.ne', two_mul, Real.rpow_add hδ]
  unfold cLin
  field_simp

/-- Step `step:p2s:ne-total`, constants: with `|P| ≤ σ_K (1 + σ_B)`, `|S⁻¹| ≤ 2`,
`|E_lin| ≤ C_lin ε²/(γ² δ^{2κ+1})` and `|ΔK| ≤ C_ΔK ε/(γ² δ^{2κ})`, the total is at most
`C_E ε²/(γ⁴ δ^{4κ})`. -/
theorem total_le {n : ℕ} {cR M σK σB σT γb γ δ ε : ℝ} (hκ : 1 ≤ κ) (hγ : 0 < γ) (hγb : γ ≤ γb)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hσK : 0 ≤ σK) (hσB : 0 ≤ σB)
    (hc : 0 ≤ cLin n cR M σK σB σT γb) :
    σK * (1 + σB) * (2 * (cLin n cR M σK σB σT γb * ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)))) +
        M / 2 * (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 ≤
      cE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) := by
  obtain ⟨-, -, -, ⟨hab, -, -⟩⟩ := absorb (γb := γb) hκ hγ hγb hδ hδ1 hε
  have hδκ : 0 < δ ^ (2 * κ) := Real.rpow_pos_of_pos hδ _
  have hsq : (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 =
      cDK n cR M σK σB σT γb ^ 2 * (ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ)))) := by
    rw [show 2 * (2 * κ) = 2 * κ + 2 * κ by ring, Real.rpow_add hδ]
    field_simp
  have hcE : cE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) =
      2 * σK * (1 + σB) * γb ^ 2 * cLin n cR M σK σB σT γb *
          (ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ)))) +
        M / 2 * (cDK n cR M σK σB σT γb ^ 2 * (ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))))) := by
    unfold cE
    ring
  rw [hsq, hcE]
  have hlin : σK * (1 + σB) * (2 * (cLin n cR M σK σB σT γb * ε ^ 2 /
      (γ ^ 2 * δ ^ (2 * κ + 1)))) =
      2 * σK * (1 + σB) * cLin n cR M σK σB σT γb * (ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1))) := by
    ring
  rw [hlin]
  refine add_le_add ?_ le_rfl
  calc 2 * σK * (1 + σB) * cLin n cR M σK σB σT γb * (ε ^ 2 / (γ ^ 2 * δ ^ (2 * κ + 1)))
      ≤ 2 * σK * (1 + σB) * cLin n cR M σK σB σT γb *
          (γb ^ 2 * (ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))))) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
    _ = _ := by ring

end NewtonErrorSharp

/-- Blueprint `bp:p2s:newton-error` (the identity is re-assembled from the constant-free helpers
`KAM.Apost.NewtonError.sMat_spec`, `newtonMap_mem`, `sumVec_invarianceError_newtonMap` and
`KAM.Apost.xi_equation`). -/
theorem newton_error_bounds (hC : CohData n τ κ cR) (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hγb : γ ≤ γb) {r β ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : Admissible σK σB σT 𝔅 h ω r β ε K) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r)
    (hεδ : ε ≤ δ)
    (hTS : cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1)
    (hβ : cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) < β)
    (hsym : cSym n cR σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1 / 2) :
    (∀ θ ∈ complexStrip n (r - 2 * δ), newtonMap h K ω (r - 2 * δ) θ ∈ 𝔅) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ), IsUnit (sMat K θ).det ∧ ‖(sMat K θ)⁻¹‖ ≤ 2) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      sumVec n (invarianceError h (newtonMap h K ω (r - 2 * δ)) ω θ) =
        frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ linError h K ω θ) + sumVec n (quadRemainder h K ω θ)) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖invarianceError h (newtonMap h K ω (r - 2 * δ)) ω θ‖ ≤
        cE n cR M σK σB σT γb * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * κ))) := by
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hn : 0 < n := by have := hS.two_le; omega
  have hsubr : complexStrip n (r - 2 * δ) ⊆ complexStrip n r :=
    Triangular.strip_mono (by linarith)
  have hsub1 : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨⟨-, -, -, -, -, -, -, hPd, -⟩, -, -, -⟩ :=
    frame_basic hS hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  obtain ⟨⟨hξd, -, -, -, -, -⟩, -, -⟩ := correction_spec hS hK hδ hδ1 h2δ
  obtain ⟨-, -, -, hbd⟩ := correction_bounds hC hS hγb hK hδ hδ1 h2δ hεδ hTS
  obtain ⟨hgeo1, hgeo2⟩ := geometry_sep hC hS (CorrectionSharp.admissible_noTwist hK) hδ hδ1 h2δ
  have hfi := frame_identities hS hr hK.holo hK𝔅 hGu
  have hxieq := NewtonError.xi_equation hS hK hδ hδ1 h2δ
  -- step `ne-id`: invertibility of `S`
  have hSinv : ∀ θ ∈ complexStrip n (r - 2 * δ), IsUnit (sMat K θ).det ∧ ‖(sMat K θ)⁻¹‖ ≤ 2 :=
    fun θ hθ => NewtonError.sMat_spec hn ((hgeo2 θ hθ).2.trans hsym)
  -- step `ne-id`: the expansion and the reduction
  have hident : ∀ θ ∈ complexStrip n (r - 2 * δ),
      sumVec n (invarianceError h (newtonMap h K ω (r - 2 * δ)) ω θ) =
        frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ linError h K ω θ) + sumVec n (quadRemainder h K ω θ) := by
    intro θ hθ
    have hθr := hsubr hθ
    have hopen_r := (isOpen_complexStrip n r).mem_nhds hθr
    have hopen_w := (isOpen_complexStrip n (r - 2 * δ)).mem_nhds hθ
    rw [NewtonError.sumVec_invarianceError_newtonMap hθ (hK.holo.differentiableAt hopen_r)
      (hPd.differentiableAt hopen_r) (hξd.differentiableAt hopen_w)]
    obtain ⟨-, -, -, -, hred, hQP, hQE⟩ := hfi θ hθr
    have hSS : sMat K θ * (sMat K θ)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ (hSinv θ hθ).1
    have key := NewtonError.alg_core (frameMat K θ) (reducer K θ)
      (triangularMat (torsion h K ω θ)) (redDefect h K ω θ) (linMat h K θ)
      (fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))) (sMat K θ) (sMat K θ)⁻¹
      (sumVec n (invarianceError h K ω θ)) (eta h K ω θ) (xi h K ω θ)
      (fderiv ℂ (xi h K ω) θ (fun l => (ω l : ℂ))) hQP hSS hQE hred (hxieq θ hθ)
    have hone : 1 - sMat K θ = omegaZeroMatrix n * symDefect K θ := by
      unfold sMat
      exact sub_sub_cancel _ _
    rw [key, hone]
    rfl
  refine ⟨fun θ hθ => ?_, hSinv, hident, fun θ hθ => ?_⟩
  · exact NewtonError.newtonMap_mem hθ (hK.ball_sub θ (hsubr hθ))
      (lt_of_le_of_lt (hbd θ hθ).2.2.1 hβ)
  · have hθr := hsubr hθ
    have hcLin : 0 ≤ cLin n cR M σK σB σT γb := by
      have := hC.cR_pos
      have := hS.σK_pos
      have := hS.σB_pos
      have := hS.σT_pos
      have := hS.M_pos
      have : 0 < γb := hγ.trans_le hγb
      unfold cLin cRed cXi cSym cDXi cOm cG cXiN cXi0 hT cT0
      positivity
    obtain ⟨-, -, -, -, -, -, hPn, -⟩ :=
      frame_bounds hS (hK𝔅 θ hθr) (hK.deriv_le θ hθr) (hGu θ hθr) (hK.gram θ hθr).2 ω
    obtain ⟨-, hξb, hcb, hdξb⟩ := hbd θ hθ
    have hlin := NewtonError.norm_linError_le (h := h) (ω := ω) (K := K) (θ := θ)
      (hgeo1 θ (hsub1 hθ)).2.2.2 hξb (hgeo2 θ hθ).2 hdξb
    rw [NewtonErrorSharp.lin_eq hγ hδ] at hlin
    have hq' := NewtonErrorSharp.norm_quadRemainder_half hS (hK.ball_sub θ hθr) hcb hβ
    rw [← norm_sumVec, hident θ hθ]
    calc _ ≤ ‖frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ linError h K ω θ)‖ +
          ‖sumVec n (quadRemainder h K ω θ)‖ := norm_add_le _ _
      _ ≤ σK * (1 + σB) * (2 * (cLin n cR M σK σB σT γb * ε ^ 2 /
            (γ ^ 2 * δ ^ (2 * κ + 1)))) +
          M / 2 * (cDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 := by
        rw [norm_sumVec]
        exact add_le_add (NewtonError.norm_mulVec_mulVec_le hPn (hSinv θ hθ).2 hlin) hq'
      _ ≤ _ := NewtonErrorSharp.total_le hC.one_le_kappa hγ hγb hδ hδ1 hε0 hS.σK_pos.le
          hS.σB_pos.le hcLin

end KAM.Sharp

end
