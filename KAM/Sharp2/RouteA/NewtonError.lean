/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Correction
public import KAM.Apost.NewtonError
import KAM.Strip.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The new invariance error of route A

`newton_error_boundsA`: the error of the Newton map `K̄ = K + P ξ` is
`≤ C_E ε²/(γ⁴ δ^{2a})` on `T_{r-2δ}`, `a = 2κ`, with `C_E` of `bp:p2s2:constantsA`. The identity
`Ē = P S⁻¹ E_lin + Δ²X` is assembled as in `KAM.Sharp.newton_error_bounds` from the constant-free
pieces of `KAM.Apost.NewtonError`; the bounds use the refined data (`|P| ≤ σ_K + σ_N`,
`|Δ²X| ≤ (M₂/2)|ΔK|²`, `E_red`, `E_sym` of `KAM.Sharp2.RouteA.Geometry`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ} {τ M : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- `|Δ²X| ≤ (M₂/2) d²` if `|ΔK(θ)| ≤ d < β`, `B_β(K(θ)) ⊆ 𝔅` and `|D²X_h| ≤ M₂` on `𝔅`. -/
theorem norm_quadRemainder_M2 {σK σB σT M2 : ℝ} (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M2) (hM2 : 0 ≤ M2)
    {β d : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hball : Metric.ball (K θ) β ⊆ 𝔅) (hcorr : ‖correction h K ω θ‖ ≤ d) (hd : d < β) :
    ‖quadRemainder h K ω θ‖ ≤ M2 / 2 * d ^ 2 := by
  have hw : ‖correction h K ω θ‖ < β := lt_of_le_of_lt hcorr hd
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg _) hw
  have hzw : K θ + correction h K ω θ ∈ Metric.ball (K θ) β := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg : segment ℝ (K θ) (K θ + correction h K ω θ) ⊆ 𝔅 :=
    ((convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hzw).trans hball
  have h1 := taylor_iteratedFDeriv hS.isOpen (differentiableOn_ham hS) (A := M2) hd2 hseg
  calc ‖quadRemainder h K ω θ‖ ≤ M2 / 2 * ‖correction h K ω θ‖ ^ 2 := h1
    _ ≤ M2 / 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcorr 2) (by positivity)

/-- `|P| ≤ σ_K + σ_N`. -/
theorem norm_frameMat_le {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ} {a b : ℝ}
    (hL : ‖tangentMat K θ‖ ≤ a) (hN : ‖normalMat K θ‖ ≤ b) : ‖frameMat K θ‖ ≤ a + b :=
  (Tools.norm_fromCols_le_add _ _).trans (add_le_add hL hN)

/-- The identity `Ē = P S⁻¹ E_lin + Δ²X` from `|E_sym| ≤ 1/2`. -/
theorem newton_identity {σK σB σT : ℝ} (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r β ε δ : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : Admissible σK σB σT 𝔅 h ω r β ε K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h2δ : 2 * δ < r) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (r - 2 * δ)) (hsym : ‖symDefect K θ‖ ≤ 1 / 2) :
    IsUnit (sMat K θ).det ∧ ‖(sMat K θ)⁻¹‖ ≤ 2 ∧
    sumVec n (invarianceError h (newtonMap h K ω (r - 2 * δ)) ω θ) =
      frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ linError h K ω θ) + sumVec n (quadRemainder h K ω θ) := by
  have hr := hK.r_pos
  have hn : 0 < n := by have := hS.two_le; omega
  have hθr : θ ∈ complexStrip n r := Triangular.strip_mono (by linarith) hθ
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅 := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  obtain ⟨⟨-, -, -, -, -, -, -, hPd, -⟩, -, -, -⟩ :=
    frame_basic hS hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  obtain ⟨⟨hξd, -, -, -, -, -⟩, -, -⟩ := correction_spec hS hK hδ hδ1 h2δ
  have hSi := NewtonError.sMat_spec hn hsym
  refine ⟨hSi.1, hSi.2, ?_⟩
  have hopen_r := (isOpen_complexStrip n r).mem_nhds hθr
  have hopen_w := (isOpen_complexStrip n (r - 2 * δ)).mem_nhds hθ
  rw [NewtonError.sumVec_invarianceError_newtonMap hθ (hK.holo.differentiableAt hopen_r)
    (hPd.differentiableAt hopen_r) (hξd.differentiableAt hopen_w)]
  obtain ⟨-, -, -, -, hred, hQP, hQE⟩ := frame_identities hS hr hK.holo hK𝔅 hGu θ hθr
  have hSS : sMat K θ * (sMat K θ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hSi.1
  have key := NewtonError.alg_core (frameMat K θ) (reducer K θ)
    (triangularMat (torsion h K ω θ)) (redDefect h K ω θ) (linMat h K θ)
    (fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))) (sMat K θ) (sMat K θ)⁻¹
    (sumVec n (invarianceError h K ω θ)) (eta h K ω θ) (xi h K ω θ)
    (fderiv ℂ (xi h K ω) θ (fun l => (ω l : ℂ))) hQP hSS hQE hred
    (NewtonError.xi_equation hS hK hδ hδ1 h2δ θ hθ)
  have hone : 1 - sMat K θ = omegaZeroMatrix n * symDefect K θ := by
    unfold sMat
    exact sub_sub_cancel _ _
  rw [key, hone]
  rfl

/-- Definition `bp:p2s2:constantsA`, the new error (`p.iso = false`, `Θ = 0`). -/
theorem newton_error_boundsA {p : StepInA} (hp : p.Pos) (hfix : p.iso = false) (hΘ : p.Θ = 0)
    (hpn : p.n = n) (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ p.M2)
    (hγb : γ ≤ p.γb) {Ω : Set (Fin n → ℝ)} (hω : ω ∈ Ω)
    {r β ε δ b cb : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmA 𝔅 h ω r (r - δ) β ε p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r) (hε1 : ε ≤ 1)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ))
    (hβ : p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hsym : p.CSym * (ε / (γ * δ ^ (p.κ + 1))) ≤ 1 / 2) :
    (∀ θ ∈ complexStrip n (r - 2 * δ), ‖correction h K ω θ‖ ≤
      p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ), ‖lagrangeMat K θ‖ ≤ p.COm * (ε / (γ * δ ^ (p.κ + 1)))) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖invarianceError h (newtonMap h K ω (r - 2 * δ)) ω θ‖ ≤
        p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) := by
  subst hpn
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  have hsubr : complexStrip p.n (r - 2 * δ) ⊆ complexStrip p.n r :=
    Triangular.strip_mono (by linarith)
  have hsub1 : complexStrip p.n (r - 2 * δ) ⊆ complexStrip p.n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hsub2 : complexStrip p.n (r - δ) ⊆ complexStrip p.n r :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 := hK.mem
  have hAd := hK.toAdmissible hε1
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hηd, -, -⟩, -, -, -⟩ :=
    frame_basic hS hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  have hηNd := Correction.diffOn_etaN hηd
  have hHN : ∀ θ ∈ complexStrip p.n r, ‖etaN h K ω θ‖ ≤ p.sLt * ε := fun θ hθ =>
    norm_etaN_le (hK.tangentT θ hθ) (hK.error_le θ hθ)
  have hbd := (correction_boundsA hp hfix hΘ hS hγb hω hK hδ hδD h2δ hc hcb hbr hca).2
  have hΩ : ∀ θ ∈ complexStrip p.n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ p.COm * (ε / (γ * δ ^ (p.κ + 1))) := by
    intro θ hθ
    refine (norm_lagrangeMat_le hS hp.n_pos hc hω hr h2δ hK.holo hK.primary hK𝔅 hηNd hHN θ hθ).trans
      (le_of_eq ?_)
    unfold StepInA.COm
    ring
  have hsy : ∀ θ ∈ complexStrip p.n (r - 2 * δ),
      ‖symDefect K θ‖ ≤ p.CSym * (ε / (γ * δ ^ (p.κ + 1))) := by
    intro θ hθ
    have := norm_symDefect_le (hK.gram θ (hsubr hθ)).1 (hK.gram θ (hsubr hθ)).2 (hΩ θ hθ)
    unfold StepInA.CSym
    rwa [mul_assoc]
  refine ⟨fun θ hθ => (hbd θ hθ).2.1, hΩ, fun θ hθ => ?_⟩
  obtain ⟨hξ, hΔ, hdξ⟩ := hbd θ hθ
  have hθr := hsubr hθ
  obtain ⟨hSu, hSn, hid⟩ := newton_identity hS hAd hδ hδ1 h2δ hθ ((hsy θ hθ).trans hsym)
  -- `E_red`
  obtain ⟨hDE, hDEt⟩ := Geometry.geo_de hS hK.holo hK𝔅 hK.error_le hδ θ (hsub1 hθ)
  have hred := norm_redDefect_le hδ hε0 hDE hDEt (hK.tangentT θ hθr) (hK.normal θ hθr)
    (hK.normalT θ hθr)
  have hlin := NewtonError.norm_linError_le hred hξ (hsy θ hθ) hdξ
  obtain ⟨-, -, -, -, s5, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set X := ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) with hX
  set x := ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) with hx
  have hs0 : 0 < δ ^ p.κ := Real.rpow_pos_of_pos hδ _
  have hx0 : 0 ≤ x := div_nonneg hε0 (by positivity)
  have e2 : δ ^ (2 * p.κ) = (δ ^ p.κ) ^ 2 := by rw [two_mul, Real.rpow_add hδ, sq]
  have e4 : δ ^ (2 * (2 * p.κ)) = (δ ^ p.κ) ^ 4 := by
    rw [show 2 * (2 * p.κ) = 2 * p.κ + 2 * p.κ by ring, Real.rpow_add hδ, e2]; ring
  have e21 : δ ^ (2 * p.κ + 1) = (δ ^ p.κ) ^ 2 * δ := by rw [Real.rpow_add_one hδ.ne', e2]
  have e11 : δ ^ (p.κ + 1) = δ ^ p.κ * δ := Real.rpow_add_one hδ.ne' _
  -- `|E_lin| ≤ C_lin ε X`
  have hL0 : (p.CRed * ε / δ) * (p.CXi * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) +
      (p.CSym * (ε / (γ * δ ^ (p.κ + 1)))) * (p.CDXi * (ε / (γ * δ ^ p.κ))) = p.CLin * (ε * X) := by
    have e0 : p.CLin = p.CRed * p.CXi + p.CSym * p.CDXi := by simp [StepInA.CLin, hΘ]
    rw [e0, hX, e21, e2, e11]
    field_simp
  have hL1 : ‖linError h K ω θ‖ ≤ p.CLin * (ε * X) := by
    rw [← hL0]
    exact hlin
  have hsq : (p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ^ 2 = p.CDK ^ 2 * (ε * x) := by
    rw [hx, e2, e4]
    field_simp
  have hq := norm_quadRemainder_M2 hS hd2 hp.M2 (hK.ball_sub θ hθr) hΔ hβ
  have hPn := norm_frameMat_le (hK.tangent_le hθr) (hK.normal θ hθr)
  have hXle : X ≤ (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x := by
    rw [s5]
    exact mul_le_mul_of_nonneg_right (pow_mul_rpow_le 2 hγ hγb hδ hδD
      (by linarith [hp.κ_ge])) hx0
  have hC : p.CE = 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * p.CLin + p.M2 / 2 * p.CDK ^ 2 := by
    simp [StepInA.CE, StepInA.CE1, hfix]
  have hgoal : p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) = p.CE * (ε * x) := by
    rw [hx, mul_div_assoc]
    congr 1
    rw [sq]
    ring
  rw [hgoal, ← norm_sumVec, hid]
  have hP0 := hp.P
  have hCL := hp.CLin
  calc _ ≤ ‖frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ linError h K ω θ)‖ +
        ‖sumVec p.n (quadRemainder h K ω θ)‖ := norm_add_le _ _
    _ ≤ p.P * (2 * (p.CLin * (ε * X))) + p.M2 / 2 * (p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ^ 2 :=
        by
        rw [norm_sumVec]
        exact add_le_add (NewtonError.norm_mulVec_mulVec_le hPn hSn hL1) hq
    _ = 2 * p.P * p.CLin * ε * X + p.M2 / 2 * (p.CDK ^ 2 * (ε * x)) := by rw [hsq]; ring
    _ ≤ 2 * p.P * p.CLin * ε * ((p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x) +
          p.M2 / 2 * (p.CDK ^ 2 * (ε * x)) :=
        add_le_add (mul_le_mul_of_nonneg_left hXle (by positivity)) le_rfl
    _ = p.CE * (ε * x) := by rw [hC]; ring

end KAM.Sharp2.RouteA

end
