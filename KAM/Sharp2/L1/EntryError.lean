/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.EntryCorrection
public import KAM.Sharp2.L1.SolveDefect
public import KAM.Sharp2.RouteA.NewtonError
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The new error of the ℓ¹ entry step (package B10c)

Blueprint `bp:p2s2l1:entryA`, the new error: B9's `KAM.Sharp2.RouteA.newton_error_boundsA` with the
entry constants. The Lagrangian defect of the initial torus is bounded by the smaller of B9's sup
bound and the ℓ¹ bound of the defect identity (`KAM.Sharp2.L1.norm_lagrangeMat_le_l1` at the bites
`δ, δ`): `|Ω_K| ≤ C^K_Ω ε/(γ δ^{κ+1})`, `C^K_Ω = min {C_Ω, (n/e) G₀ a_N g}`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

variable {n : ℕ} {τ M : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- The Lagrangian defect of the initial torus on `T_{r-2δ}`: `|Ω_K| ≤ C^K_Ω ε/(γ δ^{κ+1})`. -/
theorem entry_lagrange_le_of {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf)
    (hpn : p.n = n) {σK σB σT : ℝ} (hS : Standing n τ M σK σB σT 𝔅 h ω γ) (hγb : γ ≤ p.γb)
    {Ω : Set (Fin n → ℝ)} (hω : ω ∈ Ω) {r ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hr : 0 < r) (hε0 : 0 ≤ ε) (hKd : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hηNd : DifferentiableOn ℂ (etaN h K ω) (complexStrip n r))
    (hHN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ p.sLt * ε)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r) (hc : SDConst n p.κ γ δ p.c Ω)
    (hηN1 : L1Vec r (etaN h K ω) (E.aN * ε)) (hΓ : smallDivisorSup ω δ ≤ E.G0) :
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1))) := by
  subst hpn
  intro θ hθ
  have hγ := hS.gamma_pos
  have hK := hKd
  set W := ε / (γ * δ ^ (p.κ + 1)) with hW
  have hW0 : 0 ≤ W := div_nonneg hε0 (by positivity)
  unfold Ent.COmK
  rw [min_mul_of_nonneg _ _ hW0]
  refine le_min ?_ ?_
  · refine (norm_lagrangeMat_le hS hp.n_pos hc hω hr h2δ hKd hKp hK𝔅 hηNd hHN θ
      hθ).trans (le_of_eq ?_)
    unfold StepInA.COm
    ring
  · have hθ' : θ ∈ complexStrip p.n (r - δ - δ) := by rwa [show r - δ - δ = r - 2 * δ by ring]
    have h1 := norm_lagrangeMat_le_l1 hS hδ hδ (by linarith) hKd hKp hK𝔅 hGu hηN1 θ hθ'
    have hεδ : ε / δ ≤ p.g * W := by
      obtain ⟨-, -, -, -, -, -, -, s8⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
      have hgd := StepInA.gd_le hp hγ hγb hδ hδD
      have e : ε / δ = (γ * δ ^ p.κ) * W := by
        rw [hW, Real.rpow_add_one hδ.ne']
        have := Real.rpow_pos_of_pos hδ p.κ
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right hgd hW0
    have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
    have haN := hE.aN
    calc ‖lagrangeMat K θ‖ ≤ p.n / (Real.exp 1 * δ) * smallDivisorSup ω δ * (E.aN * ε) := h1
      _ = p.n * (Real.exp 1)⁻¹ * smallDivisorSup ω δ * E.aN * (ε / δ) := by
          field_simp
      _ ≤ p.n * (Real.exp 1)⁻¹ * E.G0 * E.aN * (p.g * W) := by
          have he : 0 ≤ (Real.exp 1)⁻¹ := (inv_pos.2 (Real.exp_pos 1)).le
          have h0 : 0 ≤ ε / δ := div_nonneg hε0 hδ.le
          have hs : 0 ≤ smallDivisorSup ω δ := smallDivisorSup_nonneg ω δ
          calc p.n * (Real.exp 1)⁻¹ * smallDivisorSup ω δ * E.aN * (ε / δ)
              ≤ p.n * (Real.exp 1)⁻¹ * E.G0 * E.aN * (ε / δ) := by gcongr
            _ ≤ p.n * (Real.exp 1)⁻¹ * E.G0 * E.aN * (p.g * W) := by
                have := hE.G0
                gcongr
      _ = p.n * Ent.einv * E.G0 * E.aN * p.g * W := by unfold Ent.einv; ring

/-- The Lagrangian defect of the initial torus on `T_{r-2δ}` (fixed frequency). -/
theorem entry_lagrange_le {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf) (hpn : p.n = n)
    (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ) (hγb : γ ≤ p.γb) {Ω : Set (Fin n → ℝ)}
    (hω : ω ∈ Ω) {r β ε δ : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmA 𝔅 h ω r (r - δ) β ε p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r) (hc : SDConst n p.κ γ δ p.c Ω)
    (hD : EntryData E h K ω r δ ε) :
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1))) := by
  have hr := hK.r_pos
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hηd, -, -⟩, -, -, -⟩ :=
    frame_basic hS hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  exact entry_lagrange_le_of hp hE hpn hS hγb hω hr hK.ε_nonneg hK.holo hK.primary hK.mem
    (fun θ hθ => (hK.gram θ hθ).1) (Correction.diffOn_etaN hηd)
    (fun θ hθ => norm_etaN_le (hK.tangentT θ hθ) (hK.error_le θ hθ)) hδ hδD h2δ hc hD.l1EtaN
    hD.gam0

/-- Blueprint `bp:p2s2l1:entryA`, the new error (`p.iso = false`, `Θ = 0`). -/
theorem entry_newton_error {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf)
    (hfix : p.iso = false) (hΘ : p.Θ = 0) (hpn : p.n = n)
    (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ p.M2)
    (hγb : γ ≤ p.γb) {Ω : Set (Fin n → ℝ)} (hω : ω ∈ Ω)
    {r β ε δ b cb : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmA 𝔅 h ω r (r - δ) β ε p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r) (hε1 : ε ≤ 1)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ)) (hD : EntryData E h K ω r δ ε)
    (hβ : Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hsym : Ent.CSym p E * (ε / (γ * δ ^ (p.κ + 1))) ≤ 1 / 2) :
    (∀ θ ∈ complexStrip n (r - 2 * δ), ‖correction h K ω θ‖ ≤
      Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ Ent.COmK p E * (ε / (γ * δ ^ (p.κ + 1)))) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖invarianceError h (newtonMap h K ω (r - 2 * δ)) ω θ‖ ≤
        Ent.CE p E * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) := by
  have hΩ := entry_lagrange_le hp hE hpn hS hγb hω hK hδ hδD h2δ hc hD
  subst hpn
  have hk := Ent.nonneg hp hE
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hsubr : complexStrip p.n (r - 2 * δ) ⊆ complexStrip p.n r :=
    Triangular.strip_mono (by linarith)
  have hsub1 : complexStrip p.n (r - 2 * δ) ⊆ complexStrip p.n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 := hK.mem
  have hAd := hK.toAdmissible hε1
  have hbd := (entry_correction_bounds hp hE hfix hΘ hS hγb hω hK hδ hδD h2δ hc hcb hbr hca
    hD).2.1
  have hsy : ∀ θ ∈ complexStrip p.n (r - 2 * δ),
      ‖symDefect K θ‖ ≤ Ent.CSym p E * (ε / (γ * δ ^ (p.κ + 1))) := by
    intro θ hθ
    have := norm_symDefect_le (hK.gram θ (hsubr hθ)).1 (hK.gram θ (hsubr hθ)).2 (hΩ θ hθ)
    unfold Ent.CSym
    rwa [mul_assoc]
  refine ⟨fun θ hθ => (hbd θ hθ).2.1, hΩ, fun θ hθ => ?_⟩
  obtain ⟨hξ, hΔ, hdξ⟩ := hbd θ hθ
  have hθr := hsubr hθ
  obtain ⟨hSu, hSn, hid⟩ := newton_identity hS hAd hδ (hδD.trans hp.δ1) h2δ hθ
    ((hsy θ hθ).trans hsym)
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
  have hL0 : (p.CRed * ε / δ) * (Ent.CXi p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) +
      (Ent.CSym p E * (ε / (γ * δ ^ (p.κ + 1)))) * (Ent.CDXi p E * (ε / (γ * δ ^ p.κ))) =
        Ent.CLin p E * (ε * X) := by
    have e0 : Ent.CLin p E = p.CRed * Ent.CXi p E + Ent.CSym p E * Ent.CDXi p E := by
      simp [Ent.CLin, hΘ]
    rw [e0, hX, e21, e2, e11]
    field_simp
  have hL1 : ‖linError h K ω θ‖ ≤ Ent.CLin p E * (ε * X) := by
    rw [← hL0]
    exact hlin
  have hsq : (Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ^ 2 = Ent.CDK p E ^ 2 * (ε * x) := by
    rw [hx, e2, e4]
    field_simp
  have hq := norm_quadRemainder_M2 hS hd2 hp.M2 (hK.ball_sub θ hθr) hΔ hβ
  have hPn := norm_frameMat_le (hK.tangent_le hθr) (hK.normal θ hθr)
  have hXle : X ≤ (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x := by
    rw [s5]
    exact mul_le_mul_of_nonneg_right (pow_mul_rpow_le 2 hγ hγb hδ hδD
      (by linarith [hp.κ_ge])) hx0
  have hC : Ent.CE p E = 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * Ent.CLin p E +
      p.M2 / 2 * Ent.CDK p E ^ 2 := by
    simp [Ent.CE, Ent.CE1, hfix]
  have hgoal : Ent.CE p E * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) = Ent.CE p E * (ε * x) := by
    rw [hx, mul_div_assoc]
    congr 1
    rw [sq]
    ring
  rw [hgoal, ← norm_sumVec, hid]
  have hP0 := hp.P
  have hCL := hk.CLin
  calc _ ≤ ‖frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ linError h K ω θ)‖ +
        ‖sumVec p.n (quadRemainder h K ω θ)‖ := norm_add_le _ _
    _ ≤ p.P * (2 * (Ent.CLin p E * (ε * X))) +
          p.M2 / 2 * (Ent.CDK p E * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ^ 2 := by
        rw [norm_sumVec]
        exact add_le_add (NewtonError.norm_mulVec_mulVec_le hPn hSn hL1) hq
    _ = 2 * p.P * Ent.CLin p E * ε * X + p.M2 / 2 * (Ent.CDK p E ^ 2 * (ε * x)) := by
        rw [hsq]; ring
    _ ≤ 2 * p.P * Ent.CLin p E * ε * ((p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x) +
          p.M2 / 2 * (Ent.CDK p E ^ 2 * (ε * x)) :=
        add_le_add (mul_le_mul_of_nonneg_left hXle (by positivity)) le_rfl
    _ = Ent.CE p E * (ε * x) := by rw [hC]; ring

end KAM.Sharp2.L1

end
