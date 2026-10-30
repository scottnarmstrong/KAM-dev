/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.RouteA.Correction
public import KAM.Sharp2.RouteA.NewtonError
public import KAM.Iso.Sharp.NewtonError
import KAM.Strip.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The new errors of the isoenergetic route A

`iso_newton_error_boundsA`: the invariance error at the new frequency and the energy error of the
Newton map are `≤ C_E ε²/(γ⁴ δ^{2a})`, with `C_E = max {C_E1, C_E2}` of `bp:p2s2:constantsA`. The
identities are `KAM.Iso.Sharp.IsoNewtonErrorSharp.sumVec_error_eq_of`, `energyAverage_sub_eq_of`
(constant-free); the bounds use the refined data.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp

variable {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ωstar : Fin n → ℝ} {τ M σω ν γ : ℝ}

/-- `|Δ²X| ≤ (M₂/2) d²`. -/
theorem norm_isoQuadX_M2 {σK σB σT M2 : ℝ} {ω₀ ω : Fin n → ℝ} {E₀ β d : ℝ}
    (hS : Standing n τ M σK σB σT D H ω₀ γ)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M2) (hM2 : 0 ≤ M2)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hball : Metric.ball (K θ) β ⊆ D) (hcorr : ‖isoCorrection H K ω E₀ θ‖ ≤ d) (hd : d < β) :
    ‖isoQuadX H K ω E₀ θ‖ ≤ M2 / 2 * d ^ 2 := by
  have hw : ‖isoCorrection H K ω E₀ θ‖ < β := lt_of_le_of_lt hcorr hd
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg _) hw
  have hzw : K θ + isoCorrection H K ω E₀ θ ∈ Metric.ball (K θ) β := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg : segment ℝ (K θ) (K θ + isoCorrection H K ω E₀ θ) ⊆ D :=
    ((convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hzw).trans hball
  have h1 := taylor_iteratedFDeriv hS.isOpen (differentiableOn_ham hS) (A := M2) hd2 hseg
  calc ‖isoQuadX H K ω E₀ θ‖ ≤ M2 / 2 * ‖isoCorrection H K ω E₀ θ‖ ^ 2 := h1
    _ ≤ M2 / 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcorr 2) (by positivity)

/-- `|Δ²H| ≤ (M_{h2}/2) d²`. -/
theorem norm_isoQuadH_Mh2 {σK σB σT Mh2 : ℝ} {ω : Fin n → ℝ} {E₀ β d : ℝ}
    (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ Mh2) (hM2 : 0 ≤ Mh2)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hball : Metric.ball (K θ) β ⊆ D) (hcorr : ‖isoCorrection H K ω E₀ θ‖ ≤ d) (hd : d < β) :
    ‖isoQuadH H K ω E₀ θ‖ ≤ Mh2 / 2 * d ^ 2 := by
  have hw : ‖isoCorrection H K ω E₀ θ‖ < β := lt_of_le_of_lt hcorr hd
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg _) hw
  have hzw : K θ + isoCorrection H K ω E₀ θ ∈ Metric.ball (K θ) β := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg : segment ℝ (K θ) (K θ + isoCorrection H K ω E₀ θ) ⊆ D :=
    ((convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hzw).trans hball
  have h1 := taylor_iteratedFDeriv hS.isOpen hS.holo (A := Mh2) hd2 hseg
  calc ‖isoQuadH H K ω E₀ θ‖ ≤ Mh2 / 2 * ‖isoCorrection H K ω E₀ θ‖ ^ 2 := h1
    _ ≤ Mh2 / 2 * d ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcorr 2) (by positivity)

/-- Products of the normalised errors, with `x = ε/(γ⁴ δ^{2a})`, `X = ε/(γ²δ^{2κ+1})`,
`E = ε/(γ²δ^{2κ})`, `u = ε/(γδ^κ)`, `Y = ε/(γδ^{κ+1})`. -/
theorem products {γ δ ε κ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    (ε / δ) * (ε / (γ ^ 2 * δ ^ (2 * κ))) = ε * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
    (ε / (γ * δ ^ (κ + 1))) * (ε / (γ * δ ^ κ)) = ε * (ε / (γ ^ 2 * δ ^ (2 * κ + 1))) ∧
    (ε / (γ ^ 2 * δ ^ (2 * κ))) ^ 2 = ε * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ)))) ∧
    (ε / (γ * δ ^ κ)) * (ε / (γ ^ 2 * δ ^ (2 * κ))) =
      (γ * δ ^ κ) * (ε * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ))))) ∧
    ε * (ε / (γ ^ 2 * δ ^ (2 * κ))) = (γ ^ 2 * δ ^ (2 * κ)) * (ε * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ))))) ∧
    (ε / (γ * δ ^ (κ + 1))) * (ε / (γ ^ 2 * δ ^ (2 * κ))) =
      (γ * δ ^ (κ - 1)) * (ε * (ε / (γ ^ 4 * δ ^ (2 * (2 * κ))))) := by
  have hs : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  have e2 : δ ^ (2 * κ) = (δ ^ κ) ^ 2 := by rw [two_mul, Real.rpow_add hδ, sq]
  have e4 : δ ^ (2 * (2 * κ)) = (δ ^ κ) ^ 4 := by
    rw [show 2 * (2 * κ) = 2 * κ + 2 * κ by ring, Real.rpow_add hδ, e2]; ring
  have e21 : δ ^ (2 * κ + 1) = (δ ^ κ) ^ 2 * δ := by rw [Real.rpow_add_one hδ.ne', e2]
  have e11 : δ ^ (κ + 1) = δ ^ κ * δ := Real.rpow_add_one hδ.ne' _
  have e1m : δ ^ (κ - 1) = δ ^ κ / δ := Real.rpow_sub_one hδ.ne' _
  rw [e2, e4, e21, e11, e1m]
  generalize δ ^ κ = s at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp

/-- Definition `bp:p2s2:constantsA`, the new errors of the isoenergetic step. -/
theorem iso_newton_error_boundsA {p : StepInA} (hp : p.Pos) (hiso : p.iso = true) (hpn : p.n = n)
    (hS : IsoStanding n τ M p.sK p.sB p.sT σω ν ωstar D H γ)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ p.M1)
    (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ p.M2)
    (hd2H : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ p.Mh2) (hγb : γ ≤ p.γb)
    {Ω : Set (Fin n → ℝ)} {E₀ r β ε δ b cb s : ℝ} (hω : s • ωstar ∈ Ω)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : AdmIA D H ωstar E₀ r (r - δ) β ε s p.sK p.sB p.sT p.sLt p.sN p.sNt p.t K)
    (hδ : 0 < δ) (hδD : δ ≤ p.δ) (h2δ : 2 * δ < r) (hεδ : ε ≤ δ) (hΘ : ‖s • ωstar‖ ≤ p.Θ)
    (hHY : ∀ θ ∈ complexStrip n r, ∑ b, ‖energyRow H K θ b‖ ≤ p.HY)
    (hc : SDConst n p.κ γ δ p.c Ω) (hcb : SDConst n p.κ γ b cb Ω) (hbr : b ≤ r)
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ))
    (hβ : p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hsym : p.CSym * (ε / (γ * δ ^ (p.κ + 1))) ≤ 1 / 2) :
    (∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoCorrection H K (s • ωstar) E₀ θ‖ ≤
      p.CDK * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ), ‖lagrangeMat K θ‖ ≤ p.COm * (ε / (γ * δ ^ (p.κ + 1)))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖invarianceError H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
          (isoNewS H K ωstar E₀ s • ωstar) θ‖ ≤
        p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))) ∧
    ‖KAM.Iso.energyAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) - (E₀ : ℂ)‖ ≤
      p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) := by
  subst hpn
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hr := hK.r_pos
  have hr' : 0 < r - 2 * δ := by linarith
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hδ1 : δ ≤ 1 := hδD.trans hp.δ1
  have hε1 : ε ≤ 1 := hεδ.trans hδ1
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hnpos : 0 < p.n := hp.n_pos
  have hsub2 : complexStrip p.n (r - 2 * δ) ⊆ complexStrip p.n r :=
    Triangular.strip_mono (by linarith)
  have hsub1 : complexStrip p.n (r - 2 * δ) ⊆ complexStrip p.n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hK𝔅 := hK.mem
  have hGu : ∀ θ ∈ complexStrip p.n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  have hAd := hK.toIso hε1
  have hKN := hAd.toAdmissibleNoTwist
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hηd, -, -⟩, -, -, -⟩ :=
    frame_basic hSt hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  have hηNd := KAM.Apost.Correction.diffOn_etaN hηd
  have hHN : ∀ θ ∈ complexStrip p.n r, ‖etaN H K (s • ωstar) θ‖ ≤ p.sLt * ε := fun θ hθ =>
    norm_etaN_le (hK.tangentT θ hθ) (hK.error_le θ hθ)
  obtain ⟨⟨hXω, -⟩, hbd, -⟩ := iso_correction_boundsA hp hiso rfl hS hd1 hγb hω hK hδ hδD h2δ hεδ hΘ
    hHY hc hcb hbr hca
  have hΩ : ∀ θ ∈ complexStrip p.n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ p.COm * (ε / (γ * δ ^ (p.κ + 1))) := by
    intro θ hθ
    refine (norm_lagrangeMat_le hSt hp.n_pos hc hω hr h2δ hK.holo hK.primary hK𝔅 hηNd hHN θ hθ).trans
      (le_of_eq ?_)
    unfold StepInA.COm
    ring
  have hsy : ∀ θ ∈ complexStrip p.n (r - 2 * δ),
      ‖symDefect K θ‖ ≤ p.CSym * (ε / (γ * δ ^ (p.κ + 1))) := by
    intro θ hθ
    have := norm_symDefect_le (hK.gram θ (hsub2 hθ)).1 (hK.gram θ (hsub2 hθ)).2 (hΩ θ hθ)
    unfold StepInA.CSym
    rwa [mul_assoc]
  have hSb : ∀ θ ∈ complexStrip p.n (r - 2 * δ), IsUnit (sMat K θ).det ∧ ‖(sMat K θ)⁻¹‖ ≤ 2 :=
    fun θ hθ => NewtonError.sMat_spec hnpos ((hsy θ hθ).trans hsym)
  have hcorr : ∀ θ ∈ complexStrip p.n (r - 2 * δ), ‖isoCorrection H K (s • ωstar) E₀ θ‖ < β :=
    fun θ hθ => lt_of_le_of_lt (hbd θ hθ).2.1 hβ
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := products (ε := ε) (κ := p.κ) hγ hδ
  obtain ⟨-, -, -, -, s5, -, -, -⟩ := scales (ε := ε) (κ := p.κ) hγ hδ
  set E := ε / (γ ^ 2 * δ ^ (2 * p.κ)) with hEd
  set u := ε / (γ * δ ^ p.κ) with hud
  set Y := ε / (γ * δ ^ (p.κ + 1)) with hYd
  set X := ε / (γ ^ 2 * δ ^ (2 * p.κ + 1)) with hXd
  set x := ε / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) with hxd
  have hx0 : 0 ≤ x := div_nonneg hε0 (by positivity)
  have hεx : 0 ≤ ε * x := mul_nonneg hε0 hx0
  have hgoal : p.CE * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) = p.CE * (ε * x) := by
    rw [hxd, mul_div_assoc]
    congr 1
    rw [sq]
    ring
  have hCE1 : p.CE1 = 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * p.CLin + p.M2 / 2 * p.CDK ^ 2 +
      p.g * p.CS * p.CdK := by simp [StepInA.CE1, hiso]
  have hCE : p.CE = max p.CE1 p.CE2 := by simp [StepInA.CE, hiso]
  have hκ := hp.κ_ge
  have hXle : X ≤ (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x := by
    rw [s5]
    exact mul_le_mul_of_nonneg_right (pow_mul_rpow_le 2 hγ hγb hδ hδD (by linarith)) hx0
  have hgd := StepInA.gd_le hp hγ hγb hδ hδD
  rw [hgoal]
  refine ⟨fun θ hθ => (hbd θ hθ).2.1, hΩ, fun θ hθ => ?_, ?_⟩
  · -- the invariance error
    have hid := IsoNewtonErrorSharp.sumVec_error_eq_of hS hAd hδ hδ1 h2δ
      (fun θ hθ => (hSb θ hθ).1) θ hθ
    obtain ⟨hxi, hΔ, hdξ, hdΔ, -⟩ := hbd θ hθ
    have hθr := hsub2 hθ
    obtain ⟨hDE, hDEt⟩ := Geometry.geo_de hSt hK.holo hK𝔅 hK.error_le hδ θ (hsub1 hθ)
    have hred := norm_redDefect_le hδ hε0 hDE hDEt (hK.tangentT θ hθr) (hK.normal θ hθr)
      (hK.normalT θ hθr)
    have hlin : ‖isoLinError H K (s • ωstar) (isoXi H K (s • ωstar) E₀)
        (isoXiOmega H K (s • ωstar) E₀) θ‖ ≤ p.CLin * (ε * X) := by
      refine (norm_isoLinError_le H K (s • ωstar) _ _ θ).trans ?_
      have h1 := mul_le_mul hred hxi (norm_nonneg _) ((norm_nonneg _).trans hred)
      have h2 := mul_le_mul (hsy θ hθ) hdξ (norm_nonneg _) (mul_nonneg hp.CSym
        (div_nonneg hε0 (by positivity)))
      have h3 := mul_le_mul (mul_le_mul (hΩ θ hθ) hΘ (norm_nonneg _) ((norm_nonneg _).trans
        (hΩ θ hθ))) hXω (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans (hΩ θ hθ)) hp.Θ)
      refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
      have e1 : (p.n : ℝ) * max p.sNt (p.sLt + 2 * p.sN) * ε / δ * (p.CXi * E) =
          p.CRed * p.CXi * ((ε / δ) * E) := by unfold StepInA.CRed; ring
      have e2 : p.CSym * Y * (p.CDXi * u) = p.CSym * p.CDXi * (Y * u) := by ring
      have e3 : p.COm * Y * p.Θ * (p.CS * u) = p.Θ * p.COm * p.CS * (Y * u) := by ring
      rw [e1, e2, e3, hp1, hp2]
      unfold StepInA.CLin
      ring
    have hq : ‖sumVec p.n (isoQuadX H K (s • ωstar) E₀ θ)‖ ≤ p.M2 / 2 * (p.CDK * E) ^ 2 := by
      rw [norm_sumVec]
      exact norm_isoQuadX_M2 hSt hd2 hp.M2 (hK.ball_sub θ hθr) hΔ hβ
    have hω' : ‖isoXiOmega H K (s • ωstar) E₀ • sumVec p.n
        (fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ)))‖ ≤
        p.CS * u * (p.CdK * E) := by
      rw [norm_smul, norm_sumVec]
      exact mul_le_mul hXω hdΔ (norm_nonneg _) ((norm_nonneg _).trans hXω)
    have hPn := norm_frameMat_le (hK.tangent_le hθr) (hK.normal θ hθr)
    rw [← norm_sumVec, hid]
    have hP0 := hp.P
    have hCL := hp.CLin
    have hCS := hp.CS
    have hCdK := hp.CdK
    calc _ ≤ ‖frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ isoLinError H K (s • ωstar)
            (isoXi H K (s • ωstar) E₀) (isoXiOmega H K (s • ωstar) E₀) θ)‖ +
          ‖sumVec p.n (isoQuadX H K (s • ωstar) E₀ θ)‖ +
          ‖isoXiOmega H K (s • ωstar) E₀ • sumVec p.n
            (fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ)))‖ :=
          norm_add₃_le
      _ ≤ (p.sK + p.sN) * (2 * (p.CLin * (ε * X))) + p.M2 / 2 * (p.CDK * E) ^ 2 +
          p.CS * u * (p.CdK * E) :=
          add_le_add (add_le_add (NewtonError.norm_mulVec_mulVec_le hPn (hSb θ hθ).2 hlin) hq) hω'
      _ = 2 * p.P * p.CLin * ε * X + p.M2 / 2 * (p.CDK ^ 2 * E ^ 2) +
          p.CS * p.CdK * (u * E) := by unfold StepInA.P; ring
      _ ≤ 2 * p.P * p.CLin * ε * ((p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x) +
            p.M2 / 2 * (p.CDK ^ 2 * (ε * x)) + p.CS * p.CdK * (p.g * (ε * x)) := by
          rw [hp3, hp4]
          refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left hXle (by positivity)) le_rfl)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgd hεx)
              (mul_nonneg hCS hCdK))
      _ = p.CE1 * (ε * x) := by rw [hCE1]; ring
      _ ≤ p.CE * (ε * x) := mul_le_mul_of_nonneg_right (by rw [hCE]; exact le_max_left _ _) hεx
  · -- the energy error
    obtain ⟨-, -, -, hXLd, hXNd⟩ :=
      NewtonErrorAux.border_facts hSet hKN hK.twist hK.energy_le hδ hδ1 h2δ
    have hed := energy_defect hSet hr hK.holo hK.primary hK.real hK𝔅 hGu (r' := r - 2 * δ) hr'
      (by linarith) hXLd hXNd
    have hA : ‖avg (fun θ => fderiv ℂ (fun y => H (K y)) θ
        (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ))‖ ≤
        p.n * (p.sLt * ε + p.Θ * (p.COm * Y)) * (p.c * p.CG * E) := by
      refine hed.2.2 _ _ (fun x' _ => ?_) (fun x' _ =>
        (hbd _ (ofReal_mem_complexStrip hr' x')).2.2.2.2)
      have hθ := ofReal_mem_complexStrip hr' x' (n := p.n)
      refine (hed.1 _ hθ).2.2.trans ?_
      exact mul_le_mul_of_nonneg_left (add_le_add (hHN _ (hsub2 hθ))
        (mul_le_mul hΘ (hΩ _ hθ) (norm_nonneg _) hp.Θ)) hn0
    have hQ : ‖avg (isoQuadH H K (s • ωstar) E₀)‖ ≤ p.Mh2 / 2 * (p.CDK * E) ^ 2 :=
      norm_torusAverage_le_of_strip_bound hr' fun θ hθ =>
        norm_isoQuadH_Mh2 hS hd2H hp.Mh2 (hK.ball_sub θ (hsub2 hθ)) (hbd θ hθ).2.1 hβ
    rw [IsoNewtonErrorSharp.energyAverage_sub_eq_of hS hAd hδ hδ1 h2δ hcorr]
    have hcG : 0 ≤ p.c * p.CG := mul_nonneg hp.c hp.CG
    have hk1 : 0 ≤ p.κ - 1 := by linarith
    have hW1 : γ * δ ^ (p.κ - 1) ≤ p.γb * p.δ ^ (p.κ - 1) := by
      have := pow_mul_rpow_le (j := p.κ - 1) 1 hγ hγb hδ hδD hk1
      simpa using this
    have hW2 : γ ^ 2 * δ ^ (2 * p.κ) ≤ p.γb * p.δ ^ (p.κ - 1) * p.g := by
      have h1 := pow_mul_rpow_le (j := 2 * p.κ - 1) 2 hγ hγb hδ hδD (by linarith)
      have h2 : δ ^ (2 * p.κ) ≤ δ ^ (2 * p.κ - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      have h3 : γ ^ 2 * δ ^ (2 * p.κ) ≤ γ ^ 2 * δ ^ (2 * p.κ - 1) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : p.γb * p.δ ^ (p.κ - 1) * p.g = p.γb ^ 2 * p.δ ^ (2 * p.κ - 1) := by
        have hD := hp.δ
        unfold StepInA.g
        rw [show 2 * p.κ - 1 = (p.κ - 1) + p.κ by ring, Real.rpow_add hD]
        ring
      rw [h4]
      exact h3.trans h1
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add hA hQ
      _ = p.n * p.sLt * (p.c * p.CG) * (ε * E) +
            p.n * p.Θ * p.COm * (p.c * p.CG) * (Y * E) + p.Mh2 / 2 * (p.CDK ^ 2 * E ^ 2) := by ring
      _ ≤ p.n * p.sLt * (p.c * p.CG) * ((p.γb * p.δ ^ (p.κ - 1) * p.g) * (ε * x)) +
            p.n * p.Θ * p.COm * (p.c * p.CG) * ((p.γb * p.δ ^ (p.κ - 1)) * (ε * x)) +
            p.Mh2 / 2 * (p.CDK ^ 2 * (ε * x)) := by
          rw [hp3, hp5, hp6]
          have hnL : 0 ≤ (p.n : ℝ) * p.sLt * (p.c * p.CG) := mul_nonneg (mul_nonneg hn0 hp.sLt) hcG
          have hnΘ : 0 ≤ (p.n : ℝ) * p.Θ * p.COm * (p.c * p.CG) :=
            mul_nonneg (mul_nonneg (mul_nonneg hn0 hp.Θ) hp.COm) hcG
          exact add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW2 hεx) hnL)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW1 hεx) hnΘ)) le_rfl
      _ = p.CE2 * (ε * x) := by unfold StepInA.CE2; ring
      _ ≤ p.CE * (ε * x) := mul_le_mul_of_nonneg_right (by rw [hCE]; exact le_max_right _ _) hεx

end KAM.Iso.Sharp2.RouteA

end
