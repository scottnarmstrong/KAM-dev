/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.L1.EntryCorrection
public import KAM.Sharp2.L1.EntryError
public import KAM.Iso.Sharp2.RouteA.NewtonError
public import KAM.Sharp2.RouteA.NewtonError
public import KAM.Iso.Sharp.NewtonError
import KAM.Strip.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The new errors of the isoenergetic ℓ¹ entry step (package B10c)

`iso_entry_newton_error`: B9's `KAM.Iso.Sharp2.RouteA.iso_newton_error_boundsA` with the entry
constants: the solves of `iso_entry_correction_bounds`, the Lagrangian defect bound `C^K_Ω` of
`KAM.Sharp2.L1.entry_lagrange_le_of`, and `C_ξᴸ` in the energy branch.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Sharp2.L1
  KAM.Iso.Sharp

variable {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ωstar : Fin n → ℝ} {τ M σω ν γ : ℝ}

/-- The new errors of the isoenergetic ℓ¹ entry step, for a bite `δ ≤ p.δ`. -/
theorem iso_entry_newton_error {p : StepInA} {Ed : EntryA} (hp : p.Pos) (hE : Ed.Wf)
    (hiso : p.iso = true) (hpn : p.n = n)
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
    (hca : cb * b ^ (-p.κ) ≤ p.ca * δ ^ (-p.κ)) (hD : EntryData Ed H K (s • ωstar) r δ ε)
    (hβ : Ent.CDK p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ))) < β)
    (hsym : Ent.CSym p Ed * (ε / (γ * δ ^ (p.κ + 1))) ≤ 1 / 2) :
    (∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoCorrection H K (s • ωstar) E₀ θ‖ ≤
      Ent.CDK p Ed * (ε / (γ ^ 2 * δ ^ (2 * p.κ)))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ Ent.COmK p Ed * (ε / (γ * δ ^ (p.κ + 1)))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖invarianceError H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ))
          (isoNewS H K ωstar E₀ s • ωstar) θ‖ ≤
        Ent.CE p Ed * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ)))) ∧
    ‖KAM.Iso.energyAverage H (isoNewtonMap H K ωstar E₀ s (r - 2 * δ)) - (E₀ : ℂ)‖ ≤
      Ent.CE p Ed * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) := by
  have hk := Ent.nonneg hp hE
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
  obtain ⟨⟨hXω, -⟩, hbd, -⟩ := iso_entry_correction_bounds hp hE hiso rfl hS hd1 hγb hω hK hδ hδD
    h2δ hεδ hΘ hHY hc hcb hbr hca hD
  have hΩ : ∀ θ ∈ complexStrip p.n (r - 2 * δ),
      ‖lagrangeMat K θ‖ ≤ Ent.COmK p Ed * (ε / (γ * δ ^ (p.κ + 1))) :=
    entry_lagrange_le_of hp hE rfl hSt hγb hω hr hε0 hK.holo hK.primary hK𝔅 hGu hηNd hHN hδ hδD h2δ
      hc hD.l1EtaN hD.gam0
  have hsy : ∀ θ ∈ complexStrip p.n (r - 2 * δ),
      ‖symDefect K θ‖ ≤ Ent.CSym p Ed * (ε / (γ * δ ^ (p.κ + 1))) := by
    intro θ hθ
    have := norm_symDefect_le (hK.gram θ (hsub2 hθ)).1 (hK.gram θ (hsub2 hθ)).2 (hΩ θ hθ)
    unfold Ent.CSym
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
  have hgoal : Ent.CE p Ed * ε ^ 2 / (γ ^ 4 * δ ^ (2 * (2 * p.κ))) = Ent.CE p Ed * (ε * x) := by
    rw [hxd, mul_div_assoc]
    congr 1
    rw [sq]
    ring
  have hCE1 : Ent.CE1 p Ed = 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * Ent.CLin p Ed +
      p.M2 / 2 * Ent.CDK p Ed ^ 2 + p.g * Ent.CS p Ed * Ent.CdK p Ed := by simp [Ent.CE1, hiso]
  have hCE : Ent.CE p Ed = max (Ent.CE1 p Ed) (Ent.CE2 p Ed) := by simp [Ent.CE, hiso]
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
        (isoXiOmega H K (s • ωstar) E₀) θ‖ ≤ Ent.CLin p Ed * (ε * X) := by
      refine (norm_isoLinError_le H K (s • ωstar) _ _ θ).trans ?_
      have h1 := mul_le_mul hred hxi (norm_nonneg _) ((norm_nonneg _).trans hred)
      have h2 := mul_le_mul (hsy θ hθ) hdξ (norm_nonneg _) (mul_nonneg hk.CSym
        (div_nonneg hε0 (by positivity)))
      have h3 := mul_le_mul (mul_le_mul (hΩ θ hθ) hΘ (norm_nonneg _) ((norm_nonneg _).trans
        (hΩ θ hθ))) hXω (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans (hΩ θ hθ)) hp.Θ)
      refine (add_le_add (add_le_add h1 h2) h3).trans (le_of_eq ?_)
      have e1 : (p.n : ℝ) * max p.sNt (p.sLt + 2 * p.sN) * ε / δ * (Ent.CXi p Ed * E) =
          p.CRed * Ent.CXi p Ed * ((ε / δ) * E) := by unfold StepInA.CRed; ring
      have e2 : Ent.CSym p Ed * Y * (Ent.CDXi p Ed * u) =
          Ent.CSym p Ed * Ent.CDXi p Ed * (Y * u) := by
        ring
      have e3 : Ent.COmK p Ed * Y * p.Θ * (Ent.CS p Ed * u) =
          p.Θ * Ent.COmK p Ed * Ent.CS p Ed * (Y * u) := by ring
      rw [e1, e2, e3, hp1, hp2]
      unfold Ent.CLin
      ring
    have hq : ‖sumVec p.n (isoQuadX H K (s • ωstar) E₀ θ)‖ ≤
        p.M2 / 2 * (Ent.CDK p Ed * E) ^ 2 := by
      rw [norm_sumVec]
      exact norm_isoQuadX_M2 hSt hd2 hp.M2 (hK.ball_sub θ hθr) hΔ hβ
    have hω' : ‖isoXiOmega H K (s • ωstar) E₀ • sumVec p.n
        (fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ)))‖ ≤
        Ent.CS p Ed * u * (Ent.CdK p Ed * E) := by
      rw [norm_smul, norm_sumVec]
      exact mul_le_mul hXω hdΔ (norm_nonneg _) ((norm_nonneg _).trans hXω)
    have hPn := norm_frameMat_le (hK.tangent_le hθr) (hK.normal θ hθr)
    rw [← norm_sumVec, hid]
    have hP0 := hp.P
    have hCL := hk.CLin
    have hCS := hk.CS
    have hCdK := hk.CdK
    calc _ ≤ ‖frameMat K θ *ᵥ ((sMat K θ)⁻¹ *ᵥ isoLinError H K (s • ωstar)
            (isoXi H K (s • ωstar) E₀) (isoXiOmega H K (s • ωstar) E₀) θ)‖ +
          ‖sumVec p.n (isoQuadX H K (s • ωstar) E₀ θ)‖ +
          ‖isoXiOmega H K (s • ωstar) E₀ • sumVec p.n
            (fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ)))‖ :=
          norm_add₃_le
      _ ≤ (p.sK + p.sN) * (2 * (Ent.CLin p Ed * (ε * X))) + p.M2 / 2 * (Ent.CDK p Ed * E) ^ 2 +
          Ent.CS p Ed * u * (Ent.CdK p Ed * E) :=
          add_le_add (add_le_add (NewtonError.norm_mulVec_mulVec_le hPn (hSb θ hθ).2 hlin) hq) hω'
      _ = 2 * p.P * Ent.CLin p Ed * ε * X + p.M2 / 2 * (Ent.CDK p Ed ^ 2 * E ^ 2) +
          Ent.CS p Ed * Ent.CdK p Ed * (u * E) := by unfold StepInA.P; ring
      _ ≤ 2 * p.P * Ent.CLin p Ed * ε * ((p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x) +
            p.M2 / 2 * (Ent.CDK p Ed ^ 2 * (ε * x)) +
            Ent.CS p Ed * Ent.CdK p Ed * (p.g * (ε * x)) := by
          rw [hp3, hp4]
          refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left hXle (by positivity)) le_rfl)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgd hεx)
              (mul_nonneg hCS hCdK))
      _ = Ent.CE1 p Ed * (ε * x) := by rw [hCE1]; ring
      _ ≤ Ent.CE p Ed * (ε * x) :=
          mul_le_mul_of_nonneg_right (by rw [hCE]; exact le_max_left _ _) hεx
  · -- the energy error
    obtain ⟨-, -, -, hXLd, hXNd⟩ :=
      NewtonErrorAux.border_facts hSet hKN hK.twist hK.energy_le hδ hδ1 h2δ
    have hed := energy_defect hSet hr hK.holo hK.primary hK.real hK𝔅 hGu (r' := r - 2 * δ) hr'
      (by linarith) hXLd hXNd
    have hA : ‖avg (fun θ => fderiv ℂ (fun y => H (K y)) θ
        (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ))‖ ≤
        p.n * (p.sLt * ε + p.Θ * (Ent.COmK p Ed * Y)) * (Ent.CXiL p Ed * E) := by
      refine hed.2.2 _ _ (fun x' _ => ?_) (fun x' _ =>
        (hbd _ (ofReal_mem_complexStrip hr' x')).2.2.2.2)
      have hθ := ofReal_mem_complexStrip hr' x' (n := p.n)
      refine (hed.1 _ hθ).2.2.trans ?_
      exact mul_le_mul_of_nonneg_left (add_le_add (hHN _ (hsub2 hθ))
        (mul_le_mul hΘ (hΩ _ hθ) (norm_nonneg _) hp.Θ)) hn0
    have hQ : ‖avg (isoQuadH H K (s • ωstar) E₀)‖ ≤ p.Mh2 / 2 * (Ent.CDK p Ed * E) ^ 2 :=
      norm_torusAverage_le_of_strip_bound hr' fun θ hθ =>
        norm_isoQuadH_Mh2 hS hd2H hp.Mh2 (hK.ball_sub θ (hsub2 hθ)) (hbd θ hθ).2.1 hβ
    rw [IsoNewtonErrorSharp.energyAverage_sub_eq_of hS hAd hδ hδ1 h2δ hcorr]
    have hcG : 0 ≤ Ent.CXiL p Ed := hk.CXiL
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
      _ = p.n * p.sLt * Ent.CXiL p Ed * (ε * E) +
            p.n * p.Θ * Ent.COmK p Ed * Ent.CXiL p Ed * (Y * E) +
            p.Mh2 / 2 * (Ent.CDK p Ed ^ 2 * E ^ 2) := by ring
      _ ≤ p.n * p.sLt * Ent.CXiL p Ed * ((p.γb * p.δ ^ (p.κ - 1) * p.g) * (ε * x)) +
            p.n * p.Θ * Ent.COmK p Ed * Ent.CXiL p Ed * ((p.γb * p.δ ^ (p.κ - 1)) * (ε * x)) +
            p.Mh2 / 2 * (Ent.CDK p Ed ^ 2 * (ε * x)) := by
          rw [hp3, hp5, hp6]
          have hnL : 0 ≤ (p.n : ℝ) * p.sLt * Ent.CXiL p Ed := mul_nonneg (mul_nonneg hn0 hp.sLt) hcG
          have hnΘ : 0 ≤ (p.n : ℝ) * p.Θ * Ent.COmK p Ed * Ent.CXiL p Ed :=
            mul_nonneg (mul_nonneg (mul_nonneg hn0 hp.Θ) hk.COmK) hcG
          exact add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW2 hεx) hnL)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW1 hεx) hnΘ)) le_rfl
      _ = Ent.CE2 p Ed * (ε * x) := by unfold Ent.CE2; ring
      _ ≤ Ent.CE p Ed * (ε * x) :=
          mul_le_mul_of_nonneg_right (by rw [hCE]; exact le_max_right _ _) hεx

end KAM.Iso.Sharp2.L1

end
