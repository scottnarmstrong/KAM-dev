/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Check
public import KAM.CertificateSharp.V2.RouteAll

/-!
# The hybrid engine (package C8c)

* `hybrid_certified`: `CertifiedTorus c ω*` for the base certificate from a passing hybrid check,
  with the outer displacement `base.params.disp ≥ max {dinf, d_ω} + disp₁` (format v1 H4) and the
  room of the ray `disp < (σω − s) freqNormLo` (`ray_lt_of_disp`);
* `routeHybrid`: the engine; its test is the Hamiltonian pass and the frame majorants of the base
  claim `w.R0` (as `routeARefinedR`) and `checkHybrid`;
* `routeV2Hyb`: `routeV2All` with the hybrid engine as a further `orElse`. `Sum.inl ()` is still
  the landed certifier (`checkTorusCertificateV2_routeV2Hyb_sharp`, `rfl`), a witness `Sum.inr w`
  of `routeV2All` is `Sum.inr (Sum.inl w)` here, and `Sum.inr (Sum.inr w)` names the hybrid route.
-/

@[expose] public section

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate CertArith KAM.CertificateSharp.V2

variable {n : ℕ} {α : Type} [CertArith α]

/-- **The certified torus of the base certificate from the hybrid check.** -/
theorem hybrid_certified [LawfulCertArith α] (c : TorusCertificate n α) (w : HybWit)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R0) (hF : FrameFacts c w.R0 ωstar) (h : checkHybrid c w = true) :
    CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  have hT : transferOk n c.params c.freqBox w = true := by
    simp only [checkHybrid, Bool.and_eq_true] at h
    exact h.1.1
  have T := transferOk_sound hT
  obtain ⟨Kinf, sinf, h1, -, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    checkHybrid_sound c w hω hdio B hH hF h
  have hd : max (w.step.cl.dinf : ℝ) w.step.dw + w.p1.disp ≤ c.params.disp := by
    exact_mod_cast T.disp
  have hd1 : (w.step.cl.dinf : ℝ) + w.p1.disp ≤ c.params.disp :=
    (add_le_add (le_max_left _ _) le_rfl).trans hd
  have hd2 : (w.step.dw : ℝ) + w.p1.disp ≤ c.params.disp :=
    (add_le_add (le_max_right _ _) le_rfl).trans hd
  have hroom : (c.params.disp : ℝ) < ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖ := by
    have hs := B.hs
    have hlen : c.freqBox.length = n := by
      simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hs
      exact hs.1
    have hle := freqNormLo_le_norm hlen hω
    have h3' : (c.params.disp : ℝ) <
        ((c.params.σω : ℝ) - c.params.s) * (freqNormLo c.freqBox : ℝ) := by
      exact_mod_cast T.room
    have hp : (0 : ℝ) ≤ (c.params.σω : ℝ) - c.params.s := by linarith [S.hsσ]
    exact h3'.trans_le (mul_le_mul_of_nonneg_left hle hp)
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd2), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd1, h11.trans hd2⟩

/-- The test of the hybrid route: the base claim and the hybrid check. -/
def hybTest (c : TorusCertificate n α) (w : HybWit) : Bool :=
  checkHamClaim c w.R0 && checkFrameMajorants c (w.R0.frame c.freqBox) && checkHybrid c w

/-- **The hybrid engine** (the certified first step, route A′ at the restart). -/
def routeHybrid : EngineV2 where
  Wit := HybWit
  test := fun c w => hybTest c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [hybTest, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact hybrid_certified c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω) hc

/-- The certifier at the hybrid route: the landed sub-checks and the hybrid test. -/
theorem checkTorusCertificateV2_routeHybrid (c : TorusCertificate n α) (w : HybWit) :
    checkTorusCertificateV2 routeHybrid c w = (landedBase.check c && hybTest c w) := rfl

/-- `routeV2All` with the hybrid route. -/
def routeV2Hyb : EngineV2 :=
  sharpV2.orElse
    (((((routeAFrozen.orElse routeARefined).orElse routeARefinedR).orElse L1.routeAL1).orElse
      (routeBFrozen.orElse routeBRefined)).orElse routeHybrid)

/-- **v2 is never worse than the landed certifier**, at the engine with the hybrid route. -/
theorem checkTorusCertificateV2_routeV2Hyb_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeV2Hyb c (Sum.inl ()) = checkTorusCertificateSharp c := rfl

/-- The witnesses of `routeV2All` keep their meaning. -/
theorem checkTorusCertificateV2_routeV2Hyb_all (c : TorusCertificate n α)
    (w : (((FrozenWit ⊕ RefinedWit) ⊕ RefinedWitR) ⊕ L1.L1Wit) ⊕ (RunBWit ⊕ RefinedBWit)) :
    checkTorusCertificateV2 routeV2Hyb c (Sum.inr (Sum.inl w)) =
      checkTorusCertificateV2 routeV2All c (Sum.inr w) := rfl

/-- The witness `Sum.inr (Sum.inr w)` names the hybrid route. -/
theorem checkTorusCertificateV2_routeV2Hyb_hybrid (c : TorusCertificate n α) (w : HybWit) :
    checkTorusCertificateV2 routeV2Hyb c (Sum.inr (Sum.inr w)) =
      checkTorusCertificateV2 routeHybrid c w := rfl

end KAM.CertificateSharp.Hybrid

end
