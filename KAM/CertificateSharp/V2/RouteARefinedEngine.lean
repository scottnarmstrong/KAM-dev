/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefined
public import KAM.CertificateSharp.V2.HamClaim
public import KAM.CertificateSharp.Frame.Majorants

/-!
# The engine of stage 2

`routeARefined`: the test computes the refined bounds from the certificate's models (the disc pass
`checkHamClaim`, the majorants `checkFrameMajorants` of C4) and then runs `refinedCore`. `routeAV2`
is the minimum over the landed sharp engine and the two forms of route A: the witness names the
route, and `checkTorusCertificateV2 routeAV2 c (Sum.inl ())` is the landed certifier.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The frame majorants of the claim; `|ω*|` is read from the box. -/
def RefClaim.frame (R : RefClaim) (box : FreqBox) : FrameBounds :=
  ⟨R.bL, R.bN, R.bNt, R.bT, freqNormUp box⟩

/-- The test of stage 2. -/
def refinedTest (c : TorusCertificate n α) (w : RefinedWit) : Bool :=
  checkHamClaim c w.R && checkFrameMajorants c (w.R.frame c.freqBox) &&
    refinedCore n c.params c.freqBox w

/-- The frame majorants of C4 as `FrameFacts`. -/
theorem frameFacts_of [LawfulCertArith α] {c : TorusCertificate n α} {R : RefClaim}
    {ωstar : Fin n → ℝ} (B : BaseFacts c ωstar) (h : checkFrameMajorants c (R.frame c.freqBox) = true)
    (hω : FreqEncloses n c.freqBox ωstar) : FrameFacts c R ωstar := by
  obtain ⟨h1, h2, h3, h4, -⟩ := checkFrameMajorants_sound B.hs B.hH B.hEm h hω
  exact ⟨h1, h2, h3, h4⟩

/-- **The engine of route A at the refined data.** -/
def routeARefined : EngineV2 where
  Wit := RefinedWit
  test := fun c w => refinedTest c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTest, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedCore_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω) hc

/-- The minimum over the landed sharp engine and the two forms of route A. -/
def routeAV2 : EngineV2 := sharpV2.orElse (routeAFrozen.orElse routeARefined)

/-- **v2 is never worse than the landed certifier**, at the combined engine. -/
theorem checkTorusCertificateV2_routeAV2_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeAV2 c (Sum.inl ()) = checkTorusCertificateSharp c := rfl

end KAM.CertificateSharp.V2

end
