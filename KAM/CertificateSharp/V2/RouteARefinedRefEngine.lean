/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefinedEngine
public import KAM.CertificateSharp.V2.RouteARefinedRef

/-!
# The engine of stage 2 with lever L8′

`routeARefinedR`: as `routeARefined`, the test computes the refined bounds from the certificate's
models, and then runs `refinedCoreR`. `routeAV2'` adds it to the routes of `routeAV2`, which is
unchanged; `Sum.inl ()` is still the landed certifier.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The test of stage 2 with lever L8′. -/
def refinedRefTest (c : TorusCertificate n α) (w : RefinedWitR) : Bool :=
  checkHamClaim c w.base.R && checkFrameMajorants c (w.base.R.frame c.freqBox) &&
    refinedCoreR n c.params c.freqBox w

/-- **The engine of route A at the refined data, with lever L8′.** -/
def routeARefinedR : EngineV2 where
  Wit := RefinedWitR
  test := fun c w => refinedRefTest c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedRefTest, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedCoreR_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω) hc

/-- The minimum over the landed sharp engine and the three forms of route A. -/
def routeAV2' : EngineV2 := sharpV2.orElse ((routeAFrozen.orElse routeARefined).orElse routeARefinedR)

/-- **v2 is never worse than the landed certifier**, at the combined engine. -/
theorem checkTorusCertificateV2_routeAV2'_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeAV2' c (Sum.inl ()) = checkTorusCertificateSharp c := rfl

end KAM.CertificateSharp.V2

end
