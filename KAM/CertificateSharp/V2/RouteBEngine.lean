/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBFrozen
public import KAM.CertificateSharp.V2.RouteARefinedEngine

/-!
# The engines of route B and the combined v2 engine

* `routeBRefined`: the refined bounds are computed from the certificate's models (the disc pass
  `checkHamClaim`, the frame majorants `checkFrameMajorants` of C4), then `refinedBCore`;
* `routeABV2`: the minimum over the landed sharp engine, the two forms of route A and the two
  forms of route B. The witness names the route; `checkTorusCertificateV2 routeABV2 c (Sum.inl ())`
  is the landed certifier (`checkTorusCertificateV2_routeABV2_sharp`, `rfl`). The engine
  `routeAV2` of SHARP2-C6 is unchanged.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- The test of route B at the refined data. -/
def refinedBTest (c : TorusCertificate n α) (w : RefinedBWit) : Bool :=
  checkHamClaim c w.R && checkFrameMajorants c (w.R.frame c.freqBox) &&
    refinedBCore n c.params c.freqBox w

/-- **The engine of route B at the refined data.** -/
def routeBRefined : EngineV2 where
  Wit := RefinedBWit
  test := fun c w => refinedBTest c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedBTest, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedBCore_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω)
      hc

/-- The minimum over the landed sharp engine, route A (frozen, refined) and route B (frozen,
refined). -/
def routeABV2 : EngineV2 :=
  sharpV2.orElse ((routeAFrozen.orElse routeARefined).orElse (routeBFrozen.orElse routeBRefined))

/-- **v2 is never worse than the landed certifier**, at the combined engine of routes A and B. -/
theorem checkTorusCertificateV2_routeABV2_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeABV2 c (Sum.inl ()) = checkTorusCertificateSharp c := rfl

/-- Route A's witnesses run unchanged inside the combined engine. -/
theorem checkTorusCertificateV2_routeABV2_routeA (c : TorusCertificate n α)
    (w : (routeAFrozen.orElse routeARefined).Wit) :
    checkTorusCertificateV2 routeABV2 c (Sum.inr (Sum.inl w)) =
      checkTorusCertificateV2 (routeAFrozen.orElse routeARefined) c w := rfl

end KAM.CertificateSharp.V2

end
