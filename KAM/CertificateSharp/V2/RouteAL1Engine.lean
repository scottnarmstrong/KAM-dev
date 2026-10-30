/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1
public import KAM.CertificateSharp.V2.RouteARefinedRefEngine

/-!
# The engine of route A with the ℓ¹ entry (package C6L1)

`routeAL1`: the test computes, from the certificate's own models, the refined bounds (C6's disc
pass `checkHamClaim` and C4's majorants `checkFrameMajorants`) and the ℓ¹ data of the torus
(`checkL1Claim`), and then runs `l1Core`. Its soundness concludes the landed `CertifiedTorus c ω*`
from a passing test, `FreqEncloses` and `IsDiophantine` only.

`routeAV2L1` adds it to the routes of `routeAV2'` (C6L8), which is unchanged; `Sum.inl ()` is still
the landed certifier (`checkTorusCertificateV2_routeAV2L1_sharp`, by `rfl`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.L1

open KAM KAM.Torus KAM.Certificate CertArith KAM.CertificateSharp.V2

variable {n : ℕ} {α : Type} [CertArith α]

/-- The test of route A with the ℓ¹ entry. -/
def l1Test (c : TorusCertificate n α) (w : L1Wit) : Bool :=
  checkHamClaim c w.base.R && checkFrameMajorants c (w.base.R.frame c.freqBox) &&
    checkL1Claim c w.L && l1Core n c.params c.freqBox w

/-- **The engine of route A with the ℓ¹ entry.** -/
def routeAL1 : EngineV2 where
  Wit := L1Wit
  test := fun c w => l1Test c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [l1Test, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hH, hF⟩, hL⟩, hc⟩ := h
    exact l1Core_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω)
      (checkL1Claim_sound B hω hdio hL) hc

end KAM.CertificateSharp.V2.L1

namespace KAM.CertificateSharp.V2

open KAM.Certificate

variable {n : ℕ} {α : Type} [CertArith α]

/-- The minimum over the landed sharp engine, the three forms of route A and route A with the ℓ¹
entry. -/
def routeAV2L1 : EngineV2 :=
  sharpV2.orElse (((routeAFrozen.orElse routeARefined).orElse routeARefinedR).orElse L1.routeAL1)

/-- **v2 is never worse than the landed certifier**, at the combined engine. -/
theorem checkTorusCertificateV2_routeAV2L1_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeAV2L1 c (Sum.inl ()) = checkTorusCertificateSharp c := rfl

end KAM.CertificateSharp.V2

end
