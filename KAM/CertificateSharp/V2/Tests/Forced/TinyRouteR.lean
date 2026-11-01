/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyRouteA

/-!
# Route A with lever L8′ on the forced toy `Tiny`, in the kernel

`refinedWitR`: the refined witness of `TinyRouteA` at `X⋆ = (191)` with the lever's
budgets `b_F = (1 / 1000)`, `b_T = (1 / 1000)` (found by the compiled `refinedCoreR`; at route A's
own `X⋆` the lever's torsion budget does not close). `refinedR_passes` is the whole v2 certifier
at `routeV2All` with the witness of `routeARefinedR`, and `refinedR_torus` the certified torus.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The witness of route A with lever L8′. -/
def refinedWitR : RefinedWitR where
  base := { refinedWit with core := { refinedWit.core with Xs := (191) } }
  bF := (1 / 1000)
  bT := (1 / 1000)

theorem refinedR_sites : sitesOk (refinedWitR.base.num 2 cert.params cert.freqBox)
    refinedWitR.base.core.J cert.freqBox refinedWitR.base.κ cert.params.γ refinedWitR.base.sites =
      true := by decide +kernel

theorem refinedR_core : refinedCoreR 2 cert.params cert.freqBox refinedWitR = true :=
  refinedCoreR_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refinedR_sites (by decide +kernel) (by decide +kernel)

/-- **The forced toy through `routeV2All`** with lever L8′. -/
theorem refinedR_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inr refinedWitR)))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aRefinedR]
  refine (checkV2_eq routeARefinedR cert refinedWitR).trans ?_
  rw [base_ok, Bool.true_and]
  refine (routeARefinedR_test cert refinedWitR).trans ?_
  have h1 : checkHamClaim cert refinedWitR.base.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedWitR.base.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedWitR.base.R &&
    checkFrameMajorants cert (refinedWitR.base.R.frame cert.freqBox) &&
    refinedCoreR 2 cert.params cert.freqBox refinedWitR) = true
  rw [h1, h2, refinedR_core]
  rfl

theorem refinedR_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedR_passes freq dio

end KAM.CertificateSharp.V2.Forced.Tiny

end
