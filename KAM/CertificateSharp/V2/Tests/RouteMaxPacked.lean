/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroPacked

/-!
# The packed branch of `routeMax` is reachable

The forced toy `Micro` with the production decoder in `cfgLow` (`MicroP.cert`,
`Tests/Forced/MicroPackedData.lean`) passes the certifier with every route and every base at the
packed base `.torsR` and the packed route `.aPacked` (`MicroP.packed_passes`); this module restates
it at `routeMax`'s names, and its engine-level form: the branch `.aPacked` of `routeMax` runs the test
of `Packed.routeARefinedPacked` (`checkV2With_routeMax_aPacked`, `rfl`). The other branches are in
`Tests/RouteMax.lean`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.CertificateSharp

/-- **The packed branch, at the packed base.** -/
theorem microP_routeMax_aPacked :
    checkTorusCertificateMax Forced.MicroP.cert (.torsR Forced.MicroP.books)
      (.aPacked Forced.MicroP.books Forced.MicroP.wit) = true :=
  Forced.MicroP.packed_passes

/-- The same, as the packed certifier of `Packed.checkV2With_packed_sound`. -/
theorem microP_packed_certifier :
    checkV2With (Packed.torsRBase Forced.MicroP.bk Forced.MicroP.mm Forced.MicroP.rb
        Forced.MicroP.tm Forced.MicroP.rm)
      (Packed.routeARefinedPacked Forced.MicroP.bk Forced.MicroP.mm Forced.MicroP.rb
        Forced.MicroP.tm Forced.MicroP.rm) Forced.MicroP.cert Forced.MicroP.wit = true :=
  (checkTorusCertificateMax_packed _ Forced.MicroP.books _).symm.trans microP_routeMax_aPacked

/-- **The torus of `Micro` through the packed branch of `routeMax`.** -/
theorem micro_routeMax_packed_torus : CertifiedTorus Forced.Micro.cert Forced.Micro.ωstar :=
  (Forced.certifiedTorus_cfgLow Forced.Micro.cert _ Forced.Micro.ωstar).mp
    (checkTorusCertificateMax_sound microP_routeMax_aPacked Forced.MicroP.freq Forced.MicroP.dio)

end KAM.CertificateSharp.V2

end
