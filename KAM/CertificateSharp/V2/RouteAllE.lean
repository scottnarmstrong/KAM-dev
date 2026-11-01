/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAllLN
public import KAM.CertificateSharp.V2.RouteBE

/-!
# The v2 engine with every route and `routeBRefinedE`

`routeV2AllE` is `routeV2AllLN` with `routeBRefinedE` as a further `orElse`; `routeV2All` and
`routeV2AllLN` are unchanged. A witness `w` of `routeV2AllLN` is the witness `Sum.inl w` here, and
runs the same check, by `rfl`; the witness `Sum.inr w` selects `routeBRefinedE`, at `RefinedBWit`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

variable {n : ℕ} {α : Type} [CertArith α]

/-- `routeV2AllLN` and route B with the gradient bound in the energy row. -/
def routeV2AllE : EngineV2 := routeV2AllLN.orElse routeBRefinedE

/-- The witnesses of `routeV2AllLN` run unchanged. -/
theorem checkTorusCertificateV2_routeV2AllE_all (c : TorusCertificate n α)
    (w : routeV2AllLN.Wit) :
    checkTorusCertificateV2 routeV2AllE c (Sum.inl w) =
      checkTorusCertificateV2 routeV2AllLN c w := rfl

/-- **v2 is never worse than the landed certifier** at this engine. -/
theorem checkTorusCertificateV2_routeV2AllE_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeV2AllE c (Sum.inl (Sum.inl (Sum.inl ()))) =
      checkTorusCertificateSharp c := rfl

/-- The witness of route B with the gradient bound in the energy row. -/
theorem checkTorusCertificateV2_routeV2AllE_bE (c : TorusCertificate n α) (w : RefinedBWit) :
    checkTorusCertificateV2 routeV2AllE c (Sum.inr w) =
      checkTorusCertificateV2 routeBRefinedE c w := rfl

end KAM.CertificateSharp.V2

end
