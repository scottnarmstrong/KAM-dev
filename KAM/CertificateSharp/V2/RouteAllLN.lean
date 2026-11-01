/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAll
public import KAM.CertificateSharp.V2.RouteBLN

/-!
# The v2 engine with every route and `routeBRefinedLN`

`routeV2AllLN` is `routeV2All` with `routeBRefinedLN` as a further `orElse`; `routeV2All` itself is
unchanged. A witness `w` of `routeV2All` is the witness `Sum.inl w` here, and runs the same check,
by `rfl`; the witness `Sum.inr w` selects `routeBRefinedLN`, at the same `RefinedBWit`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

variable {n : ℕ} {α : Type} [CertArith α]

/-- `routeV2All` and route B without the torsion majorant. -/
def routeV2AllLN : EngineV2 := routeV2All.orElse routeBRefinedLN

/-- The witnesses of `routeV2All` run unchanged. -/
theorem checkTorusCertificateV2_routeV2AllLN_all (c : TorusCertificate n α) (w : routeV2All.Wit) :
    checkTorusCertificateV2 routeV2AllLN c (Sum.inl w) = checkTorusCertificateV2 routeV2All c w :=
  rfl

/-- **v2 is never worse than the landed certifier** at this engine. -/
theorem checkTorusCertificateV2_routeV2AllLN_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeV2AllLN c (Sum.inl (Sum.inl ())) =
      checkTorusCertificateSharp c := rfl

/-- The witness of route B without the torsion majorant. -/
theorem checkTorusCertificateV2_routeV2AllLN_bLN (c : TorusCertificate n α) (w : RefinedBWit) :
    checkTorusCertificateV2 routeV2AllLN c (Sum.inr w) =
      checkTorusCertificateV2 routeBRefinedLN c w := rfl

end KAM.CertificateSharp.V2

end
