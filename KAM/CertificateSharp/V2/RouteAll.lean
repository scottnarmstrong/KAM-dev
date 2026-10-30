/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Engine
public import KAM.CertificateSharp.V2.RouteBEngine

/-!
# The v2 engine with every route

`routeV2All` chains the landed sharp engine, the four forms of route A and the two forms of route B.
The engines `routeAV2`, `routeAV2'`, `routeAV2L1` and `routeABV2` are unchanged, and
`checkTorusCertificateV2 routeV2All c (Sum.inl ())` is the landed certifier
(`checkTorusCertificateV2_routeV2All_sharp`, `rfl`).

**The witness names the route; the certifier tries no other.** A generator picks the route and
emits the term of the last column, with `w` of the type of the second:

| Engine | `w` | Witness of `routeV2All` |
|---|---|---|
| `sharpV2` | `Unit` | `Sum.inl ()` |
| `routeAFrozen` | `FrozenWit` | `Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl w))))` |
| `routeARefined` | `RefinedWit` | `Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr w))))` |
| `routeARefinedR` | `RefinedWitR` | `Sum.inr (Sum.inl (Sum.inl (Sum.inr w)))` |
| `L1.routeAL1` | `L1.L1Wit` | `Sum.inr (Sum.inl (Sum.inr w))` |
| `routeBFrozen` | `RunBWit` | `Sum.inr (Sum.inr (Sum.inl w))` |
| `routeBRefined` | `RefinedBWit` | `Sum.inr (Sum.inr (Sum.inr w))` |

Each row is a theorem below, by `rfl`: the certifier at that witness is the certifier of that
engine. The nesting keeps the older engines' witnesses: a witness `Sum.inr w` of `routeAV2L1` is
`Sum.inr (Sum.inl w)` here, and the witnesses `Sum.inl ()` and `Sum.inr (Sum.inr w)` of `routeABV2`
are the same terms here.

`routeARefinedR` is route A's lever L8′ and `L1.routeAL1` its ℓ¹ entry. Route B asks `ρ ≤ 1`
(`NumB.Wf.ρ_le`), so its two rows reject a certificate on a wider strip.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

variable {n : ℕ} {α : Type} [CertArith α]

/-- The minimum over the landed sharp engine, route A (frozen, refined, L8′, ℓ¹ entry) and route B
(frozen, refined). The module docstring lists the witness that selects each route. -/
def routeV2All : EngineV2 :=
  sharpV2.orElse
    ((((routeAFrozen.orElse routeARefined).orElse routeARefinedR).orElse L1.routeAL1).orElse
      (routeBFrozen.orElse routeBRefined))

/-- **v2 is never worse than the landed certifier**, at the engine with every route. -/
theorem checkTorusCertificateV2_routeV2All_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeV2All c (Sum.inl ()) = checkTorusCertificateSharp c := rfl

theorem checkTorusCertificateV2_routeV2All_aFrozen (c : TorusCertificate n α) (w : FrozenWit) :
    checkTorusCertificateV2 routeV2All c (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl w))))) =
      checkTorusCertificateV2 routeAFrozen c w := rfl

theorem checkTorusCertificateV2_routeV2All_aRefined (c : TorusCertificate n α) (w : RefinedWit) :
    checkTorusCertificateV2 routeV2All c (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr w))))) =
      checkTorusCertificateV2 routeARefined c w := rfl

theorem checkTorusCertificateV2_routeV2All_aRefinedR (c : TorusCertificate n α) (w : RefinedWitR) :
    checkTorusCertificateV2 routeV2All c (Sum.inr (Sum.inl (Sum.inl (Sum.inr w)))) =
      checkTorusCertificateV2 routeARefinedR c w := rfl

theorem checkTorusCertificateV2_routeV2All_aL1 (c : TorusCertificate n α) (w : L1.L1Wit) :
    checkTorusCertificateV2 routeV2All c (Sum.inr (Sum.inl (Sum.inr w))) =
      checkTorusCertificateV2 L1.routeAL1 c w := rfl

theorem checkTorusCertificateV2_routeV2All_bFrozen (c : TorusCertificate n α) (w : RunBWit) :
    checkTorusCertificateV2 routeV2All c (Sum.inr (Sum.inr (Sum.inl w))) =
      checkTorusCertificateV2 routeBFrozen c w := rfl

theorem checkTorusCertificateV2_routeV2All_bRefined (c : TorusCertificate n α) (w : RefinedBWit) :
    checkTorusCertificateV2 routeV2All c (Sum.inr (Sum.inr (Sum.inr w))) =
      checkTorusCertificateV2 routeBRefined c w := rfl

end KAM.CertificateSharp.V2

end
