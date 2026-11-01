/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAll
public import KAM.CertificateSharp.Hybrid.Iso

/-!
# Unfolding lemmas for the forced-toy tests

The v2 certifier at an engine is the landed sub-checks and the engine's test (`checkV2_eq`), and
each engine's test is its named Boolean test (`routeARefined_test`, …). All are `rfl` over
variables. Applying them, instead of a `show` or an `exact` at concrete data, keeps the elaborator
from evaluating the certifier inside a definitional-equality check.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced

open KAM.Certificate KAM.CertificateSharp.V2

variable {n : ℕ} {α : Type} [CertArith α]

theorem checkV2_eq (E : EngineV2) (c : TorusCertificate n α) (w : E.Wit) :
    checkTorusCertificateV2 E c w = (landedBase.check c && E.test c w) := rfl

theorem routeAFrozen_test (c : TorusCertificate n α) (w : FrozenWit) :
    routeAFrozen.test c w = frozenCore n c.params c.freqBox w := rfl

theorem routeARefined_test (c : TorusCertificate n α) (w : RefinedWit) :
    routeARefined.test c w = refinedTest c w := rfl

theorem routeARefinedR_test (c : TorusCertificate n α) (w : RefinedWitR) :
    routeARefinedR.test c w = refinedRefTest c w := rfl

theorem routeAL1_test (c : TorusCertificate n α) (w : L1.L1Wit) :
    L1.routeAL1.test c w = L1.l1Test c w := rfl

theorem routeBFrozen_test (c : TorusCertificate n α) (w : RunBWit) :
    routeBFrozen.test c w = frozenBCore n c.params c.freqBox w := rfl

theorem routeBRefined_test (c : TorusCertificate n α) (w : RefinedBWit) :
    routeBRefined.test c w = refinedBTest c w := rfl

theorem routeHybrid_test (c : TorusCertificate n α) (w : Hybrid.HybWit) :
    Hybrid.routeHybrid.test c w = Hybrid.hybTest c w := rfl

end KAM.CertificateSharp.V2.Forced

end
