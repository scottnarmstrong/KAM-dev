/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroPackedData
public import KAM.CertificateSharp.V2.Tests.Forced.PackedLemmas

/-!
# The packed Gram stage of the forced toy `Micro`

On `MicroP.cert`: the boundary (`gEntries`: the eight landed `DK` models against the memo `mm`) and
the packed core (`gCore`: exact packed products, packed norms, the landed final test), one kernel
run each, assembled into the packed Gram check (`gram_eq`, `gramPackedCheck_eq_core`) and the packed
Gram sub-check (`gram_ok`). No landed Gram product is evaluated.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroP

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Packed KAM.CertificateSharp.V2

theorem gEntries : pgEntries 2 cert.emb cert.weight cert.cfgLow cert.piEnc bk mm = true := by
  decide +kernel

theorem gCore : gramPackedCore 2 cert.gramInv cert.weight cert.cfgLow bk mm
    (cert.params.σB - cert.params.μ) = some db := by
  decide +kernel

theorem gram_eq : gramPackedCheck 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc bk mm
    (cert.params.σB - cert.params.μ) = some db :=
  (gramPackedCheck_eq_core 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc bk gEntries
    _).trans gCore

theorem eps_eq : gramInvRadius db = some eps := by decide +kernel

/-- **The packed Gram sub-check passes** on `MicroP.cert`. -/
theorem gram_ok : checkGramPacked bk mm cert = true := checkGramPacked_of gram_eq

end KAM.CertificateSharp.V2.Forced.MicroP

end
