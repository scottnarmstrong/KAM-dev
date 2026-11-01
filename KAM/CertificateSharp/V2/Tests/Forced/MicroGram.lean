/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroStages
public import KAM.CertificateSharp.Kernel.Stage
public import KAM.CertificateSharp.V2.Engine

/-!
# The Gram check and the stages `L`, `G⁻¹`, `DL`, `[4, 0]` of the forced toy `Micro`

Each stage literal of `MicroStages` (computed by the Python mirror) is re-proved by its own
kernel run and rewritten into the landed `gramCheck` (`gramCheck_eq_of_rows`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Micro

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem G_eq : gramModels 2 cert.emb cert.weight cert.cfgLow cert.piEnc = G :=
  eq_of_matBeq (by decide +kernel)

theorem dRows_eq : gramDefectRows 2 cert.gramInv G cert.weight cert.cfgLow cert.piEnc = dRows := by
  decide +kernel

theorem gram_eq : gramCheck 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc
    (cert.params.σB - cert.params.μ) = some db :=
  (gramCheck_eq_of_rows 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc _
    (by decide +kernel) (by rewrite [G_eq]; exact dRows_eq)).trans (by decide +kernel)

theorem gram_ok : checkGram cert = true := checkGram_of_gramCheck gram_eq

theorem eps_eq : gramInvRadius db = some eps := by decide +kernel

theorem L_eq : dkModels 2 cert.emb cert.weight cert.piEnc = L := eq_of_matBeq (by decide +kernel)

theorem Gi_eq : gramInvModels 2 cert.gramInv eps = Gi := eq_of_matBeq (by decide +kernel)

theorem DL_eq : dkwModels 2 cert.emb cert.freqBox cert.params.s cert.weight cert.cfgLow
    cert.piEnc = DL :=
  eq_of_matBeq (by decide +kernel)

theorem N0_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 0] (2 + 2) 2 2 L Gi = N0 :=
  eq_of_matBeq (by decide +kernel)

end KAM.CertificateSharp.V2.Forced.Micro

end
