/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroPackedData
public import KAM.CertificateSharp.V2.Tests.Forced.MicroStages

/-!
# The torsion slots of `MicroP.cert`

`ms_eq`: the landed jet composition at `cfgLow` (`Slp.compose`, read by `checkTorsionR` as by the
landed `checkTorsion`) is the stage literal `Micro.ms`, re-proved by one kernel run on
`MicroP.cert` (its `cfgLow` differs from `Micro.cert`'s by the decoder, which no `direct` product
reads, but the term differs, so `Micro.ms_eq` does not apply).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroP

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem ms_eq : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgLow
    cert.piEnc (torsionSlots 2 cert.ham.jet) = some Micro.ms :=
  eq_of_optModelsBeq (by decide +kernel)

end KAM.CertificateSharp.V2.Forced.MicroP

end
