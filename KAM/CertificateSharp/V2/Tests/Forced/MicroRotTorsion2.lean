/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroRotStages
public import KAM.CertificateSharp.Kernel.Stage
public import KAM.CertificateSharp.V2.Engine

/-!
# Torsion stages of the forced toy `MicroRot` (part 2)

`DN2_eq`: stage literals re-proved by their own kernel runs
(`eq_of_matBeq`, `eq_of_optModelsBeq`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroRot

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem DN2_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 6] (2 + 2) 2 2 L
    (modelMatNeg 2 2 DGi1) = DN2 :=
  eq_of_matBeq (by decide +kernel)

end KAM.CertificateSharp.V2.Forced.MicroRot

end
