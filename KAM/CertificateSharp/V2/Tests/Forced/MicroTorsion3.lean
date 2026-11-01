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
# Torsion stages of the forced toy `Micro` (part 3)

`XN1_eq`: stage literals re-proved by their own kernel runs
(`eq_of_matBeq`, `eq_of_optModelsBeq`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Micro

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem XN1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 7] (2 + 2) (2 + 2) 2
    (dxhModels 2 ms) (modelMatOmega 2 2 N0) = XN1 :=
  eq_of_matBeq (by decide +kernel)

end KAM.CertificateSharp.V2.Forced.Micro

end
