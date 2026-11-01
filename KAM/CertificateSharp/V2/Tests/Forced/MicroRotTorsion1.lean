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
# Torsion stages of the forced toy `MicroRot` (part 1)

`ms_eq`, `DG1_eq`, `DG2_eq`, `DGi0_eq`, `DGi1_eq`, `DN1_eq`: stage literals re-proved by their own
kernel runs
(`eq_of_matBeq`, `eq_of_optModelsBeq`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroRot

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem ms_eq : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgLow cert.piEnc
    (torsionSlots 2 cert.ham.jet) = some ms :=
  eq_of_optModelsBeq (by decide +kernel)

theorem DG1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 1] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 DL) L = DG1 :=
  eq_of_matBeq (by decide +kernel)

theorem DG2_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 2] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 L) DL = DG2 :=
  eq_of_matBeq (by decide +kernel)

theorem DGi0_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 3] 2 2 2 Gi
    (modelMatAdd cert.weight cert.piEnc 2 2 DG1 DG2) = DGi0 :=
  eq_of_matBeq (by decide +kernel)

theorem DGi1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 4] 2 2 2 DGi0 Gi = DGi1 :=
  eq_of_matBeq (by decide +kernel)

theorem DN1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 5] (2 + 2) 2 2 DL Gi = DN1 :=
  eq_of_matBeq (by decide +kernel)

end KAM.CertificateSharp.V2.Forced.MicroRot

end
