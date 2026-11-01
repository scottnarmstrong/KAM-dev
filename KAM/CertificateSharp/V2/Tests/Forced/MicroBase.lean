/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroGram
public import KAM.CertificateSharp.V2.Tests.Forced.MicroTorsion1
public import KAM.CertificateSharp.V2.Tests.Forced.MicroTorsion2
public import KAM.CertificateSharp.V2.Tests.Forced.MicroTorsion3
public import KAM.CertificateSharp.V2.Tests.Forced.MicroChecksA
public import KAM.CertificateSharp.V2.Tests.Forced.MicroChecksB

/-!
# Every landed sub-check of the forced toy `Micro`

`torsion_ok` assembles the torsion stages of `MicroTorsion1/2/3` and `MicroGram`
(`torsionModels_eq_of_stages`);
`base_ok` is `landedBase.check Micro.cert = true`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Micro

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem Tb_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 8] 2 (2 + 2) 2
    (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 N0))
    (modelMatOmega 2 2 (modelMatAdd cert.weight cert.piEnc (2 + 2) 2 XN1
      (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2
        (modelMatAdd cert.weight cert.piEnc (2 + 2) 2 DN1 DN2))))) = Tb :=
  eq_of_matBeq (by decide +kernel)

theorem Y_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 9] 1 (2 + 2) 2 (d1Models 2 ms)
    (modelMatOmega 2 2 N0) = Y :=
  eq_of_matBeq (by decide +kernel)

/-- The torsion check from the stages: `torsionAvgCheck` on the assembled literal matrix. -/
theorem torsion_ok : checkTorsion cert = true := by
  rw [checkTorsion_eq_of gram_eq (torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit
    cert.gramInv db cert.freqBox cert.params.s cert.weight cert.cfgLow cert.piEnc eps_eq ms_eq L_eq
    Gi_eq DL_eq N0_eq DG1_eq DG2_eq DGi0_eq DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq)]
  decide +kernel

/-- **Every landed sub-check passes** on `Micro.cert`. -/
theorem base_ok : landedBase.check cert = true := by
  show (checkStatic cert && checkHamBounds cert && checkEmbedding cert && checkInvariance cert &&
    checkEnergy cert && checkGram cert && checkTorsion cert) = true
  rw [static_ok, hamBounds_ok, embedding_ok, invariance_ok, energy_ok, gram_ok, torsion_ok]
  rfl

end KAM.CertificateSharp.V2.Forced.Micro

end
