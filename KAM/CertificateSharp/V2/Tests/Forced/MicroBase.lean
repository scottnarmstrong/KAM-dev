/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroStages
public import KAM.CertificateSharp.V2.Tests.Forced.MicroChecks
public import KAM.CertificateSharp.Kernel.Stage
public import KAM.CertificateSharp.V2.Engine

/-!
# The landed sub-checks of the forced toy `Micro`, one kernel run each

`static_ok` … `energy_ok` (`MicroChecks`) decide the landed sub-checks directly. The Gram and
torsion checks go through the memoized stages of `MicroStages` (`Kernel/Stage.lean`): each stage literal, computed by
the Python mirror, is re-proved here by its own `decide +kernel` on a Boolean equality, then
rewritten into the landed `gramCheck` and `torsionModels` (`gramCheck_eq_of_rows`,
`torsionModels_eq_of_stages`). A mirror that drifted from the landed checker would fail these
equalities: the stage theorems are the cross-language agreement test of the producer. `base_ok`
assembles `landedBase.check`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Micro

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-! ### Gram -/

theorem G_eq : gramModels 2 cert.emb cert.weight cert.cfgLow cert.piEnc = G :=
  eq_of_matBeq (by decide +kernel)

theorem dRows_eq : gramDefectRows 2 cert.gramInv G cert.weight cert.cfgLow cert.piEnc = dRows := by
  decide +kernel

theorem gram_eq : gramCheck 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc
    (cert.params.σB - cert.params.μ) = some db :=
  (gramCheck_eq_of_rows 2 cert.emb cert.gramInv cert.weight cert.cfgLow cert.piEnc _
    (by decide +kernel) (by rewrite [G_eq]; exact dRows_eq)).trans (by decide +kernel)

theorem gram_ok : checkGram cert = true := checkGram_of_gramCheck gram_eq

/-! ### Torsion, stage by stage -/

theorem eps_eq : gramInvRadius db = some eps := by decide +kernel

theorem ms_eq : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgLow cert.piEnc
    (torsionSlots 2 cert.ham.jet) = some ms :=
  eq_of_optModelsBeq (by decide +kernel)

theorem L_eq : dkModels 2 cert.emb cert.weight cert.piEnc = L := eq_of_matBeq (by decide +kernel)

theorem Gi_eq : gramInvModels 2 cert.gramInv eps = Gi := eq_of_matBeq (by decide +kernel)

theorem DL_eq : dkwModels 2 cert.emb cert.freqBox cert.params.s cert.weight cert.cfgLow
    cert.piEnc = DL :=
  eq_of_matBeq (by decide +kernel)

theorem N0_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 0] (2 + 2) 2 2 L Gi = N0 :=
  eq_of_matBeq (by decide +kernel)

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

theorem DN2_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 6] (2 + 2) 2 2 L
    (modelMatNeg 2 2 DGi1) = DN2 :=
  eq_of_matBeq (by decide +kernel)

theorem XN1_eq : modelMatMul cert.weight cert.cfgLow cert.piEnc [4, 7] (2 + 2) (2 + 2) 2
    (dxhModels 2 ms) (modelMatOmega 2 2 N0) = XN1 :=
  eq_of_matBeq (by decide +kernel)

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
  rw [checkTorsion_eq_of gram_eq (torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit cert.gramInv
    db cert.freqBox cert.params.s cert.weight cert.cfgLow cert.piEnc eps_eq ms_eq L_eq Gi_eq DL_eq
    N0_eq DG1_eq DG2_eq DGi0_eq DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq)]
  decide +kernel

/-- **Every landed sub-check passes** on `Micro.cert`. -/
theorem base_ok : landedBase.check cert = true := by
  show (checkStatic cert && checkHamBounds cert && checkEmbedding cert && checkInvariance cert &&
    checkEnergy cert && checkGram cert && checkTorsion cert) = true
  rw [static_ok, hamBounds_ok, embedding_ok, invariance_ok, energy_ok, gram_ok, torsion_ok]
  rfl

end KAM.CertificateSharp.V2.Forced.Micro

end
