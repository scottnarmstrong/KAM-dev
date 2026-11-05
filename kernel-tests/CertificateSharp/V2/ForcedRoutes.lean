/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram
public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyFreq
public import KAM.CertificateSharp.V2.Tests.Forced.TinyC2Stages
public import KAM.CertificateSharp.V2.Tests.Forced.TinyC2Freq
public import KAM.CertificateSharp.V2.Tests.Forced.Lemmas
public import KAM.CertificateSharp.Kernel.Stage
public import KAM.CertificateSharp.V2.RouteAll
public import KAM.SpinOrbit.Rotated

/-!
# The forced toys' route checks and the time normalization (opt-in, not part of the library)

Not built by anything (`kernel-tests/README.md`); the file stands for
`KAM.CertificateSharp.V2.Tests.ForcedRoutes`. It imports only library modules (the data, witnesses
and cheap Gram stages of `KAM/CertificateSharp/V2/Tests/Forced/`), so it runs directly:
`nice -n 10 lake env lean kernel-tests/CertificateSharp/V2/ForcedRoutes.lean`.

* `Tiny`: the remaining landed sub-checks and torsion stages (`base_ok`), the refined claim
  (`hamClaim_ok`, `frame_ok`), route A (`refinedA_passes`, `refinedA_torus`), L8′
  (`refinedR_passes`), route B (`refinedB_passes`, `refinedB_torus`), and the mutation `mut_frameT`
  (it needs every torsion stage);
* `TinyC2`: the time normalization of `Tiny` (H and ω* doubled) through route A;
* `timeScale_*`: the two normalizations related by `invarianceError_const_mul`, both tori certified.

The cheap subset stays in the default build: the passing certificate `Micro` (sharp, frozen A,
frozen B: `MicroRoutes`) and the mutations of `Tiny` (`TinyMut*`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem static_ok : checkStatic cert = true := by decide +kernel

theorem hamBounds_ok : checkHamBounds cert = true := by decide +kernel

theorem embedding_ok : checkEmbedding cert = true := by decide +kernel

theorem invariance_ok : checkInvariance cert = true := by decide +kernel

theorem energy_ok : checkEnergy cert = true := by decide +kernel

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
  rw [checkTorsion_eq_of gram_eq (torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit
    cert.gramInv db cert.freqBox cert.params.s cert.weight cert.cfgLow cert.piEnc eps_eq ms_eq L_eq
    Gi_eq DL_eq N0_eq DG1_eq DG2_eq DGi0_eq DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq)]
  decide +kernel

/-- **Every landed sub-check passes** on `Tiny.cert`. -/
theorem base_ok : landedBase.check cert = true := by
  show (checkStatic cert && checkHamBounds cert && checkEmbedding cert && checkInvariance cert &&
    checkEnergy cert && checkGram cert && checkTorsion cert) = true
  rw [static_ok, hamBounds_ok, embedding_ok, invariance_ok, energy_ok, gram_ok, torsion_ok]
  rfl

theorem hamClaim_ok : checkHamClaim cert Rclaim = true := by decide +kernel

/-- The assembled torsion matrix of `torsionModels_eq_of_stages`. -/
noncomputable def Tmat : ModelMatrix FB := buildMat (2 + 1) (2 + 1) fun i j =>
  if i < 2 then
    (if j < 2 then modelMatrixEntry Tb i j else freqModel 2 cert.freqBox cert.params.s i)
  else (if j < 2 then modelMatrixEntry Y 0 j else zeroModel)

theorem T_eq : torsionModels 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox cert.params.s
    cert.weight cert.cfgLow cert.piEnc = some Tmat :=
  torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox cert.params.s
    cert.weight cert.cfgLow cert.piEnc eps_eq ms_eq L_eq Gi_eq DL_eq N0_eq DG1_eq DG2_eq DGi0_eq
    DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq

theorem frameL_ok : checkFrameL cert Rclaim.bL = true := by decide +kernel

theorem frameN_ok : checkFrameN cert Rclaim.bN Rclaim.bNt = true := by
  rw [checkFrameN_eq_of gram_eq eps_eq (frameNModels_eq_of_stage 2 cert.emb cert.gramInv eps
    cert.weight cert.cfgLow cert.piEnc L_eq Gi_eq N0_eq)]
  decide +kernel

theorem frameT_ok : checkFrameT cert Rclaim.bT = true := by
  rw [checkFrameT_eq_of gram_eq T_eq]
  decide +kernel

theorem frameOm_ok : checkFrameOmega cert (freqNormUp cert.freqBox) = true := by decide +kernel

theorem frame_ok : checkFrameMajorants cert (Rclaim.frame cert.freqBox) = true := by
  show (checkFrameL cert Rclaim.bL && checkFrameN cert Rclaim.bN Rclaim.bNt &&
    checkFrameT cert Rclaim.bT && checkFrameOmega cert (freqNormUp cert.freqBox)) = true
  rw [frameL_ok, frameN_ok, frameT_ok, frameOm_ok]
  rfl

theorem refinedA_sites : sitesOk (refinedWit.num 2 cert.params cert.freqBox) refinedWit.core.J
    cert.freqBox refinedWit.κ cert.params.γ refinedWit.sites = true := by decide +kernel

theorem refinedA_core : refinedCore 2 cert.params cert.freqBox refinedWit = true :=
  refinedCore_of (by decide +kernel) (by decide +kernel) (by decide +kernel) refinedA_sites
    (by decide +kernel) (by decide +kernel)

theorem refinedA_test : refinedTest cert refinedWit = true := by
  have h1 : checkHamClaim cert refinedWit.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedWit.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedWit.R &&
    checkFrameMajorants cert (refinedWit.R.frame cert.freqBox) &&
    refinedCore 2 cert.params cert.freqBox refinedWit) = true
  rw [h1, h2, refinedA_core]
  rfl

/-- **The forced toy through `routeV2All`**, at the witness of `routeARefined`. -/
theorem refinedA_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr refinedWit))))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aRefined]
  refine (checkV2_eq routeARefined cert refinedWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeARefined_test cert refinedWit).trans refinedA_test

/-- **The certified torus of the forced toy `Tiny`** at `κ (ν₋(8) - 1, 1)`. -/
theorem refinedA_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedA_passes freq dio

theorem refinedB_sites : (refinedBWit.num cert.params cert.freqBox).sitesOk 2 refinedBWit.core.J
    cert.freqBox refinedBWit.κ cert.params.γ refinedBWit.sites = true := by decide +kernel

theorem refinedB_core : refinedBCore 2 cert.params cert.freqBox refinedBWit = true :=
  refinedBCore_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) refinedB_sites (by decide +kernel) (by decide +kernel)

/-- **The forced toy through `routeV2All`**, at the witness of `routeBRefined`. -/
theorem refinedB_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inr (Sum.inr refinedBWit))) = true := by
  rw [checkTorusCertificateV2_routeV2All_bRefined]
  refine (checkV2_eq routeBRefined cert refinedBWit).trans ?_
  rw [base_ok, Bool.true_and]
  refine (routeBRefined_test cert refinedBWit).trans ?_
  have h1 : checkHamClaim cert refinedBWit.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedBWit.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedBWit.R &&
    checkFrameMajorants cert (refinedBWit.R.frame cert.freqBox) &&
    refinedBCore 2 cert.params cert.freqBox refinedBWit) = true
  rw [h1, h2, refinedB_core]
  rfl

/-- **The certified torus of `Tiny` through route B.** -/
theorem refinedB_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedB_passes freq dio

theorem refinedR_sites : sitesOk (refinedWitR.base.num 2 cert.params cert.freqBox)
    refinedWitR.base.core.J cert.freqBox refinedWitR.base.κ cert.params.γ refinedWitR.base.sites =
      true := by decide +kernel

theorem refinedR_core : refinedCoreR 2 cert.params cert.freqBox refinedWitR = true :=
  refinedCoreR_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    refinedR_sites (by decide +kernel) (by decide +kernel)

/-- **The forced toy through `routeV2All`** with lever L8′. -/
theorem refinedR_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inr refinedWitR)))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aRefinedR]
  refine (checkV2_eq routeARefinedR cert refinedWitR).trans ?_
  rw [base_ok, Bool.true_and]
  refine (routeARefinedR_test cert refinedWitR).trans ?_
  have h1 : checkHamClaim cert refinedWitR.base.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedWitR.base.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedWitR.base.R &&
    checkFrameMajorants cert (refinedWitR.base.R.frame cert.freqBox) &&
    refinedCoreR 2 cert.params cert.freqBox refinedWitR) = true
  rw [h1, h2, refinedR_core]
  rfl

theorem refinedR_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedR_passes freq dio

/-- Rejected: the frame bound `bT` times `0.99` (frame bounds). -/
theorem mut_frameT : checkFrameT cert (Rclaim.bT * 99 / 100) = false := by
  rw [checkFrameT_eq_of gram_eq T_eq]
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

namespace KAM.CertificateSharp.V2.Forced.TinyC2

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem static_ok : checkStatic cert = true := by decide +kernel

theorem hamBounds_ok : checkHamBounds cert = true := by decide +kernel

theorem embedding_ok : checkEmbedding cert = true := by decide +kernel

theorem invariance_ok : checkInvariance cert = true := by decide +kernel

theorem energy_ok : checkEnergy cert = true := by decide +kernel

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
  rw [checkTorsion_eq_of gram_eq (torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit
    cert.gramInv db cert.freqBox cert.params.s cert.weight cert.cfgLow cert.piEnc eps_eq ms_eq L_eq
    Gi_eq DL_eq N0_eq DG1_eq DG2_eq DGi0_eq DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq)]
  decide +kernel

/-- **Every landed sub-check passes** on `TinyC2.cert`. -/
theorem base_ok : landedBase.check cert = true := by
  show (checkStatic cert && checkHamBounds cert && checkEmbedding cert && checkInvariance cert &&
    checkEnergy cert && checkGram cert && checkTorsion cert) = true
  rw [static_ok, hamBounds_ok, embedding_ok, invariance_ok, energy_ok, gram_ok, torsion_ok]
  rfl

/-- The refined claim (bounds on `H` and the frame). -/
def Rclaim : RefClaim :=
  { dh := (451 / 200), dx := (2001 / 1000), d2x := (1169 / 500000), d2h := (2001 / 1000),
    bL := (1001 / 1000), bN := (1001 / 1000), bNt := (1001 / 1000), bT := (2001 / 1000) }

theorem hamClaim_ok : checkHamClaim cert Rclaim = true := by decide +kernel

/-- The assembled torsion matrix of `torsionModels_eq_of_stages`. -/
noncomputable def Tmat : ModelMatrix FB := buildMat (2 + 1) (2 + 1) fun i j =>
  if i < 2 then
    (if j < 2 then modelMatrixEntry Tb i j else freqModel 2 cert.freqBox cert.params.s i)
  else (if j < 2 then modelMatrixEntry Y 0 j else zeroModel)

theorem T_eq : torsionModels 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox cert.params.s
    cert.weight cert.cfgLow cert.piEnc = some Tmat :=
  torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox cert.params.s
    cert.weight cert.cfgLow cert.piEnc eps_eq ms_eq L_eq Gi_eq DL_eq N0_eq DG1_eq DG2_eq DGi0_eq
    DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq

theorem frameL_ok : checkFrameL cert Rclaim.bL = true := by decide +kernel

theorem frameN_ok : checkFrameN cert Rclaim.bN Rclaim.bNt = true := by
  rw [checkFrameN_eq_of gram_eq eps_eq (frameNModels_eq_of_stage 2 cert.emb cert.gramInv eps
    cert.weight cert.cfgLow cert.piEnc L_eq Gi_eq N0_eq)]
  decide +kernel

theorem frameT_ok : checkFrameT cert Rclaim.bT = true := by
  rw [checkFrameT_eq_of gram_eq T_eq]
  decide +kernel

theorem frameOm_ok : checkFrameOmega cert (freqNormUp cert.freqBox) = true := by decide +kernel

theorem frame_ok : checkFrameMajorants cert (Rclaim.frame cert.freqBox) = true := by
  show (checkFrameL cert Rclaim.bL && checkFrameN cert Rclaim.bN Rclaim.bNt &&
    checkFrameT cert Rclaim.bT && checkFrameOmega cert (freqNormUp cert.freqBox)) = true
  rw [frameL_ok, frameN_ok, frameT_ok, frameOm_ok]
  rfl

/-- The refined route-A witness of `TinyC2`. -/
def refinedWit : RefinedWit where
  core :=
    { Xs := (241 / 10), kp := 3, th := (1 / 8), c := [(1249 / 100000), (1177 / 100000),
      (1169 / 100000)], cbar := [(291 / 12500), (371 / 20000), (1389 / 100000)],
      ctail := (1021567 / 12500000), sB := (51007441 / 50000000), sT := (143039349 / 250000000),
      sLt := (50054123 / 50000000), sN := (25029851 / 25000000), sNt := (20024641 / 20000000),
      t := (40081881 / 20000000), J := 20 }
  R := Rclaim
  κ := (2000000 / 1000001)
  sites :=
    [(some ⟨(773227 / 1000000), 6, 8, (9044 / 25)⟩,
      some ⟨(26037 / 125000), 4, 8, (171071 / 5000)⟩),
     (some ⟨(220053 / 250000), 7, 8, (25697 / 20)⟩,
      some ⟨(113319 / 250000), 5, 8, (21287 / 250)⟩),
     (some ⟨(469567 / 500000), 9, 8, (507257 / 100)⟩,
      some ⟨(668659 / 1000000), 6, 8, (36741 / 200)⟩)]

theorem refinedA_sites : sitesOk (refinedWit.num 2 cert.params cert.freqBox) refinedWit.core.J
    cert.freqBox refinedWit.κ cert.params.γ refinedWit.sites = true := by decide +kernel

theorem refinedA_core : refinedCore 2 cert.params cert.freqBox refinedWit = true :=
  refinedCore_of (by decide +kernel) (by decide +kernel) (by decide +kernel) refinedA_sites
    (by decide +kernel) (by decide +kernel)

theorem refinedA_test : refinedTest cert refinedWit = true := by
  have h1 : checkHamClaim cert refinedWit.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedWit.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedWit.R &&
    checkFrameMajorants cert (refinedWit.R.frame cert.freqBox) &&
    refinedCore 2 cert.params cert.freqBox refinedWit) = true
  rw [h1, h2, refinedA_core]
  rfl

/-- **The forced toy through `routeV2All`**, at the witness of `routeARefined`. -/
theorem refinedA_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr refinedWit))))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aRefined]
  refine (checkV2_eq routeARefined cert refinedWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeARefined_test cert refinedWit).trans refinedA_test

/-- **The certified torus of the forced toy `TinyC2`** at `κ (ν₋(8) - 1, 1)`. -/
theorem refinedA_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedA_passes freq dio

end KAM.CertificateSharp.V2.Forced.TinyC2

namespace KAM.CertificateSharp.V2.Forced

open KAM KAM.Certificate KAM.SpinOrbit

/-- The two normalizations carry the same torus. -/
theorem timeScale_emb : TinyC2.cert.emb = Tiny.cert.emb := rfl

/-- The Hamiltonian of `TinyC2` is twice that of `Tiny`. -/
theorem timeScale_H : TinyC2.cert.H = fun z => ((2 : ℝ) : ℂ) * Tiny.cert.H z := by
  funext z
  simp only [TorusCertificate.H, TinyC2.cert, Tiny.cert, TinyC2.ham, Tiny.ham, HamExpr.eval]
  push_cast
  ring

/-- The reference vector of `TinyC2` is twice that of `Tiny`. -/
theorem timeScale_ωstar : TinyC2.ωstar = (2 : ℝ) • Tiny.ωstar := by
  have h : (TinyC2.κ : ℝ) = 2 * Tiny.κ := by
    rw [TinyC2.κ, Tiny.κ]; norm_num
  funext i
  fin_cases i
  · simp [TinyC2.ωstar, Tiny.ωstar, lunarRotFreq, h]
    ring
  · simp [TinyC2.ωstar, Tiny.ωstar, lunarRotFreq, h]

/-- **The checked transformation**: the invariance error of `TinyC2` is twice that of `Tiny` at
half the frequency (`invarianceError_const_mul`). -/
theorem timeScale_invariance (ω : Fin 2 → ℝ) (θ : Fin 2 → ℂ) :
    invarianceError TinyC2.cert.H TinyC2.cert.K ω θ =
      ((2 : ℝ) : ℂ) • invarianceError Tiny.cert.H Tiny.cert.K ((2 : ℝ)⁻¹ • ω) θ := by
  have hK : TinyC2.cert.K = Tiny.cert.K := by
    simp only [TorusCertificate.K, timeScale_emb]
  rw [timeScale_H, hK]
  exact invarianceError_const_mul (by norm_num) _ _ _ _

/-- Both normalizations are certified: the tori of `Tiny` at `ω*` and of `TinyC2` at `2 ω*`. -/
theorem timeScale_tori : CertifiedTorus Tiny.cert Tiny.ωstar ∧
    CertifiedTorus TinyC2.cert ((2 : ℝ) • Tiny.ωstar) :=
  ⟨Tiny.refinedA_torus, timeScale_ωstar ▸ TinyC2.refinedA_torus⟩

end KAM.CertificateSharp.V2.Forced

end
