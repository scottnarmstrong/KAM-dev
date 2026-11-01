/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyFreq
public import KAM.CertificateSharp.V2.Tests.Forced.TinyL1Core
public import KAM.CertificateSharp.V2.Tests.Forced.TinyHybCore
public import KAM.CertificateSharp.V2.Tests.Forced.TinyHybStep
public import KAM.CertificateSharp.V2.Tests.Forced.TinyHybOmega
public import KAM.CertificateSharp.V2.Tests.Forced.Lemmas
public import KAM.CertificateSharp.Kernel.Stage
public import KAM.CertificateSharp.Hybrid.Iso

/-!
# The forced toy `Tiny` through the ℓ¹ entry and the hybrid restart (opt-in, not in the library)

Not built by anything (`kernel-tests/README.md`); the file stands for
`KAM.CertificateSharp.V2.Tests.ForcedL1Hybrid`. It imports only library modules: the data and
witnesses of `KAM/CertificateSharp/V2/Tests/Forced/` (`TinyL1HybData`), the cheap parts that the
default build decides (`TinyL1Core`, `TinyL1Claim`: the rational core and the ℓ¹ checks of `L`,
`N`, `E`; `TinyHybCore`, `TinyHybStep`, `TinyHybOmega`: the rational checks of the hybrid and the
step's model checks; with their rejections) and the bridges `Kernel/StageL1.lean`,
`Kernel/StageHyb.lean`. It runs directly:
`nice -n 10 lake env lean kernel-tests/CertificateSharp/V2/ForcedL1Hybrid.lean`.

The base certificate is `Tiny.cert` (`TorusCertificate 2 (CertFixed 96)`, `err = 4.1·10⁻¹²`), whose
landed sub-checks are re-decided here exactly as in `ForcedRoutes.lean` (`base_ok`). This file adds
what is heavy: the torsion stages, the frames, the certified sites, and the assembly.

* **Route A with the ℓ¹ entry** (`L1.routeAL1`, witness `l1Wit`): the ℓ¹ claim `checkL1Claim` is
  computed from the certificate's own models through the memoized stages (`Kernel/StageL1.lean`:
  `dkModels`, the Gram certificate and `frameNModels`, `torsionModels` through the stages of
  `torsionModels_eq_of_stages`, the composition `msF` of `checkInvariance`), on the strip
  `ρ' = 1/10` (`|E|₁ ≤ 2.98·10⁻¹²`); C6's run on that strip with its certified sites passes
  `l1Core` at `X⋆ = 1830` (the refined run alone on the same strip: `X⋆ = 832`); `l1_torus`.
* **The hybrid restart** (`Hybrid.routeHybrid`, witness `hybWit`): the Newton step `hybDK` (two
  half terms, the `(2, 2)` modes of `u` and `p` dropped by the base torus's pruning) cuts the error
  to the restart's `e₁ = 5.36·10⁻¹⁵`; the step claims (`hybStepOk`: the step norms, `‖Ω‖`, the
  Cauchy bound, the linearised error `Ẽ` and energy from the three compositions, memoized through
  `hybCompOk_eq_of`), the transfer `transferOk`, and the route-A′ core at the restart numbers
  (`refinedWitR` with the transferred claim; `ρ₁ = ρ`, so its sites are the base run's by
  `sitesOk_congr`); `hybrid_torus`.

Both conclusions are the landed `CertifiedTorus Tiny.cert Tiny.ωstar`. Every decision is a
`decide +kernel` at default limits.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-! ### The landed sub-checks (as `ForcedRoutes.lean`) -/

theorem static_ok : checkStatic cert = true := by decide +kernel

theorem hamBounds_ok : checkHamBounds cert = true := by decide +kernel

theorem embedding_ok : checkEmbedding cert = true := by decide +kernel

theorem invariance_ok : checkInvariance cert = true := by decide +kernel

theorem energy_ok : checkEnergy cert = true := by decide +kernel

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

/-- The assembled torsion matrix of `torsionModels_eq_of_stages`. -/
noncomputable def Tmat : ModelMatrix FB := buildMat (2 + 1) (2 + 1) fun i j =>
  if i < 2 then
    (if j < 2 then modelMatrixEntry Tb i j else freqModel 2 cert.freqBox cert.params.s i)
  else (if j < 2 then modelMatrixEntry Y 0 j else zeroModel)

theorem T_eq : torsionModels 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox cert.params.s
    cert.weight cert.cfgLow cert.piEnc = some Tmat :=
  torsionModels_eq_of_stages 2 cert.ham cert.emb cert.wit cert.gramInv db cert.freqBox cert.params.s
    cert.weight cert.cfgLow cert.piEnc eps_eq msT_eq L_eq Gi_eq DL_eq N0_eq DG1_eq DG2_eq DGi0_eq
    DGi1_eq DN1_eq DN2_eq XN1_eq Tb_eq Y_eq

/-- The torsion check from the stages: `torsionAvgCheck` on the assembled literal matrix. -/
theorem torsion_ok : checkTorsion cert = true := by
  rw [checkTorsion_eq_of gram_eq T_eq]
  decide +kernel

/-- **Every landed sub-check passes** on `Tiny.cert`. -/
theorem base_ok : landedBase.check cert = true := by
  show (checkStatic cert && checkHamBounds cert && checkEmbedding cert && checkInvariance cert &&
    checkEnergy cert && checkGram cert && checkTorsion cert) = true
  rw [static_ok, hamBounds_ok, embedding_ok, invariance_ok, energy_ok, gram_ok, torsion_ok]
  rfl

/-! ### The base claim (bounds on `H` and the frame), shared by both routes -/

theorem hamClaim_ok : checkHamClaim cert Rclaim = true := by decide +kernel

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

/-! ### Route A with the ℓ¹ entry -/

theorem l1T_ok : L1.checkL1T cert l1Claim = true := by
  rw [L1.checkL1T_eq_of gram_eq T_eq]
  decide +kernel

/-- **The ℓ¹ data of `Tiny` from its own models**, on `T_{1/10}` (the torsion on `T_{ρ' - δ₀'}`). -/
theorem l1Claim_ok : L1.checkL1Claim cert l1Claim = true :=
  L1.checkL1Claim_of l1W1_ok l1WT_ok (by decide +kernel) (by decide +kernel) l1L_ok l1N_ok l1T_ok
    l1E_ok

theorem l1_sites : sitesOk (l1Wit.num 2 cert.params cert.freqBox) l1Wit.base.core.J cert.freqBox
    l1Wit.base.κ cert.params.γ l1Wit.base.sites = true := by decide +kernel

theorem l1_core : L1.l1Core 2 cert.params cert.freqBox l1Wit = true :=
  L1.l1Core_of l1_Xs l1_wf l1_ok l1_sites l1_tail l1_entry l1_final

theorem l1_test : L1.l1Test cert l1Wit = true := by
  have h1 : checkHamClaim cert l1Wit.base.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (l1Wit.base.R.frame cert.freqBox) = true := frame_ok
  have h3 : L1.checkL1Claim cert l1Wit.L = true := l1Claim_ok
  show (checkHamClaim cert l1Wit.base.R &&
    checkFrameMajorants cert (l1Wit.base.R.frame cert.freqBox) && L1.checkL1Claim cert l1Wit.L &&
    L1.l1Core 2 cert.params cert.freqBox l1Wit) = true
  rw [h1, h2, h3, l1_core]
  rfl

/-- **The forced toy through `routeV2All`**, at the witness of the ℓ¹ entry. -/
theorem l1_passes : checkTorusCertificateV2 routeV2All cert (Sum.inr (Sum.inl (Sum.inr l1Wit))) =
    true := by
  rw [checkTorusCertificateV2_routeV2All_aL1]
  refine (checkV2_eq L1.routeAL1 cert l1Wit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeAL1_test cert l1Wit).trans l1_test

/-- **The certified torus of `Tiny` through route A with the ℓ¹ entry.** -/
theorem l1_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All l1_passes freq dio

/-! ### The hybrid restart -/

theorem hyb_step : Hybrid.hybStepOk cert hybWit.step hybWit.p1.rho hybWit.p1.rhoInf
    (hybWit.ρT 2 cert.freqBox) = true :=
  Hybrid.hybStepOk_of hyb_weights hyb_poly hyb_omega hyb_cauchy hyb_comp hyb_dw

/-- The certified sites of the base run of lever L8′ (`refinedWitR`). -/
theorem refinedR_sites : sitesOk (refinedWitR.base.num 2 cert.params cert.freqBox)
    refinedWitR.base.core.J cert.freqBox refinedWitR.base.κ cert.params.γ refinedWitR.base.sites =
      true := by decide +kernel

/-- The restart reuses the base run's sites (`ρ₁ = ρ`, the same schedule and constants). -/
theorem hyb_sites : sitesOk (hybWit.w1.base.num 2 hybWit.p1 cert.freqBox) hybWit.w1.base.core.J
    cert.freqBox hybWit.w1.base.κ hybWit.p1.γ hybWit.w1.base.sites = true :=
  (Hybrid.sitesOk_congr rfl rfl rfl rfl rfl rfl rfl).trans refinedR_sites

theorem hyb_core : refinedCoreR 2 hybWit.p1 cert.freqBox hybWit.w1 = true :=
  refinedCoreR_of hyb_Xs hyb_wf hyb_okR hyb_budget hyb_sites hyb_tail hyb_final

theorem hyb_check : Hybrid.checkHybrid cert hybWit = true :=
  Hybrid.checkHybrid_of hyb_transfer hyb_step hyb_core

theorem hyb_test : Hybrid.hybTest cert hybWit = true := by
  have h1 : checkHamClaim cert hybWit.R0 = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (hybWit.R0.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert hybWit.R0 && checkFrameMajorants cert (hybWit.R0.frame cert.freqBox) &&
    Hybrid.checkHybrid cert hybWit) = true
  rw [h1, h2, hyb_check]
  rfl

/-- **The forced toy through `routeV2Hyb`**, at the witness of the hybrid route. -/
theorem hyb_passes : checkTorusCertificateV2 Hybrid.routeV2Hyb cert (Sum.inr (Sum.inr hybWit)) =
    true := by
  rw [Hybrid.checkTorusCertificateV2_routeV2Hyb_hybrid]
  refine (checkV2_eq Hybrid.routeHybrid cert hybWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeHybrid_test cert hybWit).trans hyb_test

/-- **The certified torus of `Tiny` through the hybrid restart.** -/
theorem hybrid_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound Hybrid.routeV2Hyb hyb_passes freq dio

end KAM.CertificateSharp.V2.Forced.Tiny

end
