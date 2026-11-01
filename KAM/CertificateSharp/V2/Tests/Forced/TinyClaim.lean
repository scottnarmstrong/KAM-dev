/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyBase
public import KAM.CertificateSharp.V2.RouteARefinedEngine

/-!
# The refined claim of the forced toy `Tiny`

`Rclaim`: the four sums of the disc pass and the frame bounds, from the producer's mirror values
rounded up by `10⁻⁴`. `hamClaim_ok` is the disc pass (`checkHamClaim`); `frame_ok` the frame
majorants of C4, `checkFrameN` and `checkFrameT` through the memoized stages of `TinyBase`
(`checkFrameN_eq_of`, `checkFrameT_eq_of`), so the frame and the torsion share one kernel
computation of each stage.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The refined claim (bounds on `H` and the frame). -/
def Rclaim : RefClaim :=
  { dh := (141 / 125), dx := (1001 / 1000), d2x := (1169 / 1000000), d2h := (1001 / 1000),
    bL := (1001 / 1000), bN := (1001 / 1000), bNt := (1001 / 1000), bT := (1001 / 1000) }

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

end KAM.CertificateSharp.V2.Forced.Tiny

end
