/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.Data.CsegJet
public import KAM.Magnetic.Data.CsegJetEq
public import KAM.Magnetic.Data.Mag.Cert
public import KAM.Magnetic.Data.Mag.Seg.Full.S0
public import KAM.Magnetic.Data.Mag.Seg.Full.S1
public import KAM.Magnetic.Data.Mag.Seg.Full.S10
public import KAM.Magnetic.Data.Mag.Seg.Full.S11
public import KAM.Magnetic.Data.Mag.Seg.Full.S12
public import KAM.Magnetic.Data.Mag.Seg.Full.S13
public import KAM.Magnetic.Data.Mag.Seg.Full.S14
public import KAM.Magnetic.Data.Mag.Seg.Full.S15
public import KAM.Magnetic.Data.Mag.Seg.Full.S16
public import KAM.Magnetic.Data.Mag.Seg.Full.S17
public import KAM.Magnetic.Data.Mag.Seg.Full.S18
public import KAM.Magnetic.Data.Mag.Seg.Full.S19
public import KAM.Magnetic.Data.Mag.Seg.Full.S2
public import KAM.Magnetic.Data.Mag.Seg.Full.S20
public import KAM.Magnetic.Data.Mag.Seg.Full.S21
public import KAM.Magnetic.Data.Mag.Seg.Full.S22
public import KAM.Magnetic.Data.Mag.Seg.Full.S23
public import KAM.Magnetic.Data.Mag.Seg.Full.S24
public import KAM.Magnetic.Data.Mag.Seg.Full.S25
public import KAM.Magnetic.Data.Mag.Seg.Full.S26
public import KAM.Magnetic.Data.Mag.Seg.Full.S27
public import KAM.Magnetic.Data.Mag.Seg.Full.S28
public import KAM.Magnetic.Data.Mag.Seg.Full.S29
public import KAM.Magnetic.Data.Mag.Seg.Full.S3
public import KAM.Magnetic.Data.Mag.Seg.Full.S30
public import KAM.Magnetic.Data.Mag.Seg.Full.S31
public import KAM.Magnetic.Data.Mag.Seg.Full.S32
public import KAM.Magnetic.Data.Mag.Seg.Full.S33
public import KAM.Magnetic.Data.Mag.Seg.Full.S34
public import KAM.Magnetic.Data.Mag.Seg.Full.S35
public import KAM.Magnetic.Data.Mag.Seg.Full.S36
public import KAM.Magnetic.Data.Mag.Seg.Full.S37
public import KAM.Magnetic.Data.Mag.Seg.Full.S38
public import KAM.Magnetic.Data.Mag.Seg.Full.S39
public import KAM.Magnetic.Data.Mag.Seg.Full.S4
public import KAM.Magnetic.Data.Mag.Seg.Full.S40
public import KAM.Magnetic.Data.Mag.Seg.Full.S41
public import KAM.Magnetic.Data.Mag.Seg.Full.S42
public import KAM.Magnetic.Data.Mag.Seg.Full.S43
public import KAM.Magnetic.Data.Mag.Seg.Full.S44
public import KAM.Magnetic.Data.Mag.Seg.Full.S45
public import KAM.Magnetic.Data.Mag.Seg.Full.S46
public import KAM.Magnetic.Data.Mag.Seg.Full.S47
public import KAM.Magnetic.Data.Mag.Seg.Full.S48
public import KAM.Magnetic.Data.Mag.Seg.Full.S49
public import KAM.Magnetic.Data.Mag.Seg.Full.S5
public import KAM.Magnetic.Data.Mag.Seg.Full.S50
public import KAM.Magnetic.Data.Mag.Seg.Full.S51
public import KAM.Magnetic.Data.Mag.Seg.Full.S52
public import KAM.Magnetic.Data.Mag.Seg.Full.S53
public import KAM.Magnetic.Data.Mag.Seg.Full.S54
public import KAM.Magnetic.Data.Mag.Seg.Full.S55
public import KAM.Magnetic.Data.Mag.Seg.Full.S56
public import KAM.Magnetic.Data.Mag.Seg.Full.S6
public import KAM.Magnetic.Data.Mag.Seg.Full.S7
public import KAM.Magnetic.Data.Mag.Seg.Full.S8
public import KAM.Magnetic.Data.Mag.Seg.Full.S9
public import KAM.Magnetic.Data.Mag.Seg.Low.S0
public import KAM.Magnetic.Data.Mag.Seg.Low.S1
public import KAM.Magnetic.Data.Mag.Seg.Low.S10
public import KAM.Magnetic.Data.Mag.Seg.Low.S11
public import KAM.Magnetic.Data.Mag.Seg.Low.S12
public import KAM.Magnetic.Data.Mag.Seg.Low.S13
public import KAM.Magnetic.Data.Mag.Seg.Low.S14
public import KAM.Magnetic.Data.Mag.Seg.Low.S15
public import KAM.Magnetic.Data.Mag.Seg.Low.S16
public import KAM.Magnetic.Data.Mag.Seg.Low.S17
public import KAM.Magnetic.Data.Mag.Seg.Low.S18
public import KAM.Magnetic.Data.Mag.Seg.Low.S19
public import KAM.Magnetic.Data.Mag.Seg.Low.S2
public import KAM.Magnetic.Data.Mag.Seg.Low.S20
public import KAM.Magnetic.Data.Mag.Seg.Low.S21
public import KAM.Magnetic.Data.Mag.Seg.Low.S22
public import KAM.Magnetic.Data.Mag.Seg.Low.S23
public import KAM.Magnetic.Data.Mag.Seg.Low.S24
public import KAM.Magnetic.Data.Mag.Seg.Low.S25
public import KAM.Magnetic.Data.Mag.Seg.Low.S26
public import KAM.Magnetic.Data.Mag.Seg.Low.S27
public import KAM.Magnetic.Data.Mag.Seg.Low.S28
public import KAM.Magnetic.Data.Mag.Seg.Low.S29
public import KAM.Magnetic.Data.Mag.Seg.Low.S3
public import KAM.Magnetic.Data.Mag.Seg.Low.S30
public import KAM.Magnetic.Data.Mag.Seg.Low.S31
public import KAM.Magnetic.Data.Mag.Seg.Low.S32
public import KAM.Magnetic.Data.Mag.Seg.Low.S33
public import KAM.Magnetic.Data.Mag.Seg.Low.S34
public import KAM.Magnetic.Data.Mag.Seg.Low.S35
public import KAM.Magnetic.Data.Mag.Seg.Low.S36
public import KAM.Magnetic.Data.Mag.Seg.Low.S37
public import KAM.Magnetic.Data.Mag.Seg.Low.S38
public import KAM.Magnetic.Data.Mag.Seg.Low.S39
public import KAM.Magnetic.Data.Mag.Seg.Low.S4
public import KAM.Magnetic.Data.Mag.Seg.Low.S40
public import KAM.Magnetic.Data.Mag.Seg.Low.S41
public import KAM.Magnetic.Data.Mag.Seg.Low.S42
public import KAM.Magnetic.Data.Mag.Seg.Low.S43
public import KAM.Magnetic.Data.Mag.Seg.Low.S44
public import KAM.Magnetic.Data.Mag.Seg.Low.S45
public import KAM.Magnetic.Data.Mag.Seg.Low.S46
public import KAM.Magnetic.Data.Mag.Seg.Low.S47
public import KAM.Magnetic.Data.Mag.Seg.Low.S48
public import KAM.Magnetic.Data.Mag.Seg.Low.S49
public import KAM.Magnetic.Data.Mag.Seg.Low.S5
public import KAM.Magnetic.Data.Mag.Seg.Low.S50
public import KAM.Magnetic.Data.Mag.Seg.Low.S51
public import KAM.Magnetic.Data.Mag.Seg.Low.S52
public import KAM.Magnetic.Data.Mag.Seg.Low.S53
public import KAM.Magnetic.Data.Mag.Seg.Low.S54
public import KAM.Magnetic.Data.Mag.Seg.Low.S55
public import KAM.Magnetic.Data.Mag.Seg.Low.S56
public import KAM.Magnetic.Data.Mag.Seg.Low.S57
public import KAM.Magnetic.Data.Mag.Seg.Low.S58
public import KAM.Magnetic.Data.Mag.Seg.Low.S59
public import KAM.Magnetic.Data.Mag.Seg.Low.S6
public import KAM.Magnetic.Data.Mag.Seg.Low.S60
public import KAM.Magnetic.Data.Mag.Seg.Low.S61
public import KAM.Magnetic.Data.Mag.Seg.Low.S62
public import KAM.Magnetic.Data.Mag.Seg.Low.S63
public import KAM.Magnetic.Data.Mag.Seg.Low.S64
public import KAM.Magnetic.Data.Mag.Seg.Low.S65
public import KAM.Magnetic.Data.Mag.Seg.Low.S66
public import KAM.Magnetic.Data.Mag.Seg.Low.S67
public import KAM.Magnetic.Data.Mag.Seg.Low.S68
public import KAM.Magnetic.Data.Mag.Seg.Low.S69
public import KAM.Magnetic.Data.Mag.Seg.Low.S7
public import KAM.Magnetic.Data.Mag.Seg.Low.S70
public import KAM.Magnetic.Data.Mag.Seg.Low.S71
public import KAM.Magnetic.Data.Mag.Seg.Low.S72
public import KAM.Magnetic.Data.Mag.Seg.Low.S73
public import KAM.Magnetic.Data.Mag.Seg.Low.S74
public import KAM.Magnetic.Data.Mag.Seg.Low.S75
public import KAM.Magnetic.Data.Mag.Seg.Low.S76
public import KAM.Magnetic.Data.Mag.Seg.Low.S77
public import KAM.Magnetic.Data.Mag.Seg.Low.S78
public import KAM.Magnetic.Data.Mag.Seg.Low.S79
public import KAM.Magnetic.Data.Mag.Seg.Low.S8
public import KAM.Magnetic.Data.Mag.Seg.Low.S80
public import KAM.Magnetic.Data.Mag.Seg.Low.S81
public import KAM.Magnetic.Data.Mag.Seg.Low.S82
public import KAM.Magnetic.Data.Mag.Seg.Low.S83
public import KAM.Magnetic.Data.Mag.Seg.Low.S84
public import KAM.Magnetic.Data.Mag.Seg.Low.S85
public import KAM.Magnetic.Data.Mag.Seg.Low.S86
public import KAM.Magnetic.Data.Mag.Seg.Low.S87
public import KAM.Magnetic.Data.Mag.Seg.Low.S88
public import KAM.Magnetic.Data.Mag.Seg.Low.S89
public import KAM.Magnetic.Data.Mag.Seg.Low.S9
public import KAM.Magnetic.Data.Mag.Seg.Low.S90
public import KAM.Magnetic.Data.Mag.Seg.Low.S91
public import KAM.Magnetic.Data.Mag.Seg.Low.S92
public import KAM.Magnetic.Data.Mag.Seg.Low.S93
public import KAM.Magnetic.Data.Mag.Seg.Low.S94
public import KAM.Magnetic.Data.Mag.Seg.Low.S95
public import KAM.Magnetic.Data.Mag.Seg.Low.S96
public import KAM.Magnetic.Data.Mag.Seg.Low.S97
public import KAM.Magnetic.Data.Mag.Seg.Low.S98
public import KAM.Magnetic.Data.Mag.Seg.Low.S99
public import KAM.Magnetic.Data.Mag.Seg.PlanFull
public import KAM.Magnetic.Data.Mag.Seg.PlanLow
public import KAM.Magnetic.Data.Mag.Seg.StageMats
public import KAM.Magnetic.Support.CsegSupport

/-!
# The two composition chains (generated)

`planOk`, every `segOk`, `wantedOk`, and the cfgLow `compose_eq` instance.
Generated by `scripts/magnetic/mag_csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic.Data.Mag

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit KAM.Magnetic
open KAM.Magnetic.Data CertArith

theorem mag_jet : base.ham.jet = magJetLit := magJetLit_eq

theorem mag_fullPlan : magFullCkpt.planOk magJetLit.prog.ops.length = true := by decide +kernel

theorem mag_fullSegs :
    ∀ j < magFullCkpt.segs.length,
      magFullCkpt.segOk 2 magJetLit.prog.ops base.emb base.wit base.weight base.cfgFull base.piEnc j
          = true :=
  fun j hj => match j, hj with
    | 0, _ => magFull_seg0
    | 1, _ => magFull_seg1
    | 2, _ => magFull_seg2
    | 3, _ => magFull_seg3
    | 4, _ => magFull_seg4
    | 5, _ => magFull_seg5
    | 6, _ => magFull_seg6
    | 7, _ => magFull_seg7
    | 8, _ => magFull_seg8
    | 9, _ => magFull_seg9
    | 10, _ => magFull_seg10
    | 11, _ => magFull_seg11
    | 12, _ => magFull_seg12
    | 13, _ => magFull_seg13
    | 14, _ => magFull_seg14
    | 15, _ => magFull_seg15
    | 16, _ => magFull_seg16
    | 17, _ => magFull_seg17
    | 18, _ => magFull_seg18
    | 19, _ => magFull_seg19
    | 20, _ => magFull_seg20
    | 21, _ => magFull_seg21
    | 22, _ => magFull_seg22
    | 23, _ => magFull_seg23
    | 24, _ => magFull_seg24
    | 25, _ => magFull_seg25
    | 26, _ => magFull_seg26
    | 27, _ => magFull_seg27
    | 28, _ => magFull_seg28
    | 29, _ => magFull_seg29
    | 30, _ => magFull_seg30
    | 31, _ => magFull_seg31
    | 32, _ => magFull_seg32
    | 33, _ => magFull_seg33
    | 34, _ => magFull_seg34
    | 35, _ => magFull_seg35
    | 36, _ => magFull_seg36
    | 37, _ => magFull_seg37
    | 38, _ => magFull_seg38
    | 39, _ => magFull_seg39
    | 40, _ => magFull_seg40
    | 41, _ => magFull_seg41
    | 42, _ => magFull_seg42
    | 43, _ => magFull_seg43
    | 44, _ => magFull_seg44
    | 45, _ => magFull_seg45
    | 46, _ => magFull_seg46
    | 47, _ => magFull_seg47
    | 48, _ => magFull_seg48
    | 49, _ => magFull_seg49
    | 50, _ => magFull_seg50
    | 51, _ => magFull_seg51
    | 52, _ => magFull_seg52
    | 53, _ => magFull_seg53
    | 54, _ => magFull_seg54
    | 55, _ => magFull_seg55
    | 56, _ => magFull_seg56
    | j + 57, h => absurd h (by rw [show magFullCkpt.segs.length = 57 from rfl]; omega)

theorem mag_lowPlan : magLowCkpt.planOk magJetLit.prog.ops.length = true := by decide +kernel

theorem mag_lowSegs :
    ∀ j < magLowCkpt.segs.length,
      magLowCkpt.segOk 2 magJetLit.prog.ops base.emb base.wit base.weight base.cfgLow base.piEnc j =
          true :=
  fun j hj => match j, hj with
    | 0, _ => magLow_seg0
    | 1, _ => magLow_seg1
    | 2, _ => magLow_seg2
    | 3, _ => magLow_seg3
    | 4, _ => magLow_seg4
    | 5, _ => magLow_seg5
    | 6, _ => magLow_seg6
    | 7, _ => magLow_seg7
    | 8, _ => magLow_seg8
    | 9, _ => magLow_seg9
    | 10, _ => magLow_seg10
    | 11, _ => magLow_seg11
    | 12, _ => magLow_seg12
    | 13, _ => magLow_seg13
    | 14, _ => magLow_seg14
    | 15, _ => magLow_seg15
    | 16, _ => magLow_seg16
    | 17, _ => magLow_seg17
    | 18, _ => magLow_seg18
    | 19, _ => magLow_seg19
    | 20, _ => magLow_seg20
    | 21, _ => magLow_seg21
    | 22, _ => magLow_seg22
    | 23, _ => magLow_seg23
    | 24, _ => magLow_seg24
    | 25, _ => magLow_seg25
    | 26, _ => magLow_seg26
    | 27, _ => magLow_seg27
    | 28, _ => magLow_seg28
    | 29, _ => magLow_seg29
    | 30, _ => magLow_seg30
    | 31, _ => magLow_seg31
    | 32, _ => magLow_seg32
    | 33, _ => magLow_seg33
    | 34, _ => magLow_seg34
    | 35, _ => magLow_seg35
    | 36, _ => magLow_seg36
    | 37, _ => magLow_seg37
    | 38, _ => magLow_seg38
    | 39, _ => magLow_seg39
    | 40, _ => magLow_seg40
    | 41, _ => magLow_seg41
    | 42, _ => magLow_seg42
    | 43, _ => magLow_seg43
    | 44, _ => magLow_seg44
    | 45, _ => magLow_seg45
    | 46, _ => magLow_seg46
    | 47, _ => magLow_seg47
    | 48, _ => magLow_seg48
    | 49, _ => magLow_seg49
    | 50, _ => magLow_seg50
    | 51, _ => magLow_seg51
    | 52, _ => magLow_seg52
    | 53, _ => magLow_seg53
    | 54, _ => magLow_seg54
    | 55, _ => magLow_seg55
    | 56, _ => magLow_seg56
    | 57, _ => magLow_seg57
    | 58, _ => magLow_seg58
    | 59, _ => magLow_seg59
    | 60, _ => magLow_seg60
    | 61, _ => magLow_seg61
    | 62, _ => magLow_seg62
    | 63, _ => magLow_seg63
    | 64, _ => magLow_seg64
    | 65, _ => magLow_seg65
    | 66, _ => magLow_seg66
    | 67, _ => magLow_seg67
    | 68, _ => magLow_seg68
    | 69, _ => magLow_seg69
    | 70, _ => magLow_seg70
    | 71, _ => magLow_seg71
    | 72, _ => magLow_seg72
    | 73, _ => magLow_seg73
    | 74, _ => magLow_seg74
    | 75, _ => magLow_seg75
    | 76, _ => magLow_seg76
    | 77, _ => magLow_seg77
    | 78, _ => magLow_seg78
    | 79, _ => magLow_seg79
    | 80, _ => magLow_seg80
    | 81, _ => magLow_seg81
    | 82, _ => magLow_seg82
    | 83, _ => magLow_seg83
    | 84, _ => magLow_seg84
    | 85, _ => magLow_seg85
    | 86, _ => magLow_seg86
    | 87, _ => magLow_seg87
    | 88, _ => magLow_seg88
    | 89, _ => magLow_seg89
    | 90, _ => magLow_seg90
    | 91, _ => magLow_seg91
    | 92, _ => magLow_seg92
    | 93, _ => magLow_seg93
    | 94, _ => magLow_seg94
    | 95, _ => magLow_seg95
    | 96, _ => magLow_seg96
    | 97, _ => magLow_seg97
    | 98, _ => magLow_seg98
    | 99, _ => magLow_seg99
    | j + 100, h => absurd h (by rw [show magLowCkpt.segs.length = 100 from rfl]; omega)

theorem mag_fullWantedE : magFullCkpt.wantedOk [magJetLit.v0] = true := by decide +kernel
theorem mag_fullWantedI : magFullCkpt.wantedOk (d1Slots 2 magJetLit) = true := by decide +kernel
theorem mag_lowWanted : magLowCkpt.wantedOk (torsionSlots 2 magJetLit) = true := by decide +kernel

theorem mag_lowCompose :
    Slp.compose 2 base.ham.jet.prog base.emb base.wit base.weight base.cfgLow base.piEnc
      (torsionSlots 2 base.ham.jet) = some magMS := by
  rw [mag_jet]
  exact ComposeCkpt.compose_eq 2 base.emb base.wit base.weight base.cfgLow base.piEnc magLowCkpt
      mag_lowPlan
    mag_lowSegs mag_lowWanted

end KAM.Magnetic.Data.Mag
