/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.Data.CsegJet
public import KAM.Magnetic.Data.Mag.Cert
public import KAM.Magnetic.Data.Mag.Seg.Memo00
public import KAM.Magnetic.Data.Mag.Seg.Memo01
public import KAM.Magnetic.Data.Mag.Seg.Memo02
public import KAM.Magnetic.Data.Mag.Seg.Memo03
public import KAM.Magnetic.Data.Mag.Seg.Memo04
public import KAM.Magnetic.Data.Mag.Seg.Memo05
public import KAM.Magnetic.Data.Mag.Seg.Memo06
public import KAM.Magnetic.Data.Mag.Seg.Memo07
public import KAM.Magnetic.Data.Mag.Seg.Memo08
public import KAM.Magnetic.Data.Mag.Seg.Memo09
public import KAM.Magnetic.Data.Mag.Seg.Memo10
public import KAM.Magnetic.Data.Mag.Seg.Memo100
public import KAM.Magnetic.Data.Mag.Seg.Memo101
public import KAM.Magnetic.Data.Mag.Seg.Memo102
public import KAM.Magnetic.Data.Mag.Seg.Memo103
public import KAM.Magnetic.Data.Mag.Seg.Memo104
public import KAM.Magnetic.Data.Mag.Seg.Memo105
public import KAM.Magnetic.Data.Mag.Seg.Memo106
public import KAM.Magnetic.Data.Mag.Seg.Memo107
public import KAM.Magnetic.Data.Mag.Seg.Memo108
public import KAM.Magnetic.Data.Mag.Seg.Memo109
public import KAM.Magnetic.Data.Mag.Seg.Memo11
public import KAM.Magnetic.Data.Mag.Seg.Memo110
public import KAM.Magnetic.Data.Mag.Seg.Memo111
public import KAM.Magnetic.Data.Mag.Seg.Memo112
public import KAM.Magnetic.Data.Mag.Seg.Memo113
public import KAM.Magnetic.Data.Mag.Seg.Memo114
public import KAM.Magnetic.Data.Mag.Seg.Memo115
public import KAM.Magnetic.Data.Mag.Seg.Memo116
public import KAM.Magnetic.Data.Mag.Seg.Memo117
public import KAM.Magnetic.Data.Mag.Seg.Memo118
public import KAM.Magnetic.Data.Mag.Seg.Memo119
public import KAM.Magnetic.Data.Mag.Seg.Memo12
public import KAM.Magnetic.Data.Mag.Seg.Memo120
public import KAM.Magnetic.Data.Mag.Seg.Memo121
public import KAM.Magnetic.Data.Mag.Seg.Memo122
public import KAM.Magnetic.Data.Mag.Seg.Memo123
public import KAM.Magnetic.Data.Mag.Seg.Memo124
public import KAM.Magnetic.Data.Mag.Seg.Memo125
public import KAM.Magnetic.Data.Mag.Seg.Memo126
public import KAM.Magnetic.Data.Mag.Seg.Memo127
public import KAM.Magnetic.Data.Mag.Seg.Memo128
public import KAM.Magnetic.Data.Mag.Seg.Memo129
public import KAM.Magnetic.Data.Mag.Seg.Memo13
public import KAM.Magnetic.Data.Mag.Seg.Memo130
public import KAM.Magnetic.Data.Mag.Seg.Memo131
public import KAM.Magnetic.Data.Mag.Seg.Memo132
public import KAM.Magnetic.Data.Mag.Seg.Memo133
public import KAM.Magnetic.Data.Mag.Seg.Memo134
public import KAM.Magnetic.Data.Mag.Seg.Memo135
public import KAM.Magnetic.Data.Mag.Seg.Memo14
public import KAM.Magnetic.Data.Mag.Seg.Memo15
public import KAM.Magnetic.Data.Mag.Seg.Memo16
public import KAM.Magnetic.Data.Mag.Seg.Memo17
public import KAM.Magnetic.Data.Mag.Seg.Memo18
public import KAM.Magnetic.Data.Mag.Seg.Memo19
public import KAM.Magnetic.Data.Mag.Seg.Memo20
public import KAM.Magnetic.Data.Mag.Seg.Memo21
public import KAM.Magnetic.Data.Mag.Seg.Memo22
public import KAM.Magnetic.Data.Mag.Seg.Memo23
public import KAM.Magnetic.Data.Mag.Seg.Memo24
public import KAM.Magnetic.Data.Mag.Seg.Memo25
public import KAM.Magnetic.Data.Mag.Seg.Memo26
public import KAM.Magnetic.Data.Mag.Seg.Memo27
public import KAM.Magnetic.Data.Mag.Seg.Memo28
public import KAM.Magnetic.Data.Mag.Seg.Memo29
public import KAM.Magnetic.Data.Mag.Seg.Memo30
public import KAM.Magnetic.Data.Mag.Seg.Memo31
public import KAM.Magnetic.Data.Mag.Seg.Memo32
public import KAM.Magnetic.Data.Mag.Seg.Memo33
public import KAM.Magnetic.Data.Mag.Seg.Memo34
public import KAM.Magnetic.Data.Mag.Seg.Memo35
public import KAM.Magnetic.Data.Mag.Seg.Memo36
public import KAM.Magnetic.Data.Mag.Seg.Memo37
public import KAM.Magnetic.Data.Mag.Seg.Memo38
public import KAM.Magnetic.Data.Mag.Seg.Memo39
public import KAM.Magnetic.Data.Mag.Seg.Memo40
public import KAM.Magnetic.Data.Mag.Seg.Memo41
public import KAM.Magnetic.Data.Mag.Seg.Memo42
public import KAM.Magnetic.Data.Mag.Seg.Memo43
public import KAM.Magnetic.Data.Mag.Seg.Memo44
public import KAM.Magnetic.Data.Mag.Seg.Memo45
public import KAM.Magnetic.Data.Mag.Seg.Memo46
public import KAM.Magnetic.Data.Mag.Seg.Memo47
public import KAM.Magnetic.Data.Mag.Seg.Memo48
public import KAM.Magnetic.Data.Mag.Seg.Memo49
public import KAM.Magnetic.Data.Mag.Seg.Memo50
public import KAM.Magnetic.Data.Mag.Seg.Memo51
public import KAM.Magnetic.Data.Mag.Seg.Memo52
public import KAM.Magnetic.Data.Mag.Seg.Memo53
public import KAM.Magnetic.Data.Mag.Seg.Memo54
public import KAM.Magnetic.Data.Mag.Seg.Memo55
public import KAM.Magnetic.Data.Mag.Seg.Memo56
public import KAM.Magnetic.Data.Mag.Seg.Memo57
public import KAM.Magnetic.Data.Mag.Seg.Memo58
public import KAM.Magnetic.Data.Mag.Seg.Memo59
public import KAM.Magnetic.Data.Mag.Seg.Memo60
public import KAM.Magnetic.Data.Mag.Seg.Memo61
public import KAM.Magnetic.Data.Mag.Seg.Memo62
public import KAM.Magnetic.Data.Mag.Seg.Memo63
public import KAM.Magnetic.Data.Mag.Seg.Memo64
public import KAM.Magnetic.Data.Mag.Seg.Memo65
public import KAM.Magnetic.Data.Mag.Seg.Memo66
public import KAM.Magnetic.Data.Mag.Seg.Memo67
public import KAM.Magnetic.Data.Mag.Seg.Memo68
public import KAM.Magnetic.Data.Mag.Seg.Memo69
public import KAM.Magnetic.Data.Mag.Seg.Memo70
public import KAM.Magnetic.Data.Mag.Seg.Memo71
public import KAM.Magnetic.Data.Mag.Seg.Memo72
public import KAM.Magnetic.Data.Mag.Seg.Memo73
public import KAM.Magnetic.Data.Mag.Seg.Memo74
public import KAM.Magnetic.Data.Mag.Seg.Memo75
public import KAM.Magnetic.Data.Mag.Seg.Memo76
public import KAM.Magnetic.Data.Mag.Seg.Memo77
public import KAM.Magnetic.Data.Mag.Seg.Memo78
public import KAM.Magnetic.Data.Mag.Seg.Memo79
public import KAM.Magnetic.Data.Mag.Seg.Memo80
public import KAM.Magnetic.Data.Mag.Seg.Memo81
public import KAM.Magnetic.Data.Mag.Seg.Memo82
public import KAM.Magnetic.Data.Mag.Seg.Memo83
public import KAM.Magnetic.Data.Mag.Seg.Memo84
public import KAM.Magnetic.Data.Mag.Seg.Memo85
public import KAM.Magnetic.Data.Mag.Seg.Memo86
public import KAM.Magnetic.Data.Mag.Seg.Memo87
public import KAM.Magnetic.Data.Mag.Seg.Memo88
public import KAM.Magnetic.Data.Mag.Seg.Memo89
public import KAM.Magnetic.Data.Mag.Seg.Memo90
public import KAM.Magnetic.Data.Mag.Seg.Memo91
public import KAM.Magnetic.Data.Mag.Seg.Memo92
public import KAM.Magnetic.Data.Mag.Seg.Memo93
public import KAM.Magnetic.Data.Mag.Seg.Memo94
public import KAM.Magnetic.Data.Mag.Seg.Memo95
public import KAM.Magnetic.Data.Mag.Seg.Memo96
public import KAM.Magnetic.Data.Mag.Seg.Memo97
public import KAM.Magnetic.Data.Mag.Seg.Memo98
public import KAM.Magnetic.Data.Mag.Seg.Memo99
public import KAM.Magnetic.Data.Mag.Seg.PlanFull
public import KAM.Magnetic.Data.Mag.Seg.Prod.M17Dec
public import KAM.Magnetic.Data.Mag.Seg.Prod.M17Sh
public import KAM.Magnetic.Support.CsegSupport

/-!
# Packed product 17 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/magnetic/mag_csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic.Data.Mag

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit KAM.Magnetic
open KAM.Magnetic.Data CertArith

theorem magM17A0 :
    ((((magFullCkpt.slotPair base.weight 610).1.poly.toMants base.cfgFull.toMant 128).getD ([],
      [])).1).isEmpty = true := by
  decide +kernel

theorem magM17A1 :
    ((((magFullCkpt.slotPair base.weight 592).1.poly.toMants base.cfgFull.toMant 128).getD ([],
      [])).2).isEmpty = true := by
  decide +kernel

theorem magM17A2 :
    ((((magFullCkpt.slotPair base.weight 610).1.poly.toMants base.cfgFull.toMant 128).getD ([],
      [])).1).isEmpty = true := by
  decide +kernel

theorem magM17A3 :
    ((((magFullCkpt.slotPair base.weight 610).1.poly.toMants base.cfgFull.toMant 128).getD ([],
      [])).2).isEmpty = false := by
  decide +kernel

theorem magM17A4 :
    ((((magFullCkpt.slotPair base.weight 592).1.poly.toMants base.cfgFull.toMant 128).getD ([],
      [])).1).isEmpty = false := by
  decide +kernel

theorem magM17A5 :
    advFull.p17.ir.la.allSlots ((((magFullCkpt.slotPair base.weight 610).1.poly.toMants
      base.cfgFull.toMant 128).getD ([], [])).2) = true := by
  decide +kernel

theorem magM17A6 :
    advFull.p17.ir.lb.allSlots ((((magFullCkpt.slotPair base.weight 592).1.poly.toMants
      base.cfgFull.toMant 128).getD ([], [])).1) = true := by
  decide +kernel

theorem magM17A7 :
    checkPackedSpPrefix advFull.p17.ir (advFull.p17.ir.la.slotTerms ((((magFullCkpt.slotPair
      base.weight 610).1.poly.toMants base.cfgFull.toMant 128).getD ([], [])).2))
      (advFull.p17.ir.lb.slotTerms ((((magFullCkpt.slotPair base.weight 592).1.poly.toMants
      base.cfgFull.toMant 128).getD ([], [])).1)) = true := by
  decide +kernel

theorem magM17_sp :
    checkPackedSp advFull.p17.ir (advFull.p17.ir.la.slotTerms ((((magFullCkpt.slotPair base.weight
      610).1.poly.toMants base.cfgFull.toMant 128).getD ([], [])).2)) (advFull.p17.ir.lb.slotTerms
      ((((magFullCkpt.slotPair base.weight 592).1.poly.toMants base.cfgFull.toMant 128).getD ([],
      [])).1)) = true :=
  checkPackedSp_of_groups advFull.p17.ir (advFull.p17.ir.la.slotTerms ((((magFullCkpt.slotPair
    base.weight 610).1.poly.toMants base.cfgFull.toMant 128).getD ([], [])).2))
    (advFull.p17.ir.lb.slotTerms ((((magFullCkpt.slotPair base.weight 592).1.poly.toMants
    base.cfgFull.toMant 128).getD ([], [])).1)) [advFull.p17.ir.shardRange] magM17A7
    (fun s hs => ⟨advFull.p17.ir.shardRange, List.mem_singleton_self _, hs⟩)
    (fun g hg => by rw [List.mem_singleton.1 hg]; exact magM17_shards)

theorem magM17A8 :
    (magFullCkpt.slotPair base.weight 610).1.poly.isConst = false := by
  decide +kernel

theorem magM17A9 :
    (magFullCkpt.slotPair base.weight 592).1.poly.isConst = false := by
  decide +kernel

theorem magM17A10 :
    (((magFullCkpt.slotPair base.weight 610).1.poly.toMants base.cfgFull.toMant 128)).isSome = true
      := by
  decide +kernel

theorem magM17A11 :
    (((magFullCkpt.slotPair base.weight 592).1.poly.toMants base.cfgFull.toMant 128)).isSome = true
      := by
  decide +kernel

/-- The packed product 17 (cfgFull, key [0, 627]). -/
theorem magM17 :
    CertModel.polyProduct base.weight base.cfgFull [0, (ComposeState.seed base.weight
      (magFullCkptMetas.getD 51 ⟨0, 0, 0, []⟩) magFullCkpt (magFullCkptSegs.getD 51 ⟨0, 0, [], [],
      []⟩).imports).len] (magFullCkpt.slotPair base.weight 610).1.poly (magFullCkpt.slotPair
      base.weight 592).1.poly = some (((⟨[] ++ [] ++ [] ++ magM17T⟩ : CertPoly MagBackend),
      (ofRatUp (0 + 0 + 0 + advFull.p17.ir.remainderBound base.weight (2 * 128)) :
      MagBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ magM17T⟩ : CertPoly MagBackend), (ofRatUp (0
      + 0 + 0 + advFull.p17.ir.remainderBound base.weight (2 * 128)) : MagBackend)).2) :=
  polyProduct_eq_of_mulPacked base.weight base.cfgFull
    [0, (ComposeState.seed base.weight (magFullCkptMetas.getD 51 ⟨0, 0, 0, []⟩) magFullCkpt
      (magFullCkptSegs.getD 51 ⟨0, 0, [], [], []⟩).imports).len]
    (magFullCkpt.slotPair base.weight 610).1.poly (magFullCkpt.slotPair base.weight 592).1.poly 128
    advFull.p17.rr advFull.p17.ii advFull.p17.ri advFull.p17.ir
    ((⟨[] ++ [] ++ [] ++ magM17T⟩ : CertPoly MagBackend), (ofRatUp (0 + 0 + 0 +
      advFull.p17.ir.remainderBound base.weight (2 * 128)) : MagBackend))
    magM17A8 magM17A9 rfl
    (CertPoly.mulPacked_eq_of_parts base.cfgFull.toMant base.weight 128 advFull.p17.rr
      advFull.p17.ii advFull.p17.ri advFull.p17.ir (magFullCkpt.slotPair base.weight 610).1.poly
      (magFullCkpt.slotPair base.weight 592).1.poly
      (ma := (((magFullCkpt.slotPair base.weight 610).1.poly.toMants base.cfgFull.toMant 128).getD
        ([], [])))
      (mb := (((magFullCkpt.slotPair base.weight 592).1.poly.toMants base.cfgFull.toMant 128).getD
        ([], [])))
      (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
      (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
      (pIR := (advFull.p17.ir.targetTerms, advFull.p17.ir.remainderBound base.weight (2 * 128)))
      (tRR := ([] : List (CertKey × CC MagBackend))) (tII := ([] : List (CertKey × CC MagBackend)))
      (tRI := ([] : List (CertKey × CC MagBackend))) (tIR := magM17T)
      (eq_some_getD_cseg ([], []) magM17A10)
      (eq_some_getD_cseg ([], []) magM17A11)
      (packedRealProduct_eq_nil_left advFull.p17.rr base.weight (2 * 128) ((((magFullCkpt.slotPair
        base.weight 592).1.poly.toMants base.cfgFull.toMant 128).getD ([], [])).1) magM17A0)
      (packedRealProduct_eq_nil_right advFull.p17.ii base.weight (2 * 128) ((((magFullCkpt.slotPair
        base.weight 610).1.poly.toMants base.cfgFull.toMant 128).getD ([], [])).2) magM17A1)
      (packedRealProduct_eq_nil_left advFull.p17.ri base.weight (2 * 128) ((((magFullCkpt.slotPair
        base.weight 592).1.poly.toMants base.cfgFull.toMant 128).getD ([], [])).2) magM17A2)
      (packedRealProduct_eq_of_sparse advFull.p17.ir base.weight (2 * 128) ((((magFullCkpt.slotPair
        base.weight 610).1.poly.toMants base.cfgFull.toMant 128).getD ([], [])).2)
        ((((magFullCkpt.slotPair base.weight 592).1.poly.toMants base.cfgFull.toMant 128).getD ([],
        [])).1) magM17A3 magM17A4 magM17A5 magM17A6 magM17_sp)
      (dyadicTerms_nil_cseg _ _ _)
      (dyadicTerms_nil_cseg _ _ _)
      (dyadicTerms_nil_cseg _ _ _)
      magM17_dec)

end KAM.Magnetic.Data.Mag
