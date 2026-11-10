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
public import KAM.Magnetic.Data.Mag.Seg.Prod.M242Dec
public import KAM.Magnetic.Data.Mag.Seg.Prod.M242Sh
public import KAM.Magnetic.Data.Mag.Seg.StageMats
public import KAM.Magnetic.Support.CsegSupport

/-!
# Packed product 242 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/magnetic/mag_csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic.Data.Mag

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit KAM.Magnetic
open KAM.Magnetic.Data CertArith

theorem magM242A0 :
    ((((modelMatrixEntry magTDL 0 1).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1).isEmpty
      = true := by
  decide +kernel

theorem magM242A1 :
    ((((modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2).isEmpty = true := by
  decide +kernel

theorem magM242A2 :
    ((((modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).1).isEmpty = false := by
  decide +kernel

theorem magM242A3 :
    ((((modelMatrixEntry magTDL 0 1).poly.toMants base.cfgLow.toMant 128).getD ([], [])).2).isEmpty
      = false := by
  decide +kernel

theorem magM242A4 :
    advLow.p143.ri.la.allSlots ((((modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0
      0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1) = true := by
  decide +kernel

theorem magM242A5 :
    advLow.p143.ri.lb.allSlots ((((modelMatrixEntry magTDL 0 1).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2) = true := by
  decide +kernel

theorem magM242A6 :
    ((((modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2).isEmpty = true := by
  decide +kernel

theorem magM242A7 :
    checkPackedSpPrefix advLow.p143.ri (advLow.p143.ri.la.slotTerms ((((modelMatrixEntry
      (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant 128).getD ([],
      [])).1)) (advLow.p143.ri.lb.slotTerms ((((modelMatrixEntry magTDL 0 1).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).2)) = true := by
  decide +kernel

theorem magM242_sp :
    checkPackedSp advLow.p143.ri (advLow.p143.ri.la.slotTerms ((((modelMatrixEntry
      (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant 128).getD ([],
      [])).1)) (advLow.p143.ri.lb.slotTerms ((((modelMatrixEntry magTDL 0 1).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).2)) = true :=
  checkPackedSp_of_groups advLow.p143.ri (advLow.p143.ri.la.slotTerms ((((modelMatrixEntry
    (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant 128).getD ([],
    [])).1)) (advLow.p143.ri.lb.slotTerms ((((modelMatrixEntry magTDL 0 1).poly.toMants
    base.cfgLow.toMant 128).getD ([], [])).2)) [advLow.p143.ri.shardRange] magM242A7
    (fun s hs => ⟨advLow.p143.ri.shardRange, List.mem_singleton_self _, hs⟩)
    (fun g hg => by rw [List.mem_singleton.1 hg]; exact magM242_shards)

theorem magM242A8 :
    (modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.isConst = false := by
  decide +kernel

theorem magM242A9 :
    (modelMatrixEntry magTDL 0 1).poly.isConst = false := by
  decide +kernel

theorem magM242A10 :
    (((modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant
      128)).isSome = true := by
  decide +kernel

theorem magM242A11 :
    (((modelMatrixEntry magTDL 0 1).poly.toMants base.cfgLow.toMant 128)).isSome = true := by
  decide +kernel

/-- The packed product 242 (cfgLow, key [4, 2, 0, 1, 0]). -/
theorem magM242 :
    CertModel.polyProduct base.weight base.cfgLow ([4, 2] ++ [0, 1, 0]) (modelMatrixEntry
      (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly (modelMatrixEntry magTDL 0 1).poly = some
      (((⟨[] ++ [] ++ magM242T ++ []⟩ : CertPoly MagBackend), (ofRatUp (0 + 0 +
      advLow.p143.ri.remainderBound base.weight (2 * 128) + 0) : MagBackend)).1.toErrTerms, ((⟨[]
      ++ [] ++ magM242T ++ []⟩ : CertPoly MagBackend), (ofRatUp (0 + 0 +
      advLow.p143.ri.remainderBound base.weight (2 * 128) + 0) : MagBackend)).2) :=
  polyProduct_eq_of_mulPacked base.weight base.cfgLow ([4, 2] ++ [0, 1, 0])
    (modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly
    (modelMatrixEntry magTDL 0 1).poly 128 advLow.p143.rr advLow.p143.ii advLow.p143.ri
    advLow.p143.ir
    ((⟨[] ++ [] ++ magM242T ++ []⟩ : CertPoly MagBackend), (ofRatUp (0 + 0 +
      advLow.p143.ri.remainderBound base.weight (2 * 128) + 0) : MagBackend))
    magM242A8 magM242A9 rfl
    (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 128 advLow.p143.rr
      advLow.p143.ii advLow.p143.ri advLow.p143.ir
      (modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly
      (modelMatrixEntry magTDL 0 1).poly
      (ma := (((modelMatrixEntry (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants
        base.cfgLow.toMant 128).getD ([], [])))
      (mb := (((modelMatrixEntry magTDL 0 1).poly.toMants base.cfgLow.toMant 128).getD ([], [])))
      (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
      (pRI := (advLow.p143.ri.targetTerms, advLow.p143.ri.remainderBound base.weight (2 * 128)))
      (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := ([] : List (CertKey × CC MagBackend)))
      (tII := ([] : List (CertKey × CC MagBackend))) (tRI := magM242T)
      (tIR := ([] : List (CertKey × CC MagBackend)))
      (eq_some_getD_cseg ([], []) magM242A10)
      (eq_some_getD_cseg ([], []) magM242A11)
      (packedRealProduct_eq_nil_right advLow.p143.rr base.weight (2 * 128) ((((modelMatrixEntry
        (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant 128).getD ([],
        [])).1) magM242A0)
      (packedRealProduct_eq_nil_left advLow.p143.ii base.weight (2 * 128) ((((modelMatrixEntry
        magTDL 0 1).poly.toMants base.cfgLow.toMant 128).getD ([], [])).2) magM242A1)
      (packedRealProduct_eq_of_sparse advLow.p143.ri base.weight (2 * 128) ((((modelMatrixEntry
        (modelMatTranspose (2 + 2) 2 magTL) 0 0).poly.toMants base.cfgLow.toMant 128).getD ([],
        [])).1) ((((modelMatrixEntry magTDL 0 1).poly.toMants base.cfgLow.toMant 128).getD ([],
        [])).2) magM242A2 magM242A3 magM242A4 magM242A5 magM242_sp)
      (packedRealProduct_eq_nil_left advLow.p143.ir base.weight (2 * 128) ((((modelMatrixEntry
        magTDL 0 1).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1) magM242A6)
      (dyadicTerms_nil_cseg _ _ _)
      (dyadicTerms_nil_cseg _ _ _)
      magM242_dec
      (dyadicTerms_nil_cseg _ _ _))

end KAM.Magnetic.Data.Mag
