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
public import KAM.Magnetic.Data.Mag.Seg.Prod.M198Dec
public import KAM.Magnetic.Data.Mag.Seg.Prod.M198Sh
public import KAM.Magnetic.Support.CsegSupport

/-!
# Packed product 198 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/magnetic/mag_csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic.Data.Mag

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit KAM.Magnetic
open KAM.Magnetic.Data CertArith

theorem magM198A0 :
    ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).1).isEmpty = false := by
  decide +kernel

theorem magM198A1 :
    ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).1).isEmpty = false := by
  decide +kernel

theorem magM198A2 :
    advLow.p0.rr.la.allSlots ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).1) = true := by
  decide +kernel

theorem magM198A3 :
    advLow.p0.rr.lb.allSlots ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).1) = true := by
  decide +kernel

theorem magM198A4 :
    ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2).isEmpty = true := by
  decide +kernel

theorem magM198A5 :
    ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2).isEmpty = true := by
  decide +kernel

theorem magM198A6 :
    ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2).isEmpty = true := by
  decide +kernel

theorem magM198A7 :
    checkPackedSpPrefix advLow.p0.rr (advLow.p0.rr.la.slotTerms ((((dkAngleModel 2 base.emb
      base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1))
      (advLow.p0.rr.lb.slotTerms ((((dkAngleModel 2 base.emb base.weight base.piEnc 0
      0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1)) = true := by
  decide +kernel

theorem magM198_sp :
    checkPackedSp advLow.p0.rr (advLow.p0.rr.la.slotTerms ((((dkAngleModel 2 base.emb base.weight
      base.piEnc 0 0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1))
      (advLow.p0.rr.lb.slotTerms ((((dkAngleModel 2 base.emb base.weight base.piEnc 0
      0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1)) = true :=
  checkPackedSp_of_groups advLow.p0.rr (advLow.p0.rr.la.slotTerms ((((dkAngleModel 2 base.emb
    base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1))
    (advLow.p0.rr.lb.slotTerms ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants
    base.cfgLow.toMant 128).getD ([], [])).1)) [advLow.p0.rr.shardRange] magM198A7
    (fun s hs => ⟨advLow.p0.rr.shardRange, List.mem_singleton_self _, hs⟩)
    (fun g hg => by rw [List.mem_singleton.1 hg]; exact magM198_shards)

theorem magM198A8 :
    (dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.isConst = false := by
  decide +kernel

theorem magM198A9 :
    (dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.isConst = false := by
  decide +kernel

theorem magM198A10 :
    (((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
      128)).isSome = true := by
  decide +kernel

theorem magM198A11 :
    (((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
      128)).isSome = true := by
  decide +kernel

/-- The packed product 198 (cfgLow, key [3, 0, 0, 0, 0]). -/
theorem magM198 :
    CertModel.polyProduct base.weight base.cfgLow [3, 0, 0, 0, 0] (dkAngleModel 2 base.emb
      base.weight base.piEnc 0 0).poly (dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly =
      some (((⟨magM198T ++ [] ++ [] ++ []⟩ : CertPoly MagBackend), (ofRatUp
      (advLow.p0.rr.remainderBound base.weight (2 * 128) + 0 + 0 + 0) : MagBackend)).1.toErrTerms,
      ((⟨magM198T ++ [] ++ [] ++ []⟩ : CertPoly MagBackend), (ofRatUp (advLow.p0.rr.remainderBound
      base.weight (2 * 128) + 0 + 0 + 0) : MagBackend)).2) :=
  polyProduct_eq_of_mulPacked base.weight base.cfgLow [3, 0, 0, 0, 0]
    (dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly
    (dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly 128 advLow.p0.rr advLow.p0.ii
    advLow.p0.ri advLow.p0.ir
    ((⟨magM198T ++ [] ++ [] ++ []⟩ : CertPoly MagBackend), (ofRatUp (advLow.p0.rr.remainderBound
      base.weight (2 * 128) + 0 + 0 + 0) : MagBackend))
    magM198A8 magM198A9 rfl
    (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 128 advLow.p0.rr advLow.p0.ii
      advLow.p0.ri advLow.p0.ir (dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly
      (dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly
      (ma := (((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
        128).getD ([], [])))
      (mb := (((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
        128).getD ([], [])))
      (pRR := (advLow.p0.rr.targetTerms, advLow.p0.rr.remainderBound base.weight (2 * 128)))
      (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
      (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := magM198T)
      (tII := ([] : List (CertKey × CC MagBackend))) (tRI := ([] : List (CertKey × CC MagBackend)))
      (tIR := ([] : List (CertKey × CC MagBackend)))
      (eq_some_getD_cseg ([], []) magM198A10)
      (eq_some_getD_cseg ([], []) magM198A11)
      (packedRealProduct_eq_of_sparse advLow.p0.rr base.weight (2 * 128) ((((dkAngleModel 2
        base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1)
        ((((dkAngleModel 2 base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant
        128).getD ([], [])).1) magM198A0 magM198A1 magM198A2 magM198A3 magM198_sp)
      (packedRealProduct_eq_nil_left advLow.p0.ii base.weight (2 * 128) ((((dkAngleModel 2 base.emb
        base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).2)
        magM198A4)
      (packedRealProduct_eq_nil_right advLow.p0.ri base.weight (2 * 128) ((((dkAngleModel 2
        base.emb base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1)
        magM198A5)
      (packedRealProduct_eq_nil_left advLow.p0.ir base.weight (2 * 128) ((((dkAngleModel 2 base.emb
        base.weight base.piEnc 0 0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1)
        magM198A6)
      magM198_dec
      (dyadicTerms_nil_cseg _ _ _)
      (dyadicTerms_nil_cseg _ _ _)
      (dyadicTerms_nil_cseg _ _ _))

end KAM.Magnetic.Data.Mag
