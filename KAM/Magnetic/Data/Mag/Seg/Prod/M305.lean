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
public import KAM.Magnetic.Data.Mag.Seg.Prod.M305Dec
public import KAM.Magnetic.Data.Mag.Seg.Prod.M305Sh
public import KAM.Magnetic.Data.Mag.Seg.StageMats
public import KAM.Magnetic.Support.CsegSupport

/-!
# Packed product 305 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/magnetic/mag_csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic.Data.Mag

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit KAM.Magnetic
open KAM.Magnetic.Data CertArith

theorem magM305A0 :
    ((((modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).1).isEmpty = true := by
  decide +kernel

theorem magM305A1 :
    ((((modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).2).isEmpty = false := by
  decide +kernel

theorem magM305A2 :
    ((((modelMatrixEntry (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1
      (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2
      magDN1 magDN2))))) 0 1).poly.toMants base.cfgLow.toMant 128).getD ([], [])).2).isEmpty =
      false := by
  decide +kernel

theorem magM305A3 :
    advLow.p206.ii.la.allSlots ((((modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2
      magN0)) 0 0).poly.toMants base.cfgLow.toMant 128).getD ([], [])).2) = true := by
  decide +kernel

theorem magM305A4 :
    advLow.p206.ii.lb.allSlots ((((modelMatrixEntry (modelMatOmega 2 2 (modelMatAdd base.weight
      base.piEnc (2 + 2) 2 magXN1 (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2 (modelMatAdd
      base.weight base.piEnc (2 + 2) 2 magDN1 magDN2))))) 0 1).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2) = true := by
  decide +kernel

theorem magM305A5 :
    ((((modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).1).isEmpty = true := by
  decide +kernel

theorem magM305A6 :
    ((((modelMatrixEntry (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1
      (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2
      magDN1 magDN2))))) 0 1).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1).isEmpty = true
      := by
  decide +kernel

theorem magM305A7 :
    checkPackedSpPrefix advLow.p206.ii (advLow.p206.ii.la.slotTerms ((((modelMatrixEntry
      (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2)) (advLow.p206.ii.lb.slotTerms ((((modelMatrixEntry (modelMatOmega 2 2
      (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1 (modelMatNeg (2 + 2) 2 (modelMatOmega 2
      2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magDN1 magDN2))))) 0 1).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).2)) = true := by
  decide +kernel

theorem magM305_sp :
    checkPackedSp advLow.p206.ii (advLow.p206.ii.la.slotTerms ((((modelMatrixEntry
      (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants base.cfgLow.toMant
      128).getD ([], [])).2)) (advLow.p206.ii.lb.slotTerms ((((modelMatrixEntry (modelMatOmega 2 2
      (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1 (modelMatNeg (2 + 2) 2 (modelMatOmega 2
      2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magDN1 magDN2))))) 0 1).poly.toMants
      base.cfgLow.toMant 128).getD ([], [])).2)) = true :=
  checkPackedSp_of_groups advLow.p206.ii (advLow.p206.ii.la.slotTerms ((((modelMatrixEntry
    (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants base.cfgLow.toMant
    128).getD ([], [])).2)) (advLow.p206.ii.lb.slotTerms ((((modelMatrixEntry (modelMatOmega 2 2
    (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1 (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2
    (modelMatAdd base.weight base.piEnc (2 + 2) 2 magDN1 magDN2))))) 0 1).poly.toMants
    base.cfgLow.toMant 128).getD ([], [])).2)) [advLow.p206.ii.shardRange] magM305A7
    (fun s hs => ⟨advLow.p206.ii.shardRange, List.mem_singleton_self _, hs⟩)
    (fun g hg => by rw [List.mem_singleton.1 hg]; exact magM305_shards)

theorem magM305A8 :
    (modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.isConst =
      false := by
  decide +kernel

theorem magM305A9 :
    (modelMatrixEntry (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1
      (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2
      magDN1 magDN2))))) 0 1).poly.isConst = false := by
  decide +kernel

theorem magM305A10 :
    (((modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants
      base.cfgLow.toMant 128)).isSome = true := by
  decide +kernel

theorem magM305A11 :
    (((modelMatrixEntry (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1
      (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2
      magDN1 magDN2))))) 0 1).poly.toMants base.cfgLow.toMant 128)).isSome = true := by
  decide +kernel

/-- The packed product 305 (cfgLow, key [4, 8, 0, 1, 0]). -/
theorem magM305 :
    CertModel.polyProduct base.weight base.cfgLow ([4, 8] ++ [0, 1, 0]) (modelMatrixEntry
      (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly (modelMatrixEntry
      (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1 (modelMatNeg (2 + 2)
      2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magDN1 magDN2))))) 0
      1).poly = some (((⟨[] ++ magM305T ++ [] ++ []⟩ : CertPoly MagBackend), (ofRatUp (0 +
      advLow.p206.ii.remainderBound base.weight (2 * 128) + 0 + 0) : MagBackend)).1.toErrTerms,
      ((⟨[] ++ magM305T ++ [] ++ []⟩ : CertPoly MagBackend), (ofRatUp (0 +
      advLow.p206.ii.remainderBound base.weight (2 * 128) + 0 + 0) : MagBackend)).2) :=
  polyProduct_eq_of_mulPacked base.weight base.cfgLow ([4, 8] ++ [0, 1, 0])
    (modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly
    (modelMatrixEntry (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1
      (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2
      magDN1 magDN2))))) 0 1).poly
    128 advLow.p206.rr advLow.p206.ii advLow.p206.ri advLow.p206.ir
    ((⟨[] ++ magM305T ++ [] ++ []⟩ : CertPoly MagBackend), (ofRatUp (0 +
      advLow.p206.ii.remainderBound base.weight (2 * 128) + 0 + 0) : MagBackend))
    magM305A8 magM305A9 rfl
    (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 128 advLow.p206.rr
      advLow.p206.ii advLow.p206.ri advLow.p206.ir
      (modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly
      (modelMatrixEntry (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1
        (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2
        magDN1 magDN2))))) 0 1).poly
      (ma := (((modelMatrixEntry (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0
        0).poly.toMants base.cfgLow.toMant 128).getD ([], [])))
      (mb := (((modelMatrixEntry (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2
        magXN1 (modelMatNeg (2 + 2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 +
        2) 2 magDN1 magDN2))))) 0 1).poly.toMants base.cfgLow.toMant 128).getD ([], [])))
      (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ)))
      (pII := (advLow.p206.ii.targetTerms, advLow.p206.ii.remainderBound base.weight (2 * 128)))
      (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ)))
      (tRR := ([] : List (CertKey × CC MagBackend))) (tII := magM305T)
      (tRI := ([] : List (CertKey × CC MagBackend))) (tIR := ([] : List (CertKey × CC MagBackend)))
      (eq_some_getD_cseg ([], []) magM305A10)
      (eq_some_getD_cseg ([], []) magM305A11)
      (packedRealProduct_eq_nil_left advLow.p206.rr base.weight (2 * 128) ((((modelMatrixEntry
        (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1 (modelMatNeg (2 +
        2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magDN1 magDN2))))) 0
        1).poly.toMants base.cfgLow.toMant 128).getD ([], [])).1) magM305A0)
      (packedRealProduct_eq_of_sparse advLow.p206.ii base.weight (2 * 128) ((((modelMatrixEntry
        (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants
        base.cfgLow.toMant 128).getD ([], [])).2) ((((modelMatrixEntry (modelMatOmega 2 2
        (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1 (modelMatNeg (2 + 2) 2 (modelMatOmega
        2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magDN1 magDN2))))) 0 1).poly.toMants
        base.cfgLow.toMant 128).getD ([], [])).2) magM305A1 magM305A2 magM305A3 magM305A4
        magM305_sp)
      (packedRealProduct_eq_nil_left advLow.p206.ri base.weight (2 * 128) ((((modelMatrixEntry
        (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magXN1 (modelMatNeg (2 +
        2) 2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 magDN1 magDN2))))) 0
        1).poly.toMants base.cfgLow.toMant 128).getD ([], [])).2) magM305A5)
      (packedRealProduct_eq_nil_right advLow.p206.ir base.weight (2 * 128) ((((modelMatrixEntry
        (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 magN0)) 0 0).poly.toMants
        base.cfgLow.toMant 128).getD ([], [])).2) magM305A6)
      (dyadicTerms_nil_cseg _ _ _)
      magM305_dec
      (dyadicTerms_nil_cseg _ _ _)
      (dyadicTerms_nil_cseg _ _ _))

end KAM.Magnetic.Data.Mag
