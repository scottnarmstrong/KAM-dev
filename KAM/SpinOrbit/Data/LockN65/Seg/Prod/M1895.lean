/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Jet
public import KAM.SpinOrbit.Data.LockN65.Seg.CharE
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo00
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo01
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo02
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo03
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo04
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo05
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo06
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo07
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo08
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo09
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo10
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo11
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo12
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo13
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo14
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo15
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo16
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo17
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo18
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo19
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo20
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo21
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo22
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo23
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo24
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo25
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo26
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo27
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo28
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo29
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo30
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo31
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo32
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo33
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo34
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo35
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo36
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo37
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo38
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo39
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo40
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo41
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo42
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo43
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo44
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo45
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo46
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo47
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo48
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo49
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo50
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo51
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo52
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo53
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo54
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo55
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo56
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo57
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo58
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo59
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo60
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo61
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo62
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo63
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo64
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo65
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo66
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo67
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo68
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo69
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo70
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo71
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo72
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo73
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo74
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo75
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo76
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo77
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo78
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo79
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo80
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo81
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo82
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo83
public import KAM.SpinOrbit.Data.LockN65.Seg.Memo84
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1895Sh
public import KAM.SpinOrbit.Data.LockN65.Seg.StageMats
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1895 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1895_shards_cover :
    ∀ s ∈ advLow.p12.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5]], s ∈ g := by
  decide +kernel

theorem lockM1895_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5]], g.all (checkShardAt advLow.p12.rr (advLow.p12.rr.la.slotTerms
      (((lockM1895a.toMants base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p12.rr.lb.slotTerms
      (((lockM1895b.toMants base.cfgLow.toMant 112).getD ([], [])).1))) = true :=
  (List.forall_mem_cons.2 ⟨lockM1895_shardsG0, (List.forall_mem_cons.2 ⟨lockM1895_shardsG1, (fun _
    h => nomatch h)⟩)⟩)

theorem lockM1895_sp :
    checkPackedSp advLow.p12.rr (advLow.p12.rr.la.slotTerms (((lockM1895a.toMants
      base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p12.rr.lb.slotTerms (((lockM1895b.toMants
      base.cfgLow.toMant 112).getD ([], [])).1)) = true :=
  checkPackedSp_of_groups advLow.p12.rr (advLow.p12.rr.la.slotTerms (((lockM1895a.toMants
        base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p12.rr.lb.slotTerms
        (((lockM1895b.toMants base.cfgLow.toMant 112).getD ([], [])).1)) [[0, 1, 2, 3], [4, 5]]
        lockM1895A7 lockM1895_shards_cover lockM1895_shards_groups









/-- The packed product 1895 (cfgLow, key [3, 1, 0, 1, 1]). -/
theorem lockM1895 :
    CertModel.polyProduct base.weight base.cfgLow [3, 1, 0, 1, 1] ((⟨0, gramInvPoly base.gramInv 0
      1, ofInt 0⟩ : CertModel LockBackend).poly) ((modelMatrixEntry lockGm 1 1).poly) = some
      (((⟨lockM1895T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (((([lockM1895RR_remN0,
      lockM1895RR_remN1].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 102 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 +
      0 + 0) : LockBackend)).1.toErrTerms, ((⟨lockM1895T ++ [] ++ [] ++ []⟩ : CertPoly
      LockBackend), (ofRatUp (((([lockM1895RR_remN0, lockM1895RR_remN1].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 102 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).2) := by
  rw [← lockM1895RR_rb, lockM1895a_eq, lockM1895b_eq]
  exact polyProduct_eq_of_mulPacked base.weight base.cfgLow [3, 1, 0, 1, 1] lockM1895a lockM1895b
      112
      advLow.p12.rr advLow.p12.ii advLow.p12.ri advLow.p12.ir
      ((⟨lockM1895T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advLow.p12.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM1895A8 lockM1895A9 rfl
      (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 112 advLow.p12.rr advLow.p12.ii
        advLow.p12.ri advLow.p12.ir lockM1895a lockM1895b
        (ma := ((lockM1895a.toMants base.cfgLow.toMant 112).getD ([], [])))
        (mb := ((lockM1895b.toMants base.cfgLow.toMant 112).getD ([], [])))
        (pRR := (advLow.p12.rr.targetTerms, advLow.p12.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM1895T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM1895A10)
        (eq_some_getD_cseg ([], []) lockM1895A11)
        (packedRealProduct_eq_of_sparse advLow.p12.rr base.weight (2 * 112) (((lockM1895a.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) (((lockM1895b.toMants base.cfgLow.toMant
          112).getD ([], [])).1) lockM1895A0 lockM1895A1 lockM1895A2 lockM1895A3 lockM1895_sp)
        (packedRealProduct_eq_nil_left advLow.p12.ii base.weight (2 * 112) (((lockM1895b.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM1895A4)
        (packedRealProduct_eq_nil_right advLow.p12.ri base.weight (2 * 112) (((lockM1895a.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM1895A5)
        (packedRealProduct_eq_nil_left advLow.p12.ir base.weight (2 * 112) (((lockM1895b.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM1895A6)
        lockM1895_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
