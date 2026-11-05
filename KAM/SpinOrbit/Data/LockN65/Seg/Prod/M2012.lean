/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.AdvLookup
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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2012Sh
public import KAM.SpinOrbit.Data.LockN65.Seg.StageMats
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 2012 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM2012_shards_cover :
    ∀ s ∈ advLow.p1078.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5]], s ∈ g := by
  decide +kernel

theorem lockM2012_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5]], g.all (checkShardAt advLow.p1078.rr (advLow.p1078.rr.la.slotTerms
      (((lockM2012a.toMants base.cfgLow.toMant 112).getD ([], [])).1))
      (advLow.p1078.rr.lb.slotTerms (((lockM2012b.toMants base.cfgLow.toMant 112).getD ([],
      [])).1))) = true :=
  (List.forall_mem_cons.2 ⟨lockM2012_shardsG0, (List.forall_mem_cons.2 ⟨lockM2012_shardsG1, (fun _
    h => nomatch h)⟩)⟩)

theorem lockM2012_sp :
    checkPackedSp advLow.p1078.rr (advLow.p1078.rr.la.slotTerms (((lockM2012a.toMants
      base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p1078.rr.lb.slotTerms
      (((lockM2012b.toMants base.cfgLow.toMant 112).getD ([], [])).1)) = true :=
  checkPackedSp_of_groups advLow.p1078.rr (advLow.p1078.rr.la.slotTerms (((lockM2012a.toMants
        base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p1078.rr.lb.slotTerms
        (((lockM2012b.toMants base.cfgLow.toMant 112).getD ([], [])).1)) [[0, 1, 2, 3], [4, 5]]
        lockM2012A7 lockM2012_shards_cover lockM2012_shards_groups









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM2012_advAt :
    advLow.b5[78]? = some ([4, 9, 0, 0, 2], (.packed 112 advLow.p1078.rr advLow.p1078.ii
      advLow.p1078.ri advLow.p1078.ir))
    := rfl

/-- The packed product 2012 (cfgLow, key [4, 9, 0, 0, 2]). -/
theorem lockM2012 :
    CertModel.polyProduct base.weight base.cfgLow ([4, 9] ++ [0, 0, 2]) ((modelMatrixEntry
      (d1Models 2 lockMS) 0 2).poly) ((modelMatrixEntry (modelMatOmega 2 2 lockN0) 2 0).poly) =
      some (((⟨lockM2012T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
      (((([lockM2012RR_remN0, lockM2012RR_remN1].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 116 * 2 ^ (2
      * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).1.toErrTerms, ((⟨lockM2012T ++ [] ++ [] ++ []⟩
      : CertPoly LockBackend), (ofRatUp (((([lockM2012RR_remN0, lockM2012RR_remN1].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 116 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).2) := by
  rw [← lockM2012RR_rb, lockM2012b_eq, lockM2012a_eq]
  exact polyProduct_eq_of_mulPacked base.weight base.cfgLow ([4, 9] ++ [0, 0, 2]) lockM2012a
      lockM2012b
      112 advLow.p1078.rr advLow.p1078.ii advLow.p1078.ri advLow.p1078.ir
      ((⟨lockM2012T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advLow.p1078.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM2012A8 lockM2012A9 ((congrArg (fun b => adviceLookup b ([4, 9] ++ [0, 0, 2]))
          lock_advLow_blocks).trans ((adviceLookup_skip_cseg advLow.b0 _ ([4, 9] ++ [0, 0, 2]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b1 _ ([4, 9] ++ [0, 0, 2]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b2 _ ([4, 9] ++ [0, 0, 2]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b3 _ ([4, 9] ++ [0, 0, 2]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b4 _ ([4, 9] ++ [0, 0, 2]) (by
          decide +kernel)).trans (adviceLookup_at_cseg advLow.b5 _ ([4, 9] ++ [0, 0, 2]) 78 [4, 9,
          0, 0, 2] (.packed 112 advLow.p1078.rr advLow.p1078.ii advLow.p1078.ri advLow.p1078.ir) (by
          decide +kernel) lockM2012_advAt (by decide +kernel))))))))
      (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 112 advLow.p1078.rr
        advLow.p1078.ii advLow.p1078.ri advLow.p1078.ir lockM2012a lockM2012b
        (ma := ((lockM2012a.toMants base.cfgLow.toMant 112).getD ([], [])))
        (mb := ((lockM2012b.toMants base.cfgLow.toMant 112).getD ([], [])))
        (pRR := (advLow.p1078.rr.targetTerms, advLow.p1078.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM2012T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM2012A10)
        (eq_some_getD_cseg ([], []) lockM2012A11)
        (packedRealProduct_eq_of_sparse advLow.p1078.rr base.weight (2 * 112) (((lockM2012a.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) (((lockM2012b.toMants base.cfgLow.toMant
          112).getD ([], [])).1) lockM2012A0 lockM2012A1 lockM2012A2 lockM2012A3 lockM2012_sp)
        (packedRealProduct_eq_nil_left advLow.p1078.ii base.weight (2 * 112) (((lockM2012b.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM2012A4)
        (packedRealProduct_eq_nil_right advLow.p1078.ri base.weight (2 * 112) (((lockM2012a.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM2012A5)
        (packedRealProduct_eq_nil_left advLow.p1078.ir base.weight (2 * 112) (((lockM2012b.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM2012A6)
        lockM2012_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
