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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011IIRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2011Sh
public import KAM.SpinOrbit.Data.LockN65.Seg.StageMats
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 2011 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM2011_shards_cover :
    ∀ s ∈ advLow.p1077.ii.shardRange, ∃ g ∈ [[0, 1, 2, 3]], s ∈ g := by
  decide +kernel

theorem lockM2011_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3]], g.all (checkShardAt advLow.p1077.ii (advLow.p1077.ii.la.slotTerms
      (((lockM2011a.toMants base.cfgLow.toMant 112).getD ([], [])).2))
      (advLow.p1077.ii.lb.slotTerms (((lockM2011b.toMants base.cfgLow.toMant 112).getD ([],
      [])).2))) = true :=
  (List.forall_mem_cons.2 ⟨lockM2011_shardsG0, (fun _ h => nomatch h)⟩)

theorem lockM2011_sp :
    checkPackedSp advLow.p1077.ii (advLow.p1077.ii.la.slotTerms (((lockM2011a.toMants
      base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1077.ii.lb.slotTerms
      (((lockM2011b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) = true :=
  checkPackedSp_of_groups advLow.p1077.ii (advLow.p1077.ii.la.slotTerms (((lockM2011a.toMants
        base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1077.ii.lb.slotTerms
        (((lockM2011b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) [[0, 1, 2, 3]] lockM2011A7
        lockM2011_shards_cover lockM2011_shards_groups









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM2011_advAt :
    advLow.b5[77]? = some ([4, 9, 0, 0, 1], (.packed 112 advLow.p1077.rr advLow.p1077.ii
      advLow.p1077.ri advLow.p1077.ir))
    := rfl

/-- The packed product 2011 (cfgLow, key [4, 9, 0, 0, 1]). -/
theorem lockM2011 :
    CertModel.polyProduct base.weight base.cfgLow ([4, 9] ++ [0, 0, 1]) ((modelMatrixEntry
      (d1Models 2 lockMS) 0 1).poly) ((modelMatrixEntry (modelMatOmega 2 2 lockN0) 1 0).poly) =
      some (((⟨[] ++ lockM2011T ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 +
      ((([lockM2011II_remN0].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 80 * 2 ^ (2 * 112) : ℕ) : ℚ)) +
      0 + 0) : LockBackend)).1.toErrTerms, ((⟨[] ++ lockM2011T ++ [] ++ []⟩ : CertPoly
      LockBackend), (ofRatUp (0 + ((([lockM2011II_remN0].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 80 *
      2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0) : LockBackend)).2) := by
  rw [← lockM2011II_rb, lockM2011b_eq, lockM2011a_eq]
  exact polyProduct_eq_of_mulPacked base.weight base.cfgLow ([4, 9] ++ [0, 0, 1]) lockM2011a
      lockM2011b
      112 advLow.p1077.rr advLow.p1077.ii advLow.p1077.ri advLow.p1077.ir
      ((⟨[] ++ lockM2011T ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 +
        advLow.p1077.ii.remainderBound base.weight (2 * 112) + 0 + 0) : LockBackend))
      lockM2011A8 lockM2011A9 ((congrArg (fun b => adviceLookup b ([4, 9] ++ [0, 0, 1]))
          lock_advLow_blocks).trans ((adviceLookup_skip_cseg advLow.b0 _ ([4, 9] ++ [0, 0, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b1 _ ([4, 9] ++ [0, 0, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b2 _ ([4, 9] ++ [0, 0, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b3 _ ([4, 9] ++ [0, 0, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b4 _ ([4, 9] ++ [0, 0, 1]) (by
          decide +kernel)).trans (adviceLookup_at_cseg advLow.b5 _ ([4, 9] ++ [0, 0, 1]) 77 [4, 9,
          0, 0, 1] (.packed 112 advLow.p1077.rr advLow.p1077.ii advLow.p1077.ri advLow.p1077.ir) (by
          decide +kernel) lockM2011_advAt (by decide +kernel))))))))
      (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 112 advLow.p1077.rr
        advLow.p1077.ii advLow.p1077.ri advLow.p1077.ir lockM2011a lockM2011b
        (ma := ((lockM2011a.toMants base.cfgLow.toMant 112).getD ([], [])))
        (mb := ((lockM2011b.toMants base.cfgLow.toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pII := (advLow.p1077.ii.targetTerms, advLow.p1077.ii.remainderBound base.weight (2 * 112)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (tRR := ([] : List (CertKey × CC LockBackend))) (tII := lockM2011T)
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM2011A10)
        (eq_some_getD_cseg ([], []) lockM2011A11)
        (packedRealProduct_eq_nil_left advLow.p1077.rr base.weight (2 * 112) (((lockM2011b.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM2011A0)
        (packedRealProduct_eq_of_sparse advLow.p1077.ii base.weight (2 * 112) (((lockM2011a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) (((lockM2011b.toMants base.cfgLow.toMant
          112).getD ([], [])).2) lockM2011A1 lockM2011A2 lockM2011A3 lockM2011A4 lockM2011_sp)
        (packedRealProduct_eq_nil_left advLow.p1077.ri base.weight (2 * 112) (((lockM2011b.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM2011A5)
        (packedRealProduct_eq_nil_right advLow.p1077.ir base.weight (2 * 112) (((lockM2011a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM2011A6)
        (dyadicTerms_nil_cseg _ _ _)
        lockM2011_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
