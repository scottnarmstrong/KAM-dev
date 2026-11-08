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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975IIRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1975Sh
public import KAM.SpinOrbit.Data.LockN65.Seg.StageMats
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1975 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1975_shards_cover :
    ∀ s ∈ advLow.p1041.ii.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7]], s ∈ g := by
  decide +kernel

theorem lockM1975_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7]], g.all (checkShardAt advLow.p1041.ii
      (advLow.p1041.ii.la.slotTerms (((lockM1975a.toMants base.cfgLow.toMant 112).getD ([],
      [])).2)) (advLow.p1041.ii.lb.slotTerms (((lockM1975b.toMants base.cfgLow.toMant 112).getD
      ([], [])).2))) = true :=
  (List.forall_mem_cons.2 ⟨lockM1975_shardsG0, (List.forall_mem_cons.2 ⟨lockM1975_shardsG1, (fun _
    h => nomatch h)⟩)⟩)

theorem lockM1975_sp :
    checkPackedSp advLow.p1041.ii (advLow.p1041.ii.la.slotTerms (((lockM1975a.toMants
      base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1041.ii.lb.slotTerms
      (((lockM1975b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) = true :=
  checkPackedSp_of_groups advLow.p1041.ii (advLow.p1041.ii.la.slotTerms (((lockM1975a.toMants
        base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1041.ii.lb.slotTerms
        (((lockM1975b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) [[0, 1, 2, 3], [4, 5, 6,
        7]] lockM1975A7 lockM1975_shards_cover lockM1975_shards_groups









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM1975_advAt :
    advLow.b5[41]? = some ([4, 6, 3, 1, 1], (.packed 112 advLow.p1041.rr advLow.p1041.ii
      advLow.p1041.ri advLow.p1041.ir))
    := rfl

/-- The packed product 1975 (cfgLow, key [4, 6, 3, 1, 1]). -/
theorem lockM1975 :
    CertModel.polyProduct base.weight base.cfgLow ([4, 6] ++ [3, 1, 1]) ((modelMatrixEntry lockTL 3
      1).poly) ((modelMatrixEntry (modelMatNeg 2 2 lockDGi1) 1 1).poly) = some (((⟨[] ++ lockM1975T
      ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 + ((([lockM1975II_remN0, lockM1975II_remN1,
      lockM1975II_remN2, lockM1975II_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 147 * 2 ^ (2 *
      112) : ℕ) : ℚ)) + 0 + 0) : LockBackend)).1.toErrTerms, ((⟨[] ++ lockM1975T ++ [] ++ []⟩ :
      CertPoly LockBackend), (ofRatUp (0 + ((([lockM1975II_remN0, lockM1975II_remN1,
      lockM1975II_remN2, lockM1975II_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 147 * 2 ^ (2 *
      112) : ℕ) : ℚ)) + 0 + 0) : LockBackend)).2) := by
  rw [← lockM1975II_rb, lockM1975b_eq, lockM1975a_eq]
  exact polyProduct_eq_of_mulPacked base.weight base.cfgLow ([4, 6] ++ [3, 1, 1]) lockM1975a
      lockM1975b
      112 advLow.p1041.rr advLow.p1041.ii advLow.p1041.ri advLow.p1041.ir
      ((⟨[] ++ lockM1975T ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 +
        advLow.p1041.ii.remainderBound base.weight (2 * 112) + 0 + 0) : LockBackend))
      lockM1975A8 lockM1975A9 ((congrArg (fun b => adviceLookup b ([4, 6] ++ [3, 1, 1]))
          lock_advLow_blocks).trans ((adviceLookup_skip_cseg advLow.b0 _ ([4, 6] ++ [3, 1, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b1 _ ([4, 6] ++ [3, 1, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b2 _ ([4, 6] ++ [3, 1, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b3 _ ([4, 6] ++ [3, 1, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b4 _ ([4, 6] ++ [3, 1, 1]) (by
          decide +kernel)).trans (adviceLookup_at_cseg advLow.b5 _ ([4, 6] ++ [3, 1, 1]) 41 [4, 6,
          3, 1, 1] (.packed 112 advLow.p1041.rr advLow.p1041.ii advLow.p1041.ri advLow.p1041.ir) (by
          decide +kernel) lockM1975_advAt (by decide +kernel))))))))
      (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 112 advLow.p1041.rr
        advLow.p1041.ii advLow.p1041.ri advLow.p1041.ir lockM1975a lockM1975b
        (ma := ((lockM1975a.toMants base.cfgLow.toMant 112).getD ([], [])))
        (mb := ((lockM1975b.toMants base.cfgLow.toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pII := (advLow.p1041.ii.targetTerms, advLow.p1041.ii.remainderBound base.weight (2 * 112)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (tRR := ([] : List (CertKey × CC LockBackend))) (tII := lockM1975T)
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM1975A10)
        (eq_some_getD_cseg ([], []) lockM1975A11)
        (packedRealProduct_eq_nil_left advLow.p1041.rr base.weight (2 * 112) (((lockM1975b.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM1975A0)
        (packedRealProduct_eq_of_sparse advLow.p1041.ii base.weight (2 * 112) (((lockM1975a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) (((lockM1975b.toMants base.cfgLow.toMant
          112).getD ([], [])).2) lockM1975A1 lockM1975A2 lockM1975A3 lockM1975A4 lockM1975_sp)
        (packedRealProduct_eq_nil_left advLow.p1041.ri base.weight (2 * 112) (((lockM1975b.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM1975A5)
        (packedRealProduct_eq_nil_right advLow.p1041.ir base.weight (2 * 112) (((lockM1975a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM1975A6)
        (dyadicTerms_nil_cseg _ _ _)
        lockM1975_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
