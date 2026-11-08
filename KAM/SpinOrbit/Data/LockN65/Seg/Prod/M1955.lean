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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1955Sh
public import KAM.SpinOrbit.Data.LockN65.Seg.StageMats
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1955 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1955_shards_cover :
    ∀ s ∈ advLow.p1021.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7]], s ∈ g := by
  decide +kernel

theorem lockM1955_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7]], g.all (checkShardAt advLow.p1021.ir
      (advLow.p1021.ir.la.slotTerms (((lockM1955a.toMants base.cfgLow.toMant 112).getD ([],
      [])).2)) (advLow.p1021.ir.lb.slotTerms (((lockM1955b.toMants base.cfgLow.toMant 112).getD
      ([], [])).1))) = true :=
  (List.forall_mem_cons.2 ⟨lockM1955_shardsG0, (List.forall_mem_cons.2 ⟨lockM1955_shardsG1, (fun _
    h => nomatch h)⟩)⟩)

theorem lockM1955_sp :
    checkPackedSp advLow.p1021.ir (advLow.p1021.ir.la.slotTerms (((lockM1955a.toMants
      base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1021.ir.lb.slotTerms
      (((lockM1955b.toMants base.cfgLow.toMant 112).getD ([], [])).1)) = true :=
  checkPackedSp_of_groups advLow.p1021.ir (advLow.p1021.ir.la.slotTerms (((lockM1955a.toMants
        base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1021.ir.lb.slotTerms
        (((lockM1955b.toMants base.cfgLow.toMant 112).getD ([], [])).1)) [[0, 1, 2, 3], [4, 5, 6,
        7]] lockM1955A7 lockM1955_shards_cover lockM1955_shards_groups









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM1955_advAt :
    advLow.b5[21]? = some ([4, 5, 0, 1, 1], (.packed 112 advLow.p1021.rr advLow.p1021.ii
      advLow.p1021.ri advLow.p1021.ir))
    := rfl

/-- The packed product 1955 (cfgLow, key [4, 5, 0, 1, 1]). -/
theorem lockM1955 :
    CertModel.polyProduct base.weight base.cfgLow ([4, 5] ++ [0, 1, 1]) ((modelMatrixEntry lockTDL
      0 1).poly) ((modelMatrixEntry lockTGi 1 1).poly) = some (((⟨[] ++ [] ++ [] ++ lockM1955T⟩ :
      CertPoly LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM1955IR_remN0, lockM1955IR_remN1,
      lockM1955IR_remN2, lockM1955IR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 163 * 2 ^ (2 *
      112) : ℕ) : ℚ))) : LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ lockM1955T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM1955IR_remN0, lockM1955IR_remN1,
      lockM1955IR_remN2, lockM1955IR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 163 * 2 ^ (2 *
      112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM1955IR_rb, lockM1955a_eq, lockM1955b_eq]
  exact polyProduct_eq_of_mulPacked base.weight base.cfgLow ([4, 5] ++ [0, 1, 1]) lockM1955a
      lockM1955b
      112 advLow.p1021.rr advLow.p1021.ii advLow.p1021.ri advLow.p1021.ir
      ((⟨[] ++ [] ++ [] ++ lockM1955T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advLow.p1021.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM1955A8 lockM1955A9 ((congrArg (fun b => adviceLookup b ([4, 5] ++ [0, 1, 1]))
          lock_advLow_blocks).trans ((adviceLookup_skip_cseg advLow.b0 _ ([4, 5] ++ [0, 1, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b1 _ ([4, 5] ++ [0, 1, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b2 _ ([4, 5] ++ [0, 1, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b3 _ ([4, 5] ++ [0, 1, 1]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b4 _ ([4, 5] ++ [0, 1, 1]) (by
          decide +kernel)).trans (adviceLookup_at_cseg advLow.b5 _ ([4, 5] ++ [0, 1, 1]) 21 [4, 5,
          0, 1, 1] (.packed 112 advLow.p1021.rr advLow.p1021.ii advLow.p1021.ri advLow.p1021.ir) (by
          decide +kernel) lockM1955_advAt (by decide +kernel))))))))
      (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 112 advLow.p1021.rr
        advLow.p1021.ii advLow.p1021.ri advLow.p1021.ir lockM1955a lockM1955b
        (ma := ((lockM1955a.toMants base.cfgLow.toMant 112).getD ([], [])))
        (mb := ((lockM1955b.toMants base.cfgLow.toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advLow.p1021.ir.targetTerms, advLow.p1021.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM1955T)
        (eq_some_getD_cseg ([], []) lockM1955A10)
        (eq_some_getD_cseg ([], []) lockM1955A11)
        (packedRealProduct_eq_nil_left advLow.p1021.rr base.weight (2 * 112) (((lockM1955b.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM1955A0)
        (packedRealProduct_eq_nil_right advLow.p1021.ii base.weight (2 * 112) (((lockM1955a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM1955A1)
        (packedRealProduct_eq_nil_left advLow.p1021.ri base.weight (2 * 112) (((lockM1955b.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM1955A2)
        (packedRealProduct_eq_of_sparse advLow.p1021.ir base.weight (2 * 112) (((lockM1955a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) (((lockM1955b.toMants base.cfgLow.toMant
          112).getD ([], [])).1) lockM1955A3 lockM1955A4 lockM1955A5 lockM1955A6 lockM1955_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM1955_dec)

end KAM.SpinOrbit.Data.LockN65
