/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.AdvLookup
public import KAM.SpinOrbit.Data.LockN65.AdvLookupSub
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
public import KAM.SpinOrbit.Data.LockN65.Seg.PlanFull
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M202Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 202 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM202_shards_cover :
    ∀ s ∈ advFull.p202.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM202_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advFull.p202.ir
      lockM202_shardsEA lockM202_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM202_shardsG0, (List.forall_mem_cons.2 ⟨lockM202_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM202_shardsG2, (List.forall_mem_cons.2 ⟨lockM202_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM202_sp :
    checkPackedSp advFull.p202.ir (advFull.p202.ir.la.slotTerms (((lockM202a.toMants
      (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])).2)) (advFull.p202.ir.lb.slotTerms
      (((lockM202b.toMants (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p202.ir) lockM202_shardsEA_eq lockM202_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p202.ir lockM202_shardsEA lockM202_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM202A7 lockM202_shards_cover
        lockM202_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM202_advAt :
    advFull.b1[2]? = some ([1, 0, 0], (.packed 112 advFull.p202.rr advFull.p202.ii advFull.p202.ri
      advFull.p202.ir))
    := rfl

/-- The packed product 202 (cfgFull, key [1, 0, 0]). -/
theorem lockM202 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 1 0) [1, 0] ((itemsPoly
      ((CertModel.toDeg base.weight base.piEnc 0 (lockFullCkpt.slotPair base.weight
      870).1).poly.terms.filterMap (derivItem 0)))) ((base.wit.expWit[0]?.getD (⟨⟨[]⟩, 0, 0⟩ :
      ExpWitness LockBackend)).poly.negP) = some (((⟨[] ++ [] ++ [] ++ lockM202T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM202IR_remN0, lockM202IR_remN1, lockM202IR_remN2,
      lockM202IR_remN3, lockM202IR_remN4, lockM202IR_remN5, lockM202IR_remN6, lockM202IR_remN7,
      lockM202IR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) :
      LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ lockM202T⟩ : CertPoly LockBackend), (ofRatUp
      (0 + 0 + 0 + ((([lockM202IR_remN0, lockM202IR_remN1, lockM202IR_remN2, lockM202IR_remN3,
      lockM202IR_remN4, lockM202IR_remN5, lockM202IR_remN6, lockM202IR_remN7, lockM202IR_remN8].sum
      : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM202IR_rb, lockM202a_eq, lockM202b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 1 0) [1, 0] lockM202a
      lockM202b
      112 advFull.p202.rr advFull.p202.ii advFull.p202.ri advFull.p202.ir
      ((⟨[] ++ [] ++ [] ++ lockM202T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advFull.p202.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM202A8 lockM202A9 ((adviceLookup_forWitness_cseg base.cfgFull 1 0 [0]).trans
          ((congrArg (fun b => adviceLookup b [1, 0, 0]) lock_advFull_blocks).trans
          ((adviceLookup_skip_cseg advFull.b0 _ [1, 0, 0] (by decide +kernel)).trans
          (adviceLookup_at_cseg advFull.b1 _ [1, 0, 0] 2 [1, 0, 0] (.packed 112 advFull.p202.rr
          advFull.p202.ii advFull.p202.ri advFull.p202.ir) (by decide +kernel) lockM202_advAt (by
          decide +kernel)))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 1 0).toMant base.weight 112
        advFull.p202.rr advFull.p202.ii advFull.p202.ri advFull.p202.ir lockM202a lockM202b
        (ma := ((lockM202a.toMants (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])))
        (mb := ((lockM202b.toMants (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advFull.p202.ir.targetTerms, advFull.p202.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM202T)
        (eq_some_getD_cseg ([], []) lockM202A10)
        (eq_some_getD_cseg ([], []) lockM202A11)
        (packedRealProduct_eq_nil_left advFull.p202.rr base.weight (2 * 112) (((lockM202b.toMants
          (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])).1) lockM202A0)
        (packedRealProduct_eq_nil_right advFull.p202.ii base.weight (2 * 112) (((lockM202a.toMants
          (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])).2) lockM202A1)
        (packedRealProduct_eq_nil_left advFull.p202.ri base.weight (2 * 112) (((lockM202b.toMants
          (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])).2) lockM202A2)
        (packedRealProduct_eq_of_sparse advFull.p202.ir base.weight (2 * 112) (((lockM202a.toMants
          (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])).2) (((lockM202b.toMants
          (base.cfgFull.forWitness 1 0).toMant 112).getD ([], [])).1) lockM202A3 lockM202A4
          lockM202A5 lockM202A6 lockM202_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM202_dec)

end KAM.SpinOrbit.Data.LockN65
