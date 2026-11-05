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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M579Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 579 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM579_shards_cover :
    ∀ s ∈ advFull.p579.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM579_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advFull.p579.ir
      lockM579_shardsEA lockM579_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM579_shardsG0, (List.forall_mem_cons.2 ⟨lockM579_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM579_shardsG2, (List.forall_mem_cons.2 ⟨lockM579_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM579_sp :
    checkPackedSp advFull.p579.ir (advFull.p579.ir.la.slotTerms (((lockM579a.toMants
      (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])).2)) (advFull.p579.ir.lb.slotTerms
      (((lockM579b.toMants (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p579.ir) lockM579_shardsEA_eq lockM579_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p579.ir lockM579_shardsEA lockM579_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM579A7 lockM579_shards_cover
        lockM579_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM579_advAt :
    advFull.b2[179]? = some ([1, 2, 1], (.packed 112 advFull.p579.rr advFull.p579.ii
      advFull.p579.ri advFull.p579.ir))
    := rfl

/-- The packed product 579 (cfgFull, key [1, 2, 1]). -/
theorem lockM579 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 1 2) [1, 1] ((itemsPoly
      ((CertModel.toDeg base.weight base.piEnc 0 (lockFullCkpt.slotPair base.weight
      2066).1).poly.terms.filterMap (derivItem 1)))) ((base.wit.expWit[2]?.getD (⟨⟨[]⟩, 0, 0⟩ :
      ExpWitness LockBackend)).poly.negP) = some (((⟨[] ++ [] ++ [] ++ lockM579T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM579IR_remN0, lockM579IR_remN1, lockM579IR_remN2,
      lockM579IR_remN3, lockM579IR_remN4, lockM579IR_remN5, lockM579IR_remN6, lockM579IR_remN7,
      lockM579IR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) :
      LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ lockM579T⟩ : CertPoly LockBackend), (ofRatUp
      (0 + 0 + 0 + ((([lockM579IR_remN0, lockM579IR_remN1, lockM579IR_remN2, lockM579IR_remN3,
      lockM579IR_remN4, lockM579IR_remN5, lockM579IR_remN6, lockM579IR_remN7, lockM579IR_remN8].sum
      : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM579IR_rb, lockM579a_eq, lockM579b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 1 2) [1, 1] lockM579a
      lockM579b
      112 advFull.p579.rr advFull.p579.ii advFull.p579.ri advFull.p579.ir
      ((⟨[] ++ [] ++ [] ++ lockM579T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advFull.p579.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM579A8 lockM579A9 ((adviceLookup_forWitness_cseg base.cfgFull 1 2 [1]).trans
          ((congrArg (fun b => adviceLookup b [1, 2, 1]) lock_advFull_blocks).trans
          ((adviceLookup_skip_cseg advFull.b0 _ [1, 2, 1] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advFull.b1 _ [1, 2, 1] (by decide +kernel)).trans
          (adviceLookup_at_cseg advFull.b2 _ [1, 2, 1] 179 [1, 2, 1] (.packed 112 advFull.p579.rr
          advFull.p579.ii advFull.p579.ri advFull.p579.ir) (by decide +kernel) lockM579_advAt (by
          decide +kernel))))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 1 2).toMant base.weight 112
        advFull.p579.rr advFull.p579.ii advFull.p579.ri advFull.p579.ir lockM579a lockM579b
        (ma := ((lockM579a.toMants (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])))
        (mb := ((lockM579b.toMants (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advFull.p579.ir.targetTerms, advFull.p579.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM579T)
        (eq_some_getD_cseg ([], []) lockM579A10)
        (eq_some_getD_cseg ([], []) lockM579A11)
        (packedRealProduct_eq_nil_left advFull.p579.rr base.weight (2 * 112) (((lockM579b.toMants
          (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])).1) lockM579A0)
        (packedRealProduct_eq_nil_right advFull.p579.ii base.weight (2 * 112) (((lockM579a.toMants
          (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])).2) lockM579A1)
        (packedRealProduct_eq_nil_left advFull.p579.ri base.weight (2 * 112) (((lockM579b.toMants
          (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])).2) lockM579A2)
        (packedRealProduct_eq_of_sparse advFull.p579.ir base.weight (2 * 112) (((lockM579a.toMants
          (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])).2) (((lockM579b.toMants
          (base.cfgFull.forWitness 1 2).toMant 112).getD ([], [])).1) lockM579A3 lockM579A4
          lockM579A5 lockM579A6 lockM579_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM579_dec)

end KAM.SpinOrbit.Data.LockN65
