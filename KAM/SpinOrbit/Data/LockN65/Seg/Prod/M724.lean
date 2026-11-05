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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M724Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 724 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM724_shards_cover :
    ∀ s ∈ advFull.p724.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM724_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advFull.p724.ir
      lockM724_shardsEA lockM724_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM724_shardsG0, (List.forall_mem_cons.2 ⟨lockM724_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM724_shardsG2, (List.forall_mem_cons.2 ⟨lockM724_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM724_sp :
    checkPackedSp advFull.p724.ir (advFull.p724.ir.la.slotTerms (((lockM724a.toMants
      (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).2)) (advFull.p724.ir.lb.slotTerms
      (((lockM724b.toMants (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p724.ir) lockM724_shardsEA_eq lockM724_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p724.ir lockM724_shardsEA lockM724_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM724A7 lockM724_shards_cover
        lockM724_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM724_advAt :
    advFull.b3[124]? = some ([1, 3, 1], (.packed 112 advFull.p724.rr advFull.p724.ii
      advFull.p724.ri advFull.p724.ir))
    := rfl

/-- The packed product 724 (cfgFull, key [1, 3, 1]). -/
theorem lockM724 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 1 3) [1, 1] ((itemsPoly
      ((CertModel.toDeg base.weight base.piEnc 0 (lockFullCkpt.slotPair base.weight
      2306).1).poly.terms.filterMap (derivItem 1)))) ((base.wit.expWit[3]?.getD (⟨⟨[]⟩, 0, 0⟩ :
      ExpWitness LockBackend)).poly.negP) = some (((⟨[] ++ [] ++ [] ++ lockM724T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM724IR_remN0, lockM724IR_remN1, lockM724IR_remN2,
      lockM724IR_remN3, lockM724IR_remN4, lockM724IR_remN5, lockM724IR_remN6, lockM724IR_remN7,
      lockM724IR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) :
      LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ lockM724T⟩ : CertPoly LockBackend), (ofRatUp
      (0 + 0 + 0 + ((([lockM724IR_remN0, lockM724IR_remN1, lockM724IR_remN2, lockM724IR_remN3,
      lockM724IR_remN4, lockM724IR_remN5, lockM724IR_remN6, lockM724IR_remN7, lockM724IR_remN8].sum
      : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM724IR_rb, lockM724a_eq, lockM724b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 1 3) [1, 1] lockM724a
      lockM724b
      112 advFull.p724.rr advFull.p724.ii advFull.p724.ri advFull.p724.ir
      ((⟨[] ++ [] ++ [] ++ lockM724T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advFull.p724.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM724A8 lockM724A9 ((adviceLookup_forWitness_cseg base.cfgFull 1 3 [1]).trans
          ((congrArg (fun b => adviceLookup b [1, 3, 1]) lock_advFull_blocks).trans
          ((adviceLookup_skip_cseg advFull.b0 _ [1, 3, 1] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advFull.b1 _ [1, 3, 1] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advFull.b2 _ [1, 3, 1] (by decide +kernel)).trans
          (adviceLookup_at_cseg advFull.b3 _ [1, 3, 1] 124 [1, 3, 1] (.packed 112 advFull.p724.rr
          advFull.p724.ii advFull.p724.ri advFull.p724.ir) (by decide +kernel) lockM724_advAt (by
          decide +kernel)))))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 1 3).toMant base.weight 112
        advFull.p724.rr advFull.p724.ii advFull.p724.ri advFull.p724.ir lockM724a lockM724b
        (ma := ((lockM724a.toMants (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])))
        (mb := ((lockM724b.toMants (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advFull.p724.ir.targetTerms, advFull.p724.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM724T)
        (eq_some_getD_cseg ([], []) lockM724A10)
        (eq_some_getD_cseg ([], []) lockM724A11)
        (packedRealProduct_eq_nil_left advFull.p724.rr base.weight (2 * 112) (((lockM724b.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).1) lockM724A0)
        (packedRealProduct_eq_nil_right advFull.p724.ii base.weight (2 * 112) (((lockM724a.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).2) lockM724A1)
        (packedRealProduct_eq_nil_left advFull.p724.ri base.weight (2 * 112) (((lockM724b.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).2) lockM724A2)
        (packedRealProduct_eq_of_sparse advFull.p724.ir base.weight (2 * 112) (((lockM724a.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).2) (((lockM724b.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).1) lockM724A3 lockM724A4
          lockM724A5 lockM724A6 lockM724_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM724_dec)

end KAM.SpinOrbit.Data.LockN65
