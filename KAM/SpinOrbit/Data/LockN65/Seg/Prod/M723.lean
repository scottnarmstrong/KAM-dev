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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M723Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 723 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM723_shards_cover :
    ∀ s ∈ advFull.p723.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM723_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advFull.p723.ir
      lockM723_shardsEA lockM723_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM723_shardsG0, (List.forall_mem_cons.2 ⟨lockM723_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM723_shardsG2, (List.forall_mem_cons.2 ⟨lockM723_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM723_sp :
    checkPackedSp advFull.p723.ir (advFull.p723.ir.la.slotTerms (((lockM723a.toMants
      (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).2)) (advFull.p723.ir.lb.slotTerms
      (((lockM723b.toMants (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p723.ir) lockM723_shardsEA_eq lockM723_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p723.ir lockM723_shardsEA lockM723_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM723A7 lockM723_shards_cover
        lockM723_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM723_advAt :
    advFull.b3[123]? = some ([1, 3, 0], (.packed 112 advFull.p723.rr advFull.p723.ii
      advFull.p723.ri advFull.p723.ir))
    := rfl

/-- The packed product 723 (cfgFull, key [1, 3, 0]). -/
theorem lockM723 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 1 3) [1, 0] ((itemsPoly
      ((CertModel.toDeg base.weight base.piEnc 0 (lockFullCkpt.slotPair base.weight
      2306).1).poly.terms.filterMap (derivItem 0)))) ((base.wit.expWit[3]?.getD (⟨⟨[]⟩, 0, 0⟩ :
      ExpWitness LockBackend)).poly.negP) = some (((⟨[] ++ [] ++ [] ++ lockM723T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM723IR_remN0, lockM723IR_remN1, lockM723IR_remN2,
      lockM723IR_remN3, lockM723IR_remN4, lockM723IR_remN5, lockM723IR_remN6, lockM723IR_remN7,
      lockM723IR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) :
      LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ lockM723T⟩ : CertPoly LockBackend), (ofRatUp
      (0 + 0 + 0 + ((([lockM723IR_remN0, lockM723IR_remN1, lockM723IR_remN2, lockM723IR_remN3,
      lockM723IR_remN4, lockM723IR_remN5, lockM723IR_remN6, lockM723IR_remN7, lockM723IR_remN8].sum
      : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM723IR_rb, lockM723a_eq, lockM723b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 1 3) [1, 0] lockM723a
      lockM723b
      112 advFull.p723.rr advFull.p723.ii advFull.p723.ri advFull.p723.ir
      ((⟨[] ++ [] ++ [] ++ lockM723T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advFull.p723.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM723A8 lockM723A9 ((adviceLookup_forWitness_cseg base.cfgFull 1 3 [0]).trans
          ((congrArg (fun b => adviceLookup b [1, 3, 0]) lock_advFull_blocks).trans
          ((adviceLookup_skip_cseg advFull.b0 _ [1, 3, 0] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advFull.b1 _ [1, 3, 0] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advFull.b2 _ [1, 3, 0] (by decide +kernel)).trans
          (adviceLookup_at_cseg advFull.b3 _ [1, 3, 0] 123 [1, 3, 0] (.packed 112 advFull.p723.rr
          advFull.p723.ii advFull.p723.ri advFull.p723.ir) (by decide +kernel) lockM723_advAt (by
          decide +kernel)))))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 1 3).toMant base.weight 112
        advFull.p723.rr advFull.p723.ii advFull.p723.ri advFull.p723.ir lockM723a lockM723b
        (ma := ((lockM723a.toMants (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])))
        (mb := ((lockM723b.toMants (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advFull.p723.ir.targetTerms, advFull.p723.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM723T)
        (eq_some_getD_cseg ([], []) lockM723A10)
        (eq_some_getD_cseg ([], []) lockM723A11)
        (packedRealProduct_eq_nil_left advFull.p723.rr base.weight (2 * 112) (((lockM723b.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).1) lockM723A0)
        (packedRealProduct_eq_nil_right advFull.p723.ii base.weight (2 * 112) (((lockM723a.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).2) lockM723A1)
        (packedRealProduct_eq_nil_left advFull.p723.ri base.weight (2 * 112) (((lockM723b.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).2) lockM723A2)
        (packedRealProduct_eq_of_sparse advFull.p723.ir base.weight (2 * 112) (((lockM723a.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).2) (((lockM723b.toMants
          (base.cfgFull.forWitness 1 3).toMant 112).getD ([], [])).1) lockM723A3 lockM723A4
          lockM723A5 lockM723A6 lockM723_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM723_dec)

end KAM.SpinOrbit.Data.LockN65
