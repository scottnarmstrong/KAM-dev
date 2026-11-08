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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M348Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 348 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM348_shards_cover :
    ∀ s ∈ advFull.p348.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM348_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advFull.p348.ir
      lockM348_shardsEA lockM348_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM348_shardsG0, (List.forall_mem_cons.2 ⟨lockM348_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM348_shardsG2, (List.forall_mem_cons.2 ⟨lockM348_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM348_sp :
    checkPackedSp advFull.p348.ir (advFull.p348.ir.la.slotTerms (((lockM348a.toMants
      (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])).2)) (advFull.p348.ir.lb.slotTerms
      (((lockM348b.toMants (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p348.ir) lockM348_shardsEA_eq lockM348_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p348.ir lockM348_shardsEA lockM348_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM348A7 lockM348_shards_cover
        lockM348_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM348_advAt :
    advFull.b1[148]? = some ([1, 1, 1], (.packed 112 advFull.p348.rr advFull.p348.ii
      advFull.p348.ri advFull.p348.ir))
    := rfl

/-- The packed product 348 (cfgFull, key [1, 1, 1]). -/
theorem lockM348 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 1 1) [1, 1] ((itemsPoly
      ((CertModel.toDeg base.weight base.piEnc 0 (lockFullCkpt.slotPair base.weight
      1110).1).poly.terms.filterMap (derivItem 1)))) ((base.wit.expWit[1]?.getD (⟨⟨[]⟩, 0, 0⟩ :
      ExpWitness LockBackend)).poly.negP) = some (((⟨[] ++ [] ++ [] ++ lockM348T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM348IR_remN0, lockM348IR_remN1, lockM348IR_remN2,
      lockM348IR_remN3, lockM348IR_remN4, lockM348IR_remN5, lockM348IR_remN6, lockM348IR_remN7,
      lockM348IR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) :
      LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ lockM348T⟩ : CertPoly LockBackend), (ofRatUp
      (0 + 0 + 0 + ((([lockM348IR_remN0, lockM348IR_remN1, lockM348IR_remN2, lockM348IR_remN3,
      lockM348IR_remN4, lockM348IR_remN5, lockM348IR_remN6, lockM348IR_remN7, lockM348IR_remN8].sum
      : ℕ) : ℚ) / ((base.weight.w.den ^ 246 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM348IR_rb, lockM348a_eq, lockM348b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 1 1) [1, 1] lockM348a
      lockM348b
      112 advFull.p348.rr advFull.p348.ii advFull.p348.ri advFull.p348.ir
      ((⟨[] ++ [] ++ [] ++ lockM348T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advFull.p348.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM348A8 lockM348A9 ((adviceLookup_forWitness_cseg base.cfgFull 1 1 [1]).trans
          ((congrArg (fun b => adviceLookup b [1, 1, 1]) lock_advFull_blocks).trans
          ((adviceLookup_skip_cseg advFull.b0 _ [1, 1, 1] (by decide +kernel)).trans
          (adviceLookup_at_cseg advFull.b1 _ [1, 1, 1] 148 [1, 1, 1] (.packed 112 advFull.p348.rr
          advFull.p348.ii advFull.p348.ri advFull.p348.ir) (by decide +kernel) lockM348_advAt (by
          decide +kernel)))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 1 1).toMant base.weight 112
        advFull.p348.rr advFull.p348.ii advFull.p348.ri advFull.p348.ir lockM348a lockM348b
        (ma := ((lockM348a.toMants (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])))
        (mb := ((lockM348b.toMants (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advFull.p348.ir.targetTerms, advFull.p348.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM348T)
        (eq_some_getD_cseg ([], []) lockM348A10)
        (eq_some_getD_cseg ([], []) lockM348A11)
        (packedRealProduct_eq_nil_left advFull.p348.rr base.weight (2 * 112) (((lockM348b.toMants
          (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])).1) lockM348A0)
        (packedRealProduct_eq_nil_right advFull.p348.ii base.weight (2 * 112) (((lockM348a.toMants
          (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])).2) lockM348A1)
        (packedRealProduct_eq_nil_left advFull.p348.ri base.weight (2 * 112) (((lockM348b.toMants
          (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])).2) lockM348A2)
        (packedRealProduct_eq_of_sparse advFull.p348.ir base.weight (2 * 112) (((lockM348a.toMants
          (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])).2) (((lockM348b.toMants
          (base.cfgFull.forWitness 1 1).toMant 112).getD ([], [])).1) lockM348A3 lockM348A4
          lockM348A5 lockM348A6 lockM348_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM348_dec)

end KAM.SpinOrbit.Data.LockN65
