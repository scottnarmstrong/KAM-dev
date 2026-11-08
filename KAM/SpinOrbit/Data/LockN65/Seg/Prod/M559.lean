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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M559Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 559 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM559_shards_cover :
    ∀ s ∈ advFull.p559.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]],
      s ∈ g := by
  decide +kernel

theorem lockM559_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]], g.all (checkShardAt
      advFull.p559.rr lockM559_shardsEA lockM559_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM559_shardsG0, (List.forall_mem_cons.2 ⟨lockM559_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM559_shardsG2, (List.forall_mem_cons.2 ⟨lockM559_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM559_sp :
    checkPackedSp advFull.p559.rr (advFull.p559.rr.la.slotTerms (((lockM559a.toMants
      (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])).1)) (advFull.p559.rr.lb.slotTerms
      (((lockM559b.toMants (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p559.rr) lockM559_shardsEA_eq lockM559_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p559.rr lockM559_shardsEA lockM559_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]] lockM559A7 lockM559_shards_cover
        lockM559_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM559_advAt :
    advFull.b2[159]? = some ([2, 7], (.packed 112 advFull.p559.rr advFull.p559.ii advFull.p559.ri
      advFull.p559.ir))
    := rfl

/-- The packed product 559 (cfgFull, key [2, 7]). -/
theorem lockM559 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 2 7) [2] ((base.wit.invWit[7]?.getD
      (⟨[]⟩ : CertPoly LockBackend))) ((lockFullCkpt.slotPair base.weight 1983).1.poly) = some
      (((⟨lockM559T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (((([lockM559RR_remN0,
      lockM559RR_remN1, lockM559RR_remN2, lockM559RR_remN3, lockM559RR_remN4, lockM559RR_remN5,
      lockM559RR_remN6, lockM559RR_remN7, lockM559RR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^
      254 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).1.toErrTerms, ((⟨lockM559T ++ []
      ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (((([lockM559RR_remN0, lockM559RR_remN1,
      lockM559RR_remN2, lockM559RR_remN3, lockM559RR_remN4, lockM559RR_remN5, lockM559RR_remN6,
      lockM559RR_remN7, lockM559RR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 254 * 2 ^ (2 * 112)
      : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).2) := by
  rw [← lockM559RR_rb, lockM559a_eq, lockM559b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 2 7) [2] lockM559a
      lockM559b 112
      advFull.p559.rr advFull.p559.ii advFull.p559.ri advFull.p559.ir
      ((⟨lockM559T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advFull.p559.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM559A8 lockM559A9 ((adviceLookup_forWitness_cseg base.cfgFull 2 7 []).trans
          ((congrArg (fun b => adviceLookup b [2, 7]) lock_advFull_blocks).trans
          ((adviceLookup_skip_cseg advFull.b0 _ [2, 7] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advFull.b1 _ [2, 7] (by decide +kernel)).trans
          (adviceLookup_at_cseg
          advFull.b2 _ [2, 7] 159 [2, 7] (.packed 112 advFull.p559.rr advFull.p559.ii
          advFull.p559.ri
          advFull.p559.ir) (by decide +kernel) lockM559_advAt (by decide +kernel))))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 2 7).toMant base.weight 112
        advFull.p559.rr advFull.p559.ii advFull.p559.ri advFull.p559.ir lockM559a lockM559b
        (ma := ((lockM559a.toMants (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])))
        (mb := ((lockM559b.toMants (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])))
        (pRR := (advFull.p559.rr.targetTerms, advFull.p559.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM559T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM559A10)
        (eq_some_getD_cseg ([], []) lockM559A11)
        (packedRealProduct_eq_of_sparse advFull.p559.rr base.weight (2 * 112) (((lockM559a.toMants
          (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])).1) (((lockM559b.toMants
          (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])).1) lockM559A0 lockM559A1
          lockM559A2 lockM559A3 lockM559_sp)
        (packedRealProduct_eq_nil_left advFull.p559.ii base.weight (2 * 112) (((lockM559b.toMants
          (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])).2) lockM559A4)
        (packedRealProduct_eq_nil_right advFull.p559.ri base.weight (2 * 112) (((lockM559a.toMants
          (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])).1) lockM559A5)
        (packedRealProduct_eq_nil_left advFull.p559.ir base.weight (2 * 112) (((lockM559b.toMants
          (base.cfgFull.forWitness 2 7).toMant 112).getD ([], [])).1) lockM559A6)
        lockM559_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
