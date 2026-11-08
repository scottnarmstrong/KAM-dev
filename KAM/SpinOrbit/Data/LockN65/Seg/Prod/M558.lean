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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M558Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 558 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM558_shards_cover :
    ∀ s ∈ advFull.p558.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM558_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advFull.p558.rr
      lockM558_shardsEA lockM558_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM558_shardsG0, (List.forall_mem_cons.2 ⟨lockM558_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM558_shardsG2, (List.forall_mem_cons.2 ⟨lockM558_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM558_sp :
    checkPackedSp advFull.p558.rr (advFull.p558.rr.la.slotTerms (((lockM558a.toMants
      (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])).1)) (advFull.p558.rr.lb.slotTerms
      (((lockM558a.toMants (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])).1)) = true
      :=
  (congrArg₂ (checkPackedSp advFull.p558.rr) lockM558_shardsEA_eq lockM558_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p558.rr lockM558_shardsEA lockM558_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM558A7 lockM558_shards_cover
        lockM558_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM558_advAt :
    advFull.b2[158]? = some ([3, 1983], (.packed 112 advFull.p558.rr advFull.p558.ii
      advFull.p558.ri advFull.p558.ir))
    := rfl

/-- The packed product 558 (cfgFull, key [3, 1983]). -/
theorem lockM558 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 3 1983) [3]
      (((base.wit.sqrtWit.find? fun e => e.1 == 1983).getD ((0, ⟨⟨[]⟩, 0, 0⟩) : ℕ × SqrtWitness
      LockBackend)).2.poly) (((base.wit.sqrtWit.find? fun e => e.1 == 1983).getD ((0, ⟨⟨[]⟩, 0, 0⟩)
      : ℕ × SqrtWitness LockBackend)).2.poly) = some (((⟨lockM558T ++ [] ++ [] ++ []⟩ : CertPoly
      LockBackend), (ofRatUp (((([lockM558RR_remN0, lockM558RR_remN1, lockM558RR_remN2,
      lockM558RR_remN3, lockM558RR_remN4, lockM558RR_remN5, lockM558RR_remN6, lockM558RR_remN7].sum
      : ℕ) : ℚ) / ((base.weight.w.den ^ 242 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) :
      LockBackend)).1.toErrTerms, ((⟨lockM558T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
      (((([lockM558RR_remN0, lockM558RR_remN1, lockM558RR_remN2, lockM558RR_remN3,
      lockM558RR_remN4, lockM558RR_remN5, lockM558RR_remN6, lockM558RR_remN7].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 242 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).2) := by
  rw [← lockM558RR_rb, lockM558a_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 3 1983) [3] lockM558a
      lockM558a
      112 advFull.p558.rr advFull.p558.ii advFull.p558.ri advFull.p558.ir
      ((⟨lockM558T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advFull.p558.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM558A8 lockM558A9 ((adviceLookup_forWitness_cseg base.cfgFull 3 1983 []).trans
          ((congrArg (fun b => adviceLookup b [3, 1983]) lock_advFull_blocks).trans
          ((adviceLookup_skip_cseg advFull.b0 _ [3, 1983] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advFull.b1 _ [3, 1983] (by decide +kernel)).trans
          (adviceLookup_at_cseg
          advFull.b2 _ [3, 1983] 158 [3, 1983] (.packed 112 advFull.p558.rr advFull.p558.ii
          advFull.p558.ri advFull.p558.ir) (by decide +kernel) lockM558_advAt
          (by decide +kernel))))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 3 1983).toMant base.weight 112
        advFull.p558.rr advFull.p558.ii advFull.p558.ri advFull.p558.ir lockM558a lockM558a
        (ma := ((lockM558a.toMants (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])))
        (mb := ((lockM558a.toMants (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])))
        (pRR := (advFull.p558.rr.targetTerms, advFull.p558.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM558T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM558A10)
        (eq_some_getD_cseg ([], []) lockM558A11)
        (packedRealProduct_eq_of_sparse advFull.p558.rr base.weight (2 * 112) (((lockM558a.toMants
          (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])).1) (((lockM558a.toMants
          (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])).1) lockM558A0 lockM558A1
          lockM558A2 lockM558A3 lockM558_sp)
        (packedRealProduct_eq_nil_left advFull.p558.ii base.weight (2 * 112) (((lockM558a.toMants
          (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])).2) lockM558A4)
        (packedRealProduct_eq_nil_right advFull.p558.ri base.weight (2 * 112) (((lockM558a.toMants
          (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])).1) lockM558A5)
        (packedRealProduct_eq_nil_left advFull.p558.ir base.weight (2 * 112) (((lockM558a.toMants
          (base.cfgFull.forWitness 3 1983).toMant 112).getD ([], [])).1) lockM558A6)
        lockM558_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
