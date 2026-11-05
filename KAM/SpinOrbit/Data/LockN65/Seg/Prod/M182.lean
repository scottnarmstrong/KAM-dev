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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M182Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 182 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM182_shards_cover :
    ∀ s ∈ advFull.p182.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM182_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advFull.p182.rr
      lockM182_shardsEA lockM182_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM182_shardsG0, (List.forall_mem_cons.2 ⟨lockM182_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM182_shardsG2, (List.forall_mem_cons.2 ⟨lockM182_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM182_sp :
    checkPackedSp advFull.p182.rr (advFull.p182.rr.la.slotTerms (((lockM182a.toMants
      (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])).1)) (advFull.p182.rr.lb.slotTerms
      (((lockM182a.toMants (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p182.rr) lockM182_shardsEA_eq lockM182_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p182.rr lockM182_shardsEA lockM182_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM182A7 lockM182_shards_cover
        lockM182_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM182_advAt :
    advFull.b0[182]? = some ([3, 787], (.packed 112 advFull.p182.rr advFull.p182.ii advFull.p182.ri
      advFull.p182.ir))
    := rfl

/-- The packed product 182 (cfgFull, key [3, 787]). -/
theorem lockM182 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 3 787) [3] (((base.wit.sqrtWit.find?
      fun e => e.1 == 787).getD ((0, ⟨⟨[]⟩, 0, 0⟩) : ℕ × SqrtWitness LockBackend)).2.poly)
      (((base.wit.sqrtWit.find? fun e => e.1 == 787).getD ((0, ⟨⟨[]⟩, 0, 0⟩) : ℕ × SqrtWitness
      LockBackend)).2.poly) = some (((⟨lockM182T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend),
      (ofRatUp (((([lockM182RR_remN0, lockM182RR_remN1, lockM182RR_remN2, lockM182RR_remN3,
      lockM182RR_remN4, lockM182RR_remN5, lockM182RR_remN6, lockM182RR_remN7].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 242 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) :
      LockBackend)).1.toErrTerms, ((⟨lockM182T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
      (((([lockM182RR_remN0, lockM182RR_remN1, lockM182RR_remN2, lockM182RR_remN3,
      lockM182RR_remN4, lockM182RR_remN5, lockM182RR_remN6, lockM182RR_remN7].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 242 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).2) := by
  rw [← lockM182RR_rb, lockM182a_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 3 787) [3] lockM182a
      lockM182a
      112 advFull.p182.rr advFull.p182.ii advFull.p182.ri advFull.p182.ir
      ((⟨lockM182T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advFull.p182.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM182A8 lockM182A9 ((adviceLookup_forWitness_cseg base.cfgFull 3 787 []).trans
          ((congrArg (fun b => adviceLookup b [3, 787]) lock_advFull_blocks).trans
          (adviceLookup_at_cseg advFull.b0 _ [3, 787] 182 [3, 787] (.packed 112 advFull.p182.rr
          advFull.p182.ii advFull.p182.ri advFull.p182.ir) (by decide +kernel) lockM182_advAt (by
          decide +kernel))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 3 787).toMant base.weight 112
        advFull.p182.rr advFull.p182.ii advFull.p182.ri advFull.p182.ir lockM182a lockM182a
        (ma := ((lockM182a.toMants (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])))
        (mb := ((lockM182a.toMants (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])))
        (pRR := (advFull.p182.rr.targetTerms, advFull.p182.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM182T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM182A10)
        (eq_some_getD_cseg ([], []) lockM182A11)
        (packedRealProduct_eq_of_sparse advFull.p182.rr base.weight (2 * 112) (((lockM182a.toMants
          (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])).1) (((lockM182a.toMants
          (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])).1) lockM182A0 lockM182A1
          lockM182A2 lockM182A3 lockM182_sp)
        (packedRealProduct_eq_nil_left advFull.p182.ii base.weight (2 * 112) (((lockM182a.toMants
          (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])).2) lockM182A4)
        (packedRealProduct_eq_nil_right advFull.p182.ri base.weight (2 * 112) (((lockM182a.toMants
          (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])).1) lockM182A5)
        (packedRealProduct_eq_nil_left advFull.p182.ir base.weight (2 * 112) (((lockM182a.toMants
          (base.cfgFull.forWitness 3 787).toMant 112).getD ([], [])).1) lockM182A6)
        lockM182_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
