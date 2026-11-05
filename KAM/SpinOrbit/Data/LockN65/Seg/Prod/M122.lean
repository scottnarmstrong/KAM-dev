/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M122Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 122 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM122_shards_cover :
    ∀ s ∈ advFull.p122.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM122_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advFull.p122.rr
      lockM122_shardsEA lockM122_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM122_shardsG0, (List.forall_mem_cons.2 ⟨lockM122_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM122_shardsG2, (List.forall_mem_cons.2 ⟨lockM122_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM122_sp :
    checkPackedSp advFull.p122.rr (advFull.p122.rr.la.slotTerms (((lockM122a.toMants
      (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])).1)) (advFull.p122.rr.lb.slotTerms
      (((lockM122a.toMants (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p122.rr) lockM122_shardsEA_eq lockM122_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p122.rr lockM122_shardsEA lockM122_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM122A7 lockM122_shards_cover
        lockM122_shards_groups)









/-- The packed product 122 (cfgFull, key [3, 433]). -/
theorem lockM122 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 3 433) [3] (((base.wit.sqrtWit.find?
      fun e => e.1 == 433).getD ((0, ⟨⟨[]⟩, 0, 0⟩) : ℕ × SqrtWitness LockBackend)).2.poly)
      (((base.wit.sqrtWit.find? fun e => e.1 == 433).getD ((0, ⟨⟨[]⟩, 0, 0⟩) : ℕ × SqrtWitness
      LockBackend)).2.poly) = some (((⟨lockM122T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend),
      (ofRatUp (((([lockM122RR_remN0, lockM122RR_remN1, lockM122RR_remN2, lockM122RR_remN3,
      lockM122RR_remN4, lockM122RR_remN5, lockM122RR_remN6, lockM122RR_remN7].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 242 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) :
      LockBackend)).1.toErrTerms, ((⟨lockM122T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
      (((([lockM122RR_remN0, lockM122RR_remN1, lockM122RR_remN2, lockM122RR_remN3,
      lockM122RR_remN4, lockM122RR_remN5, lockM122RR_remN6, lockM122RR_remN7].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 242 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).2) := by
  rw [← lockM122RR_rb, lockM122a_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 3 433) [3] lockM122a
      lockM122a
      112 advFull.p122.rr advFull.p122.ii advFull.p122.ri advFull.p122.ir
      ((⟨lockM122T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advFull.p122.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM122A8 lockM122A9 rfl
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 3 433).toMant base.weight 112
        advFull.p122.rr advFull.p122.ii advFull.p122.ri advFull.p122.ir lockM122a lockM122a
        (ma := ((lockM122a.toMants (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])))
        (mb := ((lockM122a.toMants (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])))
        (pRR := (advFull.p122.rr.targetTerms, advFull.p122.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM122T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM122A10)
        (eq_some_getD_cseg ([], []) lockM122A11)
        (packedRealProduct_eq_of_sparse advFull.p122.rr base.weight (2 * 112) (((lockM122a.toMants
          (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])).1) (((lockM122a.toMants
          (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])).1) lockM122A0 lockM122A1
          lockM122A2 lockM122A3 lockM122_sp)
        (packedRealProduct_eq_nil_left advFull.p122.ii base.weight (2 * 112) (((lockM122a.toMants
          (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])).2) lockM122A4)
        (packedRealProduct_eq_nil_right advFull.p122.ri base.weight (2 * 112) (((lockM122a.toMants
          (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])).1) lockM122A5)
        (packedRealProduct_eq_nil_left advFull.p122.ir base.weight (2 * 112) (((lockM122a.toMants
          (base.cfgFull.forWitness 3 433).toMant 112).getD ([], [])).1) lockM122A6)
        lockM122_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
