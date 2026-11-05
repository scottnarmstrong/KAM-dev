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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M123Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 123 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM123_shards_cover :
    ∀ s ∈ advFull.p123.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]],
      s ∈ g := by
  decide +kernel

theorem lockM123_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]], g.all (checkShardAt
      advFull.p123.rr lockM123_shardsEA lockM123_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM123_shardsG0, (List.forall_mem_cons.2 ⟨lockM123_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM123_shardsG2, (List.forall_mem_cons.2 ⟨lockM123_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM123_sp :
    checkPackedSp advFull.p123.rr (advFull.p123.rr.la.slotTerms (((lockM123a.toMants
      (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])).1)) (advFull.p123.rr.lb.slotTerms
      (((lockM123b.toMants (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p123.rr) lockM123_shardsEA_eq lockM123_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p123.rr lockM123_shardsEA lockM123_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]] lockM123A7 lockM123_shards_cover
        lockM123_shards_groups)









/-- The packed product 123 (cfgFull, key [2, 3]). -/
theorem lockM123 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 2 3) [2] ((base.wit.invWit[3]?.getD
      (⟨[]⟩ : CertPoly LockBackend))) ((lockFullCkpt.slotPair base.weight 433).1.poly) = some
      (((⟨lockM123T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (((([lockM123RR_remN0,
      lockM123RR_remN1, lockM123RR_remN2, lockM123RR_remN3, lockM123RR_remN4, lockM123RR_remN5,
      lockM123RR_remN6, lockM123RR_remN7, lockM123RR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^
      254 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).1.toErrTerms, ((⟨lockM123T ++ []
      ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (((([lockM123RR_remN0, lockM123RR_remN1,
      lockM123RR_remN2, lockM123RR_remN3, lockM123RR_remN4, lockM123RR_remN5, lockM123RR_remN6,
      lockM123RR_remN7, lockM123RR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 254 * 2 ^ (2 * 112)
      : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).2) := by
  rw [← lockM123RR_rb, lockM123a_eq, lockM123b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 2 3) [2] lockM123a
      lockM123b 112
      advFull.p123.rr advFull.p123.ii advFull.p123.ri advFull.p123.ir
      ((⟨lockM123T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advFull.p123.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM123A8 lockM123A9 rfl
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 2 3).toMant base.weight 112
        advFull.p123.rr advFull.p123.ii advFull.p123.ri advFull.p123.ir lockM123a lockM123b
        (ma := ((lockM123a.toMants (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])))
        (mb := ((lockM123b.toMants (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])))
        (pRR := (advFull.p123.rr.targetTerms, advFull.p123.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM123T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM123A10)
        (eq_some_getD_cseg ([], []) lockM123A11)
        (packedRealProduct_eq_of_sparse advFull.p123.rr base.weight (2 * 112) (((lockM123a.toMants
          (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])).1) (((lockM123b.toMants
          (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])).1) lockM123A0 lockM123A1
          lockM123A2 lockM123A3 lockM123_sp)
        (packedRealProduct_eq_nil_left advFull.p123.ii base.weight (2 * 112) (((lockM123b.toMants
          (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])).2) lockM123A4)
        (packedRealProduct_eq_nil_right advFull.p123.ri base.weight (2 * 112) (((lockM123a.toMants
          (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])).1) lockM123A5)
        (packedRealProduct_eq_nil_left advFull.p123.ir base.weight (2 * 112) (((lockM123b.toMants
          (base.cfgFull.forWitness 2 3).toMant 112).getD ([], [])).1) lockM123A6)
        lockM123_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
