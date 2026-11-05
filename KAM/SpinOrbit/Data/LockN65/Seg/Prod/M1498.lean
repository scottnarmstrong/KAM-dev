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
public import KAM.SpinOrbit.Data.LockN65.Seg.PlanLow
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1498Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1498 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1498_shards_cover :
    ∀ s ∈ advLow.p581.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈
      g := by
  decide +kernel

theorem lockM1498_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advLow.p581.rr
      lockM1498_shardsEA lockM1498_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM1498_shardsG0, (List.forall_mem_cons.2 ⟨lockM1498_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM1498_shardsG2, (List.forall_mem_cons.2 ⟨lockM1498_shardsG3, (fun
    _ h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM1498_sp :
    checkPackedSp advLow.p581.rr (advLow.p581.rr.la.slotTerms (((lockM1498a.toMants
      (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])).1)) (advLow.p581.rr.lb.slotTerms
      (((lockM1498a.toMants (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])).1)) = true
      :=
  (congrArg₂ (checkPackedSp advLow.p581.rr) lockM1498_shardsEA_eq lockM1498_shardsEB_eq).trans
        (checkPackedSp_of_groups advLow.p581.rr lockM1498_shardsEA lockM1498_shardsEB [[0, 1, 2,
        3], [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM1498A7 lockM1498_shards_cover
        lockM1498_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM1498_advAt :
    advLow.b2[181]? = some ([3, 1983], (.packed 112 advLow.p581.rr advLow.p581.ii advLow.p581.ri
      advLow.p581.ir))
    := rfl

/-- The packed product 1498 (cfgLow, key [3, 1983]). -/
theorem lockM1498 :
    CertModel.polyProduct base.weight (base.cfgLow.forWitness 3 1983) [3] (((base.wit.sqrtWit.find?
      fun e => e.1 == 1983).getD ((0, ⟨⟨[]⟩, 0, 0⟩) : ℕ × SqrtWitness LockBackend)).2.poly)
      (((base.wit.sqrtWit.find? fun e => e.1 == 1983).getD ((0, ⟨⟨[]⟩, 0, 0⟩) : ℕ × SqrtWitness
      LockBackend)).2.poly) = some (((⟨lockM1498T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend),
      (ofRatUp (((([lockM1498RR_remN0, lockM1498RR_remN1, lockM1498RR_remN2, lockM1498RR_remN3,
      lockM1498RR_remN4, lockM1498RR_remN5, lockM1498RR_remN6, lockM1498RR_remN7].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 242 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) :
      LockBackend)).1.toErrTerms, ((⟨lockM1498T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend),
      (ofRatUp (((([lockM1498RR_remN0, lockM1498RR_remN1, lockM1498RR_remN2, lockM1498RR_remN3,
      lockM1498RR_remN4, lockM1498RR_remN5, lockM1498RR_remN6, lockM1498RR_remN7].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 242 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) : LockBackend)).2) := by
  rw [← lockM1498RR_rb, lockM1498a_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgLow.forWitness 3 1983) [3] lockM1498a
      lockM1498a
      112 advLow.p581.rr advLow.p581.ii advLow.p581.ri advLow.p581.ir
      ((⟨lockM1498T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advLow.p581.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM1498A8 lockM1498A9 ((adviceLookup_forWitness_cseg base.cfgLow 3 1983 []).trans
          ((congrArg (fun b => adviceLookup b [3, 1983]) lock_advLow_blocks).trans
          ((adviceLookup_skip_cseg advLow.b0 _ [3, 1983] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advLow.b1 _ [3, 1983] (by decide +kernel)).trans
          (adviceLookup_at_cseg
          advLow.b2 _ [3, 1983] 181 [3, 1983] (.packed 112 advLow.p581.rr advLow.p581.ii
          advLow.p581.ri
          advLow.p581.ir) (by decide +kernel) lockM1498_advAt (by decide +kernel))))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgLow.forWitness 3 1983).toMant base.weight 112
        advLow.p581.rr advLow.p581.ii advLow.p581.ri advLow.p581.ir lockM1498a lockM1498a
        (ma := ((lockM1498a.toMants (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])))
        (mb := ((lockM1498a.toMants (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])))
        (pRR := (advLow.p581.rr.targetTerms, advLow.p581.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM1498T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM1498A10)
        (eq_some_getD_cseg ([], []) lockM1498A11)
        (packedRealProduct_eq_of_sparse advLow.p581.rr base.weight (2 * 112) (((lockM1498a.toMants
          (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])).1) (((lockM1498a.toMants
          (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])).1) lockM1498A0 lockM1498A1
          lockM1498A2 lockM1498A3 lockM1498_sp)
        (packedRealProduct_eq_nil_left advLow.p581.ii base.weight (2 * 112) (((lockM1498a.toMants
          (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])).2) lockM1498A4)
        (packedRealProduct_eq_nil_right advLow.p581.ri base.weight (2 * 112) (((lockM1498a.toMants
          (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])).1) lockM1498A5)
        (packedRealProduct_eq_nil_left advLow.p581.ir base.weight (2 * 112) (((lockM1498a.toMants
          (base.cfgLow.forWitness 3 1983).toMant 112).getD ([], [])).1) lockM1498A6)
        lockM1498_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
