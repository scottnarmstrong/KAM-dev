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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1499Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1499 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1499_shards_cover :
    ∀ s ∈ advLow.p582.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]],
      s ∈ g := by
  decide +kernel

theorem lockM1499_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]], g.all (checkShardAt
      advLow.p582.rr lockM1499_shardsEA lockM1499_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM1499_shardsG0, (List.forall_mem_cons.2 ⟨lockM1499_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM1499_shardsG2, (List.forall_mem_cons.2 ⟨lockM1499_shardsG3, (fun
    _ h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM1499_sp :
    checkPackedSp advLow.p582.rr (advLow.p582.rr.la.slotTerms (((lockM1499a.toMants
      (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])).1)) (advLow.p582.rr.lb.slotTerms
      (((lockM1499b.toMants (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advLow.p582.rr) lockM1499_shardsEA_eq lockM1499_shardsEB_eq).trans
        (checkPackedSp_of_groups advLow.p582.rr lockM1499_shardsEA lockM1499_shardsEB [[0, 1, 2,
        3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]] lockM1499A7 lockM1499_shards_cover
        lockM1499_shards_groups)









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM1499_advAt :
    advLow.b2[182]? = some ([2, 7], (.packed 112 advLow.p582.rr advLow.p582.ii advLow.p582.ri
      advLow.p582.ir))
    := rfl

/-- The packed product 1499 (cfgLow, key [2, 7]). -/
theorem lockM1499 :
    CertModel.polyProduct base.weight (base.cfgLow.forWitness 2 7) [2] ((base.wit.invWit[7]?.getD
      (⟨[]⟩ : CertPoly LockBackend))) ((lockLowCkpt.slotPair base.weight 1983).1.poly) = some
      (((⟨lockM1499T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (((([lockM1499RR_remN0,
      lockM1499RR_remN1, lockM1499RR_remN2, lockM1499RR_remN3, lockM1499RR_remN4,
      lockM1499RR_remN5, lockM1499RR_remN6, lockM1499RR_remN7, lockM1499RR_remN8].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 254 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) :
      LockBackend)).1.toErrTerms, ((⟨lockM1499T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend),
      (ofRatUp (((([lockM1499RR_remN0, lockM1499RR_remN1, lockM1499RR_remN2, lockM1499RR_remN3,
      lockM1499RR_remN4, lockM1499RR_remN5, lockM1499RR_remN6, lockM1499RR_remN7,
      lockM1499RR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 254 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 +
      0 + 0) : LockBackend)).2) := by
  rw [← lockM1499RR_rb, lockM1499a_eq, lockM1499b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgLow.forWitness 2 7) [2] lockM1499a
      lockM1499b
      112 advLow.p582.rr advLow.p582.ii advLow.p582.ri advLow.p582.ir
      ((⟨lockM1499T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advLow.p582.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM1499A8 lockM1499A9 ((adviceLookup_forWitness_cseg base.cfgLow 2 7 []).trans
          ((congrArg (fun b => adviceLookup b [2, 7]) lock_advLow_blocks).trans
          ((adviceLookup_skip_cseg advLow.b0 _ [2, 7] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advLow.b1 _ [2, 7] (by decide +kernel)).trans
          (adviceLookup_at_cseg
          advLow.b2 _ [2, 7] 182 [2, 7] (.packed 112 advLow.p582.rr advLow.p582.ii advLow.p582.ri
          advLow.p582.ir) (by decide +kernel) lockM1499_advAt (by decide +kernel))))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgLow.forWitness 2 7).toMant base.weight 112
        advLow.p582.rr advLow.p582.ii advLow.p582.ri advLow.p582.ir lockM1499a lockM1499b
        (ma := ((lockM1499a.toMants (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])))
        (mb := ((lockM1499b.toMants (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])))
        (pRR := (advLow.p582.rr.targetTerms, advLow.p582.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM1499T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM1499A10)
        (eq_some_getD_cseg ([], []) lockM1499A11)
        (packedRealProduct_eq_of_sparse advLow.p582.rr base.weight (2 * 112) (((lockM1499a.toMants
          (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])).1) (((lockM1499b.toMants
          (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])).1) lockM1499A0 lockM1499A1
          lockM1499A2 lockM1499A3 lockM1499_sp)
        (packedRealProduct_eq_nil_left advLow.p582.ii base.weight (2 * 112) (((lockM1499b.toMants
          (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])).2) lockM1499A4)
        (packedRealProduct_eq_nil_right advLow.p582.ri base.weight (2 * 112) (((lockM1499a.toMants
          (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])).1) lockM1499A5)
        (packedRealProduct_eq_nil_left advLow.p582.ir base.weight (2 * 112) (((lockM1499b.toMants
          (base.cfgLow.forWitness 2 7).toMant 112).getD ([], [])).1) lockM1499A6)
        lockM1499_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
