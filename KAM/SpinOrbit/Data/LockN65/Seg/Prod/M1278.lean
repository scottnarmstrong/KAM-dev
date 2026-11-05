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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1278Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1278 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1278_shards_cover :
    ∀ s ∈ advLow.p361.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7]], s ∈ g := by
  decide +kernel

theorem lockM1278_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7]], g.all (checkShardAt advLow.p361.ir
      (advLow.p361.ir.la.slotTerms (((lockM1278a.toMants (base.cfgLow.forWitness 1 1).toMant
      112).getD ([], [])).2)) (advLow.p361.ir.lb.slotTerms (((lockM1278b.toMants
      (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).1))) = true :=
  (List.forall_mem_cons.2 ⟨lockM1278_shardsG0, (List.forall_mem_cons.2 ⟨lockM1278_shardsG1, (fun _
    h => nomatch h)⟩)⟩)

theorem lockM1278_sp :
    checkPackedSp advLow.p361.ir (advLow.p361.ir.la.slotTerms (((lockM1278a.toMants
      (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).2)) (advLow.p361.ir.lb.slotTerms
      (((lockM1278b.toMants (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).1)) = true :=
  checkPackedSp_of_groups advLow.p361.ir (advLow.p361.ir.la.slotTerms (((lockM1278a.toMants
        (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).2)) (advLow.p361.ir.lb.slotTerms
        (((lockM1278b.toMants (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).1)) [[0, 1,
        2, 3], [4, 5, 6, 7]] lockM1278A7 lockM1278_shards_cover lockM1278_shards_groups









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM1278_advAt :
    advLow.b1[161]? = some ([1, 1, 0], (.packed 112 advLow.p361.rr advLow.p361.ii advLow.p361.ri
      advLow.p361.ir))
    := rfl

/-- The packed product 1278 (cfgLow, key [1, 1, 0]). -/
theorem lockM1278 :
    CertModel.polyProduct base.weight (base.cfgLow.forWitness 1 1) [1, 0] ((itemsPoly
      ((CertModel.toDeg base.weight base.piEnc 0 (lockLowCkpt.slotPair base.weight
      1110).1).poly.terms.filterMap (derivItem 0)))) ((base.wit.expWit[1]?.getD (⟨⟨[]⟩, 0, 0⟩ :
      ExpWitness LockBackend)).poly.negP) = some (((⟨[] ++ [] ++ [] ++ lockM1278T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM1278IR_remN0, lockM1278IR_remN1,
      lockM1278IR_remN2, lockM1278IR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 161 * 2 ^ (2 *
      112) : ℕ) : ℚ))) : LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ lockM1278T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM1278IR_remN0, lockM1278IR_remN1,
      lockM1278IR_remN2, lockM1278IR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 161 * 2 ^ (2 *
      112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM1278IR_rb, lockM1278a_eq, lockM1278b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgLow.forWitness 1 1) [1, 0] lockM1278a
      lockM1278b
      112 advLow.p361.rr advLow.p361.ii advLow.p361.ri advLow.p361.ir
      ((⟨[] ++ [] ++ [] ++ lockM1278T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advLow.p361.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM1278A8 lockM1278A9 ((adviceLookup_forWitness_cseg base.cfgLow 1 1 [0]).trans
          ((congrArg (fun b => adviceLookup b [1, 1, 0]) lock_advLow_blocks).trans
          ((adviceLookup_skip_cseg advLow.b0 _ [1, 1, 0] (by decide +kernel)).trans
          (adviceLookup_at_cseg advLow.b1 _ [1, 1, 0] 161 [1, 1, 0] (.packed 112 advLow.p361.rr
          advLow.p361.ii advLow.p361.ri advLow.p361.ir) (by decide +kernel) lockM1278_advAt (by
          decide +kernel)))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgLow.forWitness 1 1).toMant base.weight 112
        advLow.p361.rr advLow.p361.ii advLow.p361.ri advLow.p361.ir lockM1278a lockM1278b
        (ma := ((lockM1278a.toMants (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])))
        (mb := ((lockM1278b.toMants (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advLow.p361.ir.targetTerms, advLow.p361.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM1278T)
        (eq_some_getD_cseg ([], []) lockM1278A10)
        (eq_some_getD_cseg ([], []) lockM1278A11)
        (packedRealProduct_eq_nil_left advLow.p361.rr base.weight (2 * 112) (((lockM1278b.toMants
          (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).1) lockM1278A0)
        (packedRealProduct_eq_nil_right advLow.p361.ii base.weight (2 * 112) (((lockM1278a.toMants
          (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).2) lockM1278A1)
        (packedRealProduct_eq_nil_left advLow.p361.ri base.weight (2 * 112) (((lockM1278b.toMants
          (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).2) lockM1278A2)
        (packedRealProduct_eq_of_sparse advLow.p361.ir base.weight (2 * 112) (((lockM1278a.toMants
          (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).2) (((lockM1278b.toMants
          (base.cfgLow.forWitness 1 1).toMant 112).getD ([], [])).1) lockM1278A3 lockM1278A4
          lockM1278A5 lockM1278A6 lockM1278_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM1278_dec)

end KAM.SpinOrbit.Data.LockN65
