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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1664Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1664 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1664_shards_cover :
    ∀ s ∈ advLow.p747.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7]], s ∈ g := by
  decide +kernel

theorem lockM1664_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7]], g.all (checkShardAt advLow.p747.ir
      (advLow.p747.ir.la.slotTerms (((lockM1664a.toMants (base.cfgLow.forWitness 1 3).toMant
      112).getD ([], [])).2)) (advLow.p747.ir.lb.slotTerms (((lockM1664b.toMants
      (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).1))) = true :=
  (List.forall_mem_cons.2 ⟨lockM1664_shardsG0, (List.forall_mem_cons.2 ⟨lockM1664_shardsG1, (fun _
    h => nomatch h)⟩)⟩)

theorem lockM1664_sp :
    checkPackedSp advLow.p747.ir (advLow.p747.ir.la.slotTerms (((lockM1664a.toMants
      (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).2)) (advLow.p747.ir.lb.slotTerms
      (((lockM1664b.toMants (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).1)) = true :=
  checkPackedSp_of_groups advLow.p747.ir (advLow.p747.ir.la.slotTerms (((lockM1664a.toMants
        (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).2)) (advLow.p747.ir.lb.slotTerms
        (((lockM1664b.toMants (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).1)) [[0, 1,
        2, 3], [4, 5, 6, 7]] lockM1664A7 lockM1664_shards_cover lockM1664_shards_groups









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM1664_advAt :
    advLow.b3[147]? = some ([1, 3, 1], (.packed 112 advLow.p747.rr advLow.p747.ii advLow.p747.ri
      advLow.p747.ir))
    := rfl

/-- The packed product 1664 (cfgLow, key [1, 3, 1]). -/
theorem lockM1664 :
    CertModel.polyProduct base.weight (base.cfgLow.forWitness 1 3) [1, 1] ((itemsPoly
      ((CertModel.toDeg base.weight base.piEnc 0 (lockLowCkpt.slotPair base.weight
      2306).1).poly.terms.filterMap (derivItem 1)))) ((base.wit.expWit[3]?.getD (⟨⟨[]⟩, 0, 0⟩ :
      ExpWitness LockBackend)).poly.negP) = some (((⟨[] ++ [] ++ [] ++ lockM1664T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM1664IR_remN0, lockM1664IR_remN1,
      lockM1664IR_remN2, lockM1664IR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 160 * 2 ^ (2 *
      112) : ℕ) : ℚ))) : LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ [] ++ lockM1664T⟩ : CertPoly
      LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM1664IR_remN0, lockM1664IR_remN1,
      lockM1664IR_remN2, lockM1664IR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 160 * 2 ^ (2 *
      112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM1664IR_rb, lockM1664a_eq, lockM1664b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgLow.forWitness 1 3) [1, 1] lockM1664a
      lockM1664b
      112 advLow.p747.rr advLow.p747.ii advLow.p747.ri advLow.p747.ir
      ((⟨[] ++ [] ++ [] ++ lockM1664T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advLow.p747.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM1664A8 lockM1664A9 ((adviceLookup_forWitness_cseg base.cfgLow 1 3 [1]).trans
          ((congrArg (fun b => adviceLookup b [1, 3, 1]) lock_advLow_blocks).trans
          ((adviceLookup_skip_cseg advLow.b0 _ [1, 3, 1] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advLow.b1 _ [1, 3, 1] (by decide +kernel)).trans
          ((adviceLookup_skip_cseg advLow.b2 _ [1, 3, 1] (by decide +kernel)).trans
          (adviceLookup_at_cseg advLow.b3 _ [1, 3, 1] 147 [1, 3, 1] (.packed 112 advLow.p747.rr
          advLow.p747.ii advLow.p747.ri advLow.p747.ir) (by decide +kernel) lockM1664_advAt (by
          decide +kernel)))))))
      (CertPoly.mulPacked_eq_of_parts (base.cfgLow.forWitness 1 3).toMant base.weight 112
        advLow.p747.rr advLow.p747.ii advLow.p747.ri advLow.p747.ir lockM1664a lockM1664b
        (ma := ((lockM1664a.toMants (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])))
        (mb := ((lockM1664b.toMants (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advLow.p747.ir.targetTerms, advLow.p747.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM1664T)
        (eq_some_getD_cseg ([], []) lockM1664A10)
        (eq_some_getD_cseg ([], []) lockM1664A11)
        (packedRealProduct_eq_nil_left advLow.p747.rr base.weight (2 * 112) (((lockM1664b.toMants
          (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).1) lockM1664A0)
        (packedRealProduct_eq_nil_right advLow.p747.ii base.weight (2 * 112) (((lockM1664a.toMants
          (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).2) lockM1664A1)
        (packedRealProduct_eq_nil_left advLow.p747.ri base.weight (2 * 112) (((lockM1664b.toMants
          (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).2) lockM1664A2)
        (packedRealProduct_eq_of_sparse advLow.p747.ir base.weight (2 * 112) (((lockM1664a.toMants
          (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).2) (((lockM1664b.toMants
          (base.cfgLow.forWitness 1 3).toMant 112).getD ([], [])).1) lockM1664A3 lockM1664A4
          lockM1664A5 lockM1664A6 lockM1664_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM1664_dec)

end KAM.SpinOrbit.Data.LockN65
