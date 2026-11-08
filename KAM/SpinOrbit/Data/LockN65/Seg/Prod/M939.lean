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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M939Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 939 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM939_shards_cover :
    ∀ s ∈ advLow.p22.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], s ∈ g
      := by
  decide +kernel

theorem lockM939_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12]], g.all (checkShardAt advLow.p22.ir
      lockM939_shardsEA lockM939_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM939_shardsG0, (List.forall_mem_cons.2 ⟨lockM939_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM939_shardsG2, (List.forall_mem_cons.2 ⟨lockM939_shardsG3, (fun _
    h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM939_sp :
    checkPackedSp advLow.p22.ir (advLow.p22.ir.la.slotTerms (((lockM939a.toMants
      (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).2))
      (advLow.p22.ir.lb.slotTerms (((lockM939b.toMants (base.cfgLow.forWitness 1
      (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advLow.p22.ir) lockM939_shardsEA_eq lockM939_shardsEB_eq).trans
        (checkPackedSp_of_groups advLow.p22.ir lockM939_shardsEA lockM939_shardsEB [[0, 1, 2, 3],
        [4, 5, 6, 7], [8, 9, 10, 11], [12]] lockM939A7 lockM939_shards_cover
        lockM939_shards_groups)









/-- The packed product 939 (cfgLow, key [1, 4, 0]). -/
theorem lockM939 :
    CertModel.polyProduct base.weight (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)) [1,
      0] ((itemsPoly ((charPhaseModel 2 base.emb base.weight base.piEnc [1,
      0]).poly.terms.filterMap (derivItem 0)))) ((⟨charE⟩ : CertPoly LockBackend).negP) = some
      (((⟨[] ++ [] ++ [] ++ lockM939T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
      ((([lockM939IR_remN0, lockM939IR_remN1, lockM939IR_remN2, lockM939IR_remN3, lockM939IR_remN4,
      lockM939IR_remN5, lockM939IR_remN6, lockM939IR_remN7, lockM939IR_remN8].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 249 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).1.toErrTerms, ((⟨[] ++
      [] ++ [] ++ lockM939T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM939IR_remN0,
      lockM939IR_remN1, lockM939IR_remN2, lockM939IR_remN3, lockM939IR_remN4, lockM939IR_remN5,
      lockM939IR_remN6, lockM939IR_remN7, lockM939IR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^
      249 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM939IR_rb, lockM939a_eq, lockM939b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgLow.forWitness 1 (base.wit.expWit.length +
      0))
      [1, 0] lockM939a lockM939b 112 advLow.p22.rr advLow.p22.ii advLow.p22.ri advLow.p22.ir
      ((⟨[] ++ [] ++ [] ++ lockM939T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advLow.p22.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM939A8 lockM939A9 rfl
      (CertPoly.mulPacked_eq_of_parts (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant
        base.weight 112 advLow.p22.rr advLow.p22.ii advLow.p22.ri advLow.p22.ir lockM939a lockM939b
        (ma := ((lockM939a.toMants (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant
          112).getD ([], [])))
        (mb := ((lockM939b.toMants (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant
          112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advLow.p22.ir.targetTerms, advLow.p22.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM939T)
        (eq_some_getD_cseg ([], []) lockM939A10)
        (eq_some_getD_cseg ([], []) lockM939A11)
        (packedRealProduct_eq_nil_left advLow.p22.rr base.weight (2 * 112) (((lockM939b.toMants
          (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).1)
          lockM939A0)
        (packedRealProduct_eq_nil_right advLow.p22.ii base.weight (2 * 112) (((lockM939a.toMants
          (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).2)
          lockM939A1)
        (packedRealProduct_eq_nil_left advLow.p22.ri base.weight (2 * 112) (((lockM939b.toMants
          (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).2)
          lockM939A2)
        (packedRealProduct_eq_of_sparse advLow.p22.ir base.weight (2 * 112) (((lockM939a.toMants
          (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).2)
          (((lockM939b.toMants (base.cfgLow.forWitness 1 (base.wit.expWit.length + 0)).toMant
          112).getD ([], [])).1) lockM939A3 lockM939A4 lockM939A5 lockM939A6 lockM939_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM939_dec)

end KAM.SpinOrbit.Data.LockN65
