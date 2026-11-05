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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M6Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 6 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM6_shards_cover :
    ∀ s ∈ advFull.p6.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]], s ∈ g := by
  decide +kernel

theorem lockM6_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]], g.all (checkShardAt advFull.p6.ir
      lockM6_shardsEA lockM6_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM6_shardsG0, (List.forall_mem_cons.2 ⟨lockM6_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM6_shardsG2, (fun _ h => nomatch h)⟩)⟩)⟩)

theorem lockM6_sp :
    checkPackedSp advFull.p6.ir (advFull.p6.ir.la.slotTerms (((lockM6a.toMants
      (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).2))
      (advFull.p6.ir.lb.slotTerms (((lockM6b.toMants (base.cfgFull.forWitness 1
      (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advFull.p6.ir) lockM6_shardsEA_eq lockM6_shardsEB_eq).trans
        (checkPackedSp_of_groups advFull.p6.ir lockM6_shardsEA lockM6_shardsEB [[0, 1, 2, 3], [4,
        5, 6, 7], [8, 9, 10, 11]] lockM6A7 lockM6_shards_cover lockM6_shards_groups)









/-- The packed product 6 (cfgFull, key [1, 4, 1]). -/
theorem lockM6 :
    CertModel.polyProduct base.weight (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)) [1,
      1] ((itemsPoly ((charPhaseModel 2 base.emb base.weight base.piEnc [1,
      0]).poly.terms.filterMap (derivItem 1)))) ((⟨charE⟩ : CertPoly LockBackend).negP) = some
      (((⟨[] ++ [] ++ [] ++ lockM6T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
      ((([lockM6IR_remN0, lockM6IR_remN1, lockM6IR_remN2, lockM6IR_remN3, lockM6IR_remN4,
      lockM6IR_remN5, lockM6IR_remN6, lockM6IR_remN7, lockM6IR_remN8].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 245 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).1.toErrTerms, ((⟨[] ++
      [] ++ [] ++ lockM6T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 + ((([lockM6IR_remN0,
      lockM6IR_remN1, lockM6IR_remN2, lockM6IR_remN3, lockM6IR_remN4, lockM6IR_remN5,
      lockM6IR_remN6, lockM6IR_remN7, lockM6IR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 245 * 2
      ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM6IR_rb, lockM6a_eq, lockM6b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgFull.forWitness 1 (base.wit.expWit.length +
      0))
      [1, 1] lockM6a lockM6b 112 advFull.p6.rr advFull.p6.ii advFull.p6.ri advFull.p6.ir
      ((⟨[] ++ [] ++ [] ++ lockM6T⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + 0 +
        advFull.p6.ir.remainderBound base.weight (2 * 112)) : LockBackend))
      lockM6A8 lockM6A9 rfl
      (CertPoly.mulPacked_eq_of_parts (base.cfgFull.forWitness 1 (base.wit.expWit.length +
          0)).toMant
        base.weight 112 advFull.p6.rr advFull.p6.ii advFull.p6.ri advFull.p6.ir lockM6a lockM6b
        (ma := ((lockM6a.toMants (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)).toMant
          112).getD ([], [])))
        (mb := ((lockM6b.toMants (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)).toMant
          112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (advFull.p6.ir.targetTerms, advFull.p6.ir.remainderBound base.weight (2 * 112)))
        (tRR := ([] : List (CertKey × CC LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend))) (tIR := lockM6T)
        (eq_some_getD_cseg ([], []) lockM6A10)
        (eq_some_getD_cseg ([], []) lockM6A11)
        (packedRealProduct_eq_nil_left advFull.p6.rr base.weight (2 * 112) (((lockM6b.toMants
          (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).1)
          lockM6A0)
        (packedRealProduct_eq_nil_right advFull.p6.ii base.weight (2 * 112) (((lockM6a.toMants
          (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).2)
          lockM6A1)
        (packedRealProduct_eq_nil_left advFull.p6.ri base.weight (2 * 112) (((lockM6b.toMants
          (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).2)
          lockM6A2)
        (packedRealProduct_eq_of_sparse advFull.p6.ir base.weight (2 * 112) (((lockM6a.toMants
          (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)).toMant 112).getD ([], [])).2)
          (((lockM6b.toMants (base.cfgFull.forWitness 1 (base.wit.expWit.length + 0)).toMant
          112).getD ([], [])).1) lockM6A3 lockM6A4 lockM6A5 lockM6A6 lockM6_sp)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM6_dec)

end KAM.SpinOrbit.Data.LockN65
