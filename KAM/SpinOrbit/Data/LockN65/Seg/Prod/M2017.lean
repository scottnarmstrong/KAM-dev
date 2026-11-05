/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.AdvLookup
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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux12
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux13
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux14
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux15
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux16
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux17
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux18
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux19
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux20
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux21
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux22
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux23
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017IIDec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017IIRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017IISh
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017IRDec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017IRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017IRSh
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017RIDec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017RIRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017RISh
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017RRDec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017RRSh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 2017 (generated)

The product equation from its parts' shards and decodes (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith



theorem lockM2017_rr_shards_cover :
    ∀ s ∈ advLow.p1083.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13,
      14]], s ∈ g := by
  decide +kernel

theorem lockM2017_rr_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14]], g.all (checkShardAt
      advLow.p1083.rr lockM2017_rr_shardsEA lockM2017_rr_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM2017_rr_shardsG0, (List.forall_mem_cons.2 ⟨lockM2017_rr_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM2017_rr_shardsG2, (List.forall_mem_cons.2 ⟨lockM2017_rr_shardsG3,
    (fun _ h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM2017_ii_shards_cover :
    ∀ s ∈ advLow.p1083.ii.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13,
      14]], s ∈ g := by
  decide +kernel

theorem lockM2017_ii_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14]], g.all (checkShardAt
      advLow.p1083.ii (advLow.p1083.ii.la.slotTerms (((lockM2017a.toMants base.cfgLow.toMant
      112).getD ([], [])).2)) (advLow.p1083.ii.lb.slotTerms (((lockM2017b.toMants
      base.cfgLow.toMant 112).getD ([], [])).2))) = true :=
  (List.forall_mem_cons.2 ⟨lockM2017_ii_shardsG0, (List.forall_mem_cons.2 ⟨lockM2017_ii_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM2017_ii_shardsG2, (List.forall_mem_cons.2 ⟨lockM2017_ii_shardsG3,
    (fun _ h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM2017_ri_shards_cover :
    ∀ s ∈ advLow.p1083.ri.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13,
      14]], s ∈ g := by
  decide +kernel

theorem lockM2017_ri_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14]], g.all (checkShardAt
      advLow.p1083.ri (advLow.p1083.ri.la.slotTerms (((lockM2017a.toMants base.cfgLow.toMant
      112).getD ([], [])).1)) (advLow.p1083.ri.lb.slotTerms (((lockM2017b.toMants
      base.cfgLow.toMant 112).getD ([], [])).2))) = true :=
  (List.forall_mem_cons.2 ⟨lockM2017_ri_shardsG0, (List.forall_mem_cons.2 ⟨lockM2017_ri_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM2017_ri_shardsG2, (List.forall_mem_cons.2 ⟨lockM2017_ri_shardsG3,
    (fun _ h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM2017_ir_shards_cover :
    ∀ s ∈ advLow.p1083.ir.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13,
      14]], s ∈ g := by
  decide +kernel

theorem lockM2017_ir_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14]], g.all (checkShardAt
      advLow.p1083.ir (advLow.p1083.ir.la.slotTerms (((lockM2017a.toMants base.cfgLow.toMant
      112).getD ([], [])).2)) (advLow.p1083.ir.lb.slotTerms (((lockM2017b.toMants
      base.cfgLow.toMant 112).getD ([], [])).1))) = true :=
  (List.forall_mem_cons.2 ⟨lockM2017_ir_shardsG0, (List.forall_mem_cons.2 ⟨lockM2017_ir_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM2017_ir_shardsG2, (List.forall_mem_cons.2 ⟨lockM2017_ir_shardsG3,
    (fun _ h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM2017_rr_sp :
    checkPackedSp advLow.p1083.rr (advLow.p1083.rr.la.slotTerms (((lockM2017a.toMants
      base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p1083.rr.lb.slotTerms
      (((lockM2017b.toMants base.cfgLow.toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advLow.p1083.rr) lockM2017_rr_shardsEA_eq
        lockM2017_rr_shardsEB_eq).trans (checkPackedSp_of_groups advLow.p1083.rr
        lockM2017_rr_shardsEA lockM2017_rr_shardsEB [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11],
        [12, 13, 14]] lockM2017A0 lockM2017_rr_shards_cover lockM2017_rr_shards_groups)











theorem lockM2017_ii_sp :
    checkPackedSp advLow.p1083.ii (advLow.p1083.ii.la.slotTerms (((lockM2017a.toMants
      base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1083.ii.lb.slotTerms
      (((lockM2017b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) = true :=
  checkPackedSp_of_groups advLow.p1083.ii (advLow.p1083.ii.la.slotTerms (((lockM2017a.toMants
        base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1083.ii.lb.slotTerms
        (((lockM2017b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) [[0, 1, 2, 3], [4, 5, 6,
        7], [8, 9, 10, 11], [12, 13, 14]] lockM2017A5 lockM2017_ii_shards_cover
        lockM2017_ii_shards_groups











theorem lockM2017_ri_sp :
    checkPackedSp advLow.p1083.ri (advLow.p1083.ri.la.slotTerms (((lockM2017a.toMants
      base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p1083.ri.lb.slotTerms
      (((lockM2017b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) = true :=
  checkPackedSp_of_groups advLow.p1083.ri (advLow.p1083.ri.la.slotTerms (((lockM2017a.toMants
        base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p1083.ri.lb.slotTerms
        (((lockM2017b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) [[0, 1, 2, 3], [4, 5, 6,
        7], [8, 9, 10, 11], [12, 13, 14]] lockM2017A10 lockM2017_ri_shards_cover
        lockM2017_ri_shards_groups











theorem lockM2017_ir_sp :
    checkPackedSp advLow.p1083.ir (advLow.p1083.ir.la.slotTerms (((lockM2017a.toMants
      base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1083.ir.lb.slotTerms
      (((lockM2017b.toMants base.cfgLow.toMant 112).getD ([], [])).1)) = true :=
  checkPackedSp_of_groups advLow.p1083.ir (advLow.p1083.ir.la.slotTerms (((lockM2017a.toMants
        base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1083.ir.lb.slotTerms
        (((lockM2017b.toMants base.cfgLow.toMant 112).getD ([], [])).1)) [[0, 1, 2, 3], [4, 5, 6,
        7], [8, 9, 10, 11], [12, 13, 14]] lockM2017A15 lockM2017_ir_shards_cover
        lockM2017_ir_shards_groups

















/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM2017_advAt :
    advLow.b6[1]? = some ([7, 2], (.packed 112 advLow.p1083.rr advLow.p1083.ii advLow.p1083.ri
      advLow.p1083.ir))
    := rfl

/-- The packed product 2017 (cfgLow, key [7, 2]). -/
theorem lockM2017 :
    CertModel.polyProduct base.weight base.cfgLow [7, 2] (sosHiPoly) (sosHiPoly.conjSorted) = some
      (((⟨lockM2017TRR ++ lockM2017TII ++ lockM2017TRI ++ lockM2017TIR⟩ : CertPoly LockBackend),
      (ofRatUp (((([lockM2017RR_remN0, lockM2017RR_remN1, lockM2017RR_remN2, lockM2017RR_remN3].sum
      : ℕ) : ℚ) / ((base.weight.w.den ^ 240 * 2 ^ (2 * 112) : ℕ) : ℚ)) + ((([lockM2017II_remN0,
      lockM2017II_remN1, lockM2017II_remN2, lockM2017II_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den
      ^ 240 * 2 ^ (2 * 112) : ℕ) : ℚ)) + ((([lockM2017RI_remN0, lockM2017RI_remN1,
      lockM2017RI_remN2, lockM2017RI_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 240 * 2 ^ (2 *
      112) : ℕ) : ℚ)) + ((([lockM2017IR_remN0, lockM2017IR_remN1, lockM2017IR_remN2,
      lockM2017IR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 240 * 2 ^ (2 * 112) : ℕ) : ℚ))) :
      LockBackend)).1.toErrTerms, ((⟨lockM2017TRR ++ lockM2017TII ++ lockM2017TRI ++ lockM2017TIR⟩
      : CertPoly LockBackend), (ofRatUp (((([lockM2017RR_remN0, lockM2017RR_remN1,
      lockM2017RR_remN2, lockM2017RR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 240 * 2 ^ (2 *
      112) : ℕ) : ℚ)) + ((([lockM2017II_remN0, lockM2017II_remN1, lockM2017II_remN2,
      lockM2017II_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 240 * 2 ^ (2 * 112) : ℕ) : ℚ)) +
      ((([lockM2017RI_remN0, lockM2017RI_remN1, lockM2017RI_remN2, lockM2017RI_remN3].sum : ℕ) : ℚ)
      / ((base.weight.w.den ^ 240 * 2 ^ (2 * 112) : ℕ) : ℚ)) + ((([lockM2017IR_remN0,
      lockM2017IR_remN1, lockM2017IR_remN2, lockM2017IR_remN3].sum : ℕ) : ℚ) / ((base.weight.w.den
      ^ 240 * 2 ^ (2 * 112) : ℕ) : ℚ))) : LockBackend)).2) := by
  rw [← lockM2017RR_rb, ← lockM2017II_rb, ← lockM2017RI_rb, ← lockM2017IR_rb, lockM2017b_eq,
      lockM2017a_eq]
  exact polyProduct_eq_of_mulPacked base.weight base.cfgLow [7, 2] lockM2017a lockM2017b 112
      advLow.p1083.rr advLow.p1083.ii advLow.p1083.ri advLow.p1083.ir
      ((⟨lockM2017TRR ++ lockM2017TII ++ lockM2017TRI ++ lockM2017TIR⟩ : CertPoly LockBackend),
        (ofRatUp (advLow.p1083.rr.remainderBound base.weight (2 * 112) +
        advLow.p1083.ii.remainderBound base.weight (2 * 112) + advLow.p1083.ri.remainderBound
        base.weight (2 * 112) + advLow.p1083.ir.remainderBound base.weight (2 * 112)) :
            LockBackend))
      lockM2017A20 lockM2017A21 ((congrArg (fun b => adviceLookup b [7, 2])
          lock_advLow_blocks).trans ((adviceLookup_skip_cseg advLow.b0 _ [7, 2] (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b1 _ [7, 2] (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b2 _ [7, 2] (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b3 _ [7, 2] (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b4 _ [7, 2] (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b5 _ [7, 2] (by
          decide +kernel)).trans (adviceLookup_at_cseg advLow.b6 _ [7, 2] 1 [7, 2] (.packed 112
          advLow.p1083.rr advLow.p1083.ii advLow.p1083.ri advLow.p1083.ir) (by decide +kernel)
          lockM2017_advAt
          (by decide +kernel)))))))))
      (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 112 advLow.p1083.rr
        advLow.p1083.ii advLow.p1083.ri advLow.p1083.ir lockM2017a lockM2017b
        (ma := ((lockM2017a.toMants base.cfgLow.toMant 112).getD ([], [])))
        (mb := ((lockM2017b.toMants base.cfgLow.toMant 112).getD ([], [])))
        (pRR := (advLow.p1083.rr.targetTerms, advLow.p1083.rr.remainderBound base.weight (2 * 112)))
        (pII := (advLow.p1083.ii.targetTerms, advLow.p1083.ii.remainderBound base.weight (2 * 112)))
        (pRI := (advLow.p1083.ri.targetTerms, advLow.p1083.ri.remainderBound base.weight (2 * 112)))
        (pIR := (advLow.p1083.ir.targetTerms, advLow.p1083.ir.remainderBound base.weight (2 * 112)))
        (tRR := lockM2017TRR) (tII := lockM2017TII) (tRI := lockM2017TRI) (tIR := lockM2017TIR)
        (eq_some_getD_cseg ([], []) lockM2017A22)
        (eq_some_getD_cseg ([], []) lockM2017A23)
        (packedRealProduct_eq_of_sparse advLow.p1083.rr base.weight (2 * 112) (((lockM2017a.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) (((lockM2017b.toMants base.cfgLow.toMant
          112).getD ([], [])).1) lockM2017A1 lockM2017A2 lockM2017A3 lockM2017A4 lockM2017_rr_sp)
        (packedRealProduct_eq_of_sparse advLow.p1083.ii base.weight (2 * 112) (((lockM2017a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) (((lockM2017b.toMants base.cfgLow.toMant
          112).getD ([], [])).2) lockM2017A6 lockM2017A7 lockM2017A8 lockM2017A9 lockM2017_ii_sp)
        (packedRealProduct_eq_of_sparse advLow.p1083.ri base.weight (2 * 112) (((lockM2017a.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) (((lockM2017b.toMants base.cfgLow.toMant
          112).getD ([], [])).2) lockM2017A11 lockM2017A12 lockM2017A13 lockM2017A14
              lockM2017_ri_sp)
        (packedRealProduct_eq_of_sparse advLow.p1083.ir base.weight (2 * 112) (((lockM2017a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) (((lockM2017b.toMants base.cfgLow.toMant
          112).getD ([], [])).1) lockM2017A16 lockM2017A17 lockM2017A18 lockM2017A19
              lockM2017_ir_sp)
        lockM2017_rr_dec
        lockM2017_ii_dec
        lockM2017_ri_dec
        lockM2017_ir_dec)

end KAM.SpinOrbit.Data.LockN65
