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
public import KAM.SpinOrbit.Data.LockN65.Seg.PlanLow
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057RRRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1057Sh
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1057 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1057_shards_cover :
    ∀ s ∈ advLow.p140.rr.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]],
      s ∈ g := by
  decide +kernel

theorem lockM1057_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]], g.all (checkShardAt
      advLow.p140.rr lockM1057_shardsEA lockM1057_shardsEB) = true :=
  (List.forall_mem_cons.2 ⟨lockM1057_shardsG0, (List.forall_mem_cons.2 ⟨lockM1057_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM1057_shardsG2, (List.forall_mem_cons.2 ⟨lockM1057_shardsG3, (fun
    _ h => nomatch h)⟩)⟩)⟩)⟩)

theorem lockM1057_sp :
    checkPackedSp advLow.p140.rr (advLow.p140.rr.la.slotTerms (((lockM1057a.toMants
      (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])).1)) (advLow.p140.rr.lb.slotTerms
      (((lockM1057b.toMants (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])).1)) = true :=
  (congrArg₂ (checkPackedSp advLow.p140.rr) lockM1057_shardsEA_eq lockM1057_shardsEB_eq).trans
        (checkPackedSp_of_groups advLow.p140.rr lockM1057_shardsEA lockM1057_shardsEB [[0, 1, 2,
        3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13]] lockM1057A7 lockM1057_shards_cover
        lockM1057_shards_groups)









/-- The packed product 1057 (cfgLow, key [2, 3]). -/
theorem lockM1057 :
    CertModel.polyProduct base.weight (base.cfgLow.forWitness 2 3) [2] ((base.wit.invWit[3]?.getD
      (⟨[]⟩ : CertPoly LockBackend))) ((lockLowCkpt.slotPair base.weight 433).1.poly) = some
      (((⟨lockM1057T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (((([lockM1057RR_remN0,
      lockM1057RR_remN1, lockM1057RR_remN2, lockM1057RR_remN3, lockM1057RR_remN4,
      lockM1057RR_remN5, lockM1057RR_remN6, lockM1057RR_remN7, lockM1057RR_remN8].sum : ℕ) : ℚ) /
      ((base.weight.w.den ^ 254 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0 + 0) :
      LockBackend)).1.toErrTerms, ((⟨lockM1057T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend),
      (ofRatUp (((([lockM1057RR_remN0, lockM1057RR_remN1, lockM1057RR_remN2, lockM1057RR_remN3,
      lockM1057RR_remN4, lockM1057RR_remN5, lockM1057RR_remN6, lockM1057RR_remN7,
      lockM1057RR_remN8].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 254 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 +
      0 + 0) : LockBackend)).2) := by
  rw [← lockM1057RR_rb, lockM1057a_eq, lockM1057b_eq]
  exact polyProduct_eq_of_mulPacked base.weight (base.cfgLow.forWitness 2 3) [2] lockM1057a
      lockM1057b
      112 advLow.p140.rr advLow.p140.ii advLow.p140.ri advLow.p140.ir
      ((⟨lockM1057T ++ [] ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp
        (advLow.p140.rr.remainderBound base.weight (2 * 112) + 0 + 0 + 0) : LockBackend))
      lockM1057A8 lockM1057A9 rfl
      (CertPoly.mulPacked_eq_of_parts (base.cfgLow.forWitness 2 3).toMant base.weight 112
        advLow.p140.rr advLow.p140.ii advLow.p140.ri advLow.p140.ir lockM1057a lockM1057b
        (ma := ((lockM1057a.toMants (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])))
        (mb := ((lockM1057b.toMants (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])))
        (pRR := (advLow.p140.rr.targetTerms, advLow.p140.rr.remainderBound base.weight (2 * 112)))
        (pII := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := lockM1057T)
        (tII := ([] : List (CertKey × CC LockBackend)))
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM1057A10)
        (eq_some_getD_cseg ([], []) lockM1057A11)
        (packedRealProduct_eq_of_sparse advLow.p140.rr base.weight (2 * 112) (((lockM1057a.toMants
          (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])).1) (((lockM1057b.toMants
          (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])).1) lockM1057A0 lockM1057A1
          lockM1057A2 lockM1057A3 lockM1057_sp)
        (packedRealProduct_eq_nil_left advLow.p140.ii base.weight (2 * 112) (((lockM1057b.toMants
          (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])).2) lockM1057A4)
        (packedRealProduct_eq_nil_right advLow.p140.ri base.weight (2 * 112) (((lockM1057a.toMants
          (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])).1) lockM1057A5)
        (packedRealProduct_eq_nil_left advLow.p140.ir base.weight (2 * 112) (((lockM1057b.toMants
          (base.cfgLow.forWitness 2 3).toMant 112).getD ([], [])).1) lockM1057A6)
        lockM1057_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
