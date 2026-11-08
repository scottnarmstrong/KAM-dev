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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922RIRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M1922Sh
public import KAM.SpinOrbit.Data.LockN65.Seg.StageMats
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 1922 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM1922_shards_cover :
    ∀ s ∈ advLow.p988.ri.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10]], s ∈ g := by
  decide +kernel

theorem lockM1922_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10]], g.all (checkShardAt advLow.p988.ri
      (advLow.p988.ri.la.slotTerms (((lockM1922a.toMants base.cfgLow.toMant 112).getD ([], [])).1))
      (advLow.p988.ri.lb.slotTerms (((lockM1922b.toMants base.cfgLow.toMant 112).getD ([],
      [])).2))) = true :=
  (List.forall_mem_cons.2 ⟨lockM1922_shardsG0, (List.forall_mem_cons.2 ⟨lockM1922_shardsG1,
    (List.forall_mem_cons.2 ⟨lockM1922_shardsG2, (fun _ h => nomatch h)⟩)⟩)⟩)

theorem lockM1922_sp :
    checkPackedSp advLow.p988.ri (advLow.p988.ri.la.slotTerms (((lockM1922a.toMants
      base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p988.ri.lb.slotTerms (((lockM1922b.toMants
      base.cfgLow.toMant 112).getD ([], [])).2)) = true :=
  checkPackedSp_of_groups advLow.p988.ri (advLow.p988.ri.la.slotTerms (((lockM1922a.toMants
        base.cfgLow.toMant 112).getD ([], [])).1)) (advLow.p988.ri.lb.slotTerms
        (((lockM1922b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) [[0, 1, 2, 3], [4, 5, 6,
        7], [8, 9, 10]] lockM1922A7 lockM1922_shards_cover lockM1922_shards_groups









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM1922_advAt :
    advLow.b4[188]? = some ([4, 1, 1, 1, 2], (.packed 112 advLow.p988.rr advLow.p988.ii
      advLow.p988.ri advLow.p988.ir))
    := rfl

/-- The packed product 1922 (cfgLow, key [4, 1, 1, 1, 2]). -/
theorem lockM1922 :
    CertModel.polyProduct base.weight base.cfgLow ([4, 1] ++ [1, 1, 2]) ((modelMatrixEntry
      (modelMatTranspose (2 + 2) 2 lockTDL) 1 2).poly) ((modelMatrixEntry lockTL 2 1).poly) = some
      (((⟨[] ++ [] ++ lockM1922T ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 +
      ((([lockM1922RI_remN0, lockM1922RI_remN1, lockM1922RI_remN2, lockM1922RI_remN3,
      lockM1922RI_remN4, lockM1922RI_remN5, lockM1922RI_remN6].sum : ℕ) : ℚ) / ((base.weight.w.den
      ^ 220 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0) : LockBackend)).1.toErrTerms, ((⟨[] ++ [] ++ lockM1922T
      ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 + ((([lockM1922RI_remN0, lockM1922RI_remN1,
      lockM1922RI_remN2, lockM1922RI_remN3, lockM1922RI_remN4, lockM1922RI_remN5,
      lockM1922RI_remN6].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 220 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0)
      : LockBackend)).2) := by
  rw [← lockM1922RI_rb, lockM1922a_eq, lockM1922b_eq]
  exact polyProduct_eq_of_mulPacked base.weight base.cfgLow ([4, 1] ++ [1, 1, 2]) lockM1922a
      lockM1922b
      112 advLow.p988.rr advLow.p988.ii advLow.p988.ri advLow.p988.ir
      ((⟨[] ++ [] ++ lockM1922T ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 + 0 +
        advLow.p988.ri.remainderBound base.weight (2 * 112) + 0) : LockBackend))
      lockM1922A8 lockM1922A9 ((congrArg (fun b => adviceLookup b ([4, 1] ++ [1, 1, 2]))
          lock_advLow_blocks).trans ((adviceLookup_skip_cseg advLow.b0 _ ([4, 1] ++ [1, 1, 2]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b1 _ ([4, 1] ++ [1, 1, 2]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b2 _ ([4, 1] ++ [1, 1, 2]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b3 _ ([4, 1] ++ [1, 1, 2]) (by
          decide +kernel)).trans (adviceLookup_at_cseg advLow.b4 _ ([4, 1] ++ [1, 1, 2]) 188 [4, 1,
          1, 1, 2] (.packed 112 advLow.p988.rr advLow.p988.ii advLow.p988.ri advLow.p988.ir) (by
          decide +kernel) lockM1922_advAt (by decide +kernel)))))))
      (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 112 advLow.p988.rr
        advLow.p988.ii advLow.p988.ri advLow.p988.ir lockM1922a lockM1922b
        (ma := ((lockM1922a.toMants base.cfgLow.toMant 112).getD ([], [])))
        (mb := ((lockM1922b.toMants base.cfgLow.toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pII := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pRI := (advLow.p988.ri.targetTerms, advLow.p988.ri.remainderBound base.weight (2 * 112)))
        (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ))) (tRR := ([] : List (CertKey × CC
            LockBackend)))
        (tII := ([] : List (CertKey × CC LockBackend))) (tRI := lockM1922T)
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM1922A10)
        (eq_some_getD_cseg ([], []) lockM1922A11)
        (packedRealProduct_eq_nil_right advLow.p988.rr base.weight (2 * 112) (((lockM1922a.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM1922A0)
        (packedRealProduct_eq_nil_left advLow.p988.ii base.weight (2 * 112) (((lockM1922b.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM1922A1)
        (packedRealProduct_eq_of_sparse advLow.p988.ri base.weight (2 * 112) (((lockM1922a.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) (((lockM1922b.toMants base.cfgLow.toMant
          112).getD ([], [])).2) lockM1922A2 lockM1922A3 lockM1922A4 lockM1922A5 lockM1922_sp)
        (packedRealProduct_eq_nil_left advLow.p988.ir base.weight (2 * 112) (((lockM1922b.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM1922A6)
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _)
        lockM1922_dec
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
