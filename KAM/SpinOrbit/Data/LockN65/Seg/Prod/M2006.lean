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
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Arg
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux0
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux1
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux10
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux11
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux2
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux3
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux4
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux5
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux6
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux7
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux8
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Aux9
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Dec
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006IIRem
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2006Sh
public import KAM.SpinOrbit.Data.LockN65.Seg.StageMats
public import KAM.SpinOrbit.Data.LockN65.SegRoutes
public import KAM.SpinOrbit.Data.LockN65.SegSupport
public import KAM.SpinOrbit.Data.LockN65.ZRows

/-!
# Packed product 2006 (generated)

The product equation from its shards and decode (L1c).
Generated by `scripts/spin_orbit/csplit_emit.py`. Do not edit.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit
open KAM.SpinOrbit.Data CertArith

















theorem lockM2006_shards_cover :
    ∀ s ∈ advLow.p1072.ii.shardRange, ∃ g ∈ [[0, 1, 2, 3], [4, 5]], s ∈ g := by
  decide +kernel

theorem lockM2006_shards_groups :
    ∀ g ∈ [[0, 1, 2, 3], [4, 5]], g.all (checkShardAt advLow.p1072.ii (advLow.p1072.ii.la.slotTerms
      (((lockM2006a.toMants base.cfgLow.toMant 112).getD ([], [])).2))
      (advLow.p1072.ii.lb.slotTerms (((lockM2006b.toMants base.cfgLow.toMant 112).getD ([],
      [])).2))) = true :=
  (List.forall_mem_cons.2 ⟨lockM2006_shardsG0, (List.forall_mem_cons.2 ⟨lockM2006_shardsG1, (fun _
    h => nomatch h)⟩)⟩)

theorem lockM2006_sp :
    checkPackedSp advLow.p1072.ii (advLow.p1072.ii.la.slotTerms (((lockM2006a.toMants
      base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1072.ii.lb.slotTerms
      (((lockM2006b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) = true :=
  checkPackedSp_of_groups advLow.p1072.ii (advLow.p1072.ii.la.slotTerms (((lockM2006a.toMants
        base.cfgLow.toMant 112).getD ([], [])).2)) (advLow.p1072.ii.lb.slotTerms
        (((lockM2006b.toMants base.cfgLow.toMant 112).getD ([], [])).2)) [[0, 1, 2, 3], [4, 5]]
        lockM2006A7 lockM2006_shards_cover lockM2006_shards_groups









/-- The advice entry of the product, at its chunk position (a shallow `rfl`). -/
theorem lockM2006_advAt :
    advLow.b5[72]? = some ([4, 8, 1, 1, 0], (.packed 112 advLow.p1072.rr advLow.p1072.ii
      advLow.p1072.ri advLow.p1072.ir))
    := rfl

/-- The packed product 2006 (cfgLow, key [4, 8, 1, 1, 0]). -/
theorem lockM2006 :
    CertModel.polyProduct base.weight base.cfgLow ([4, 8] ++ [1, 1, 0]) ((modelMatrixEntry
      (modelMatTranspose (2 + 2) 2 (modelMatOmega 2 2 lockN0)) 1 0).poly) ((modelMatrixEntry
      (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 lockXN1 (modelMatNeg (2 + 2)
      2 (modelMatOmega 2 2 (modelMatAdd base.weight base.piEnc (2 + 2) 2 lockDN1 lockDN2))))) 0
      1).poly) = some (((⟨[] ++ lockM2006T ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 +
      ((([lockM2006II_remN0, lockM2006II_remN1].sum : ℕ) : ℚ) / ((base.weight.w.den ^ 114 * 2 ^ (2
      * 112) : ℕ) : ℚ)) + 0 + 0) : LockBackend)).1.toErrTerms, ((⟨[] ++ lockM2006T ++ [] ++ []⟩ :
      CertPoly LockBackend), (ofRatUp (0 + ((([lockM2006II_remN0, lockM2006II_remN1].sum : ℕ) : ℚ)
      / ((base.weight.w.den ^ 114 * 2 ^ (2 * 112) : ℕ) : ℚ)) + 0 + 0) : LockBackend)).2) := by
  rw [← lockM2006II_rb, lockM2006b_eq, lockM2006a_eq]
  exact polyProduct_eq_of_mulPacked base.weight base.cfgLow ([4, 8] ++ [1, 1, 0]) lockM2006a
      lockM2006b
      112 advLow.p1072.rr advLow.p1072.ii advLow.p1072.ri advLow.p1072.ir
      ((⟨[] ++ lockM2006T ++ [] ++ []⟩ : CertPoly LockBackend), (ofRatUp (0 +
        advLow.p1072.ii.remainderBound base.weight (2 * 112) + 0 + 0) : LockBackend))
      lockM2006A8 lockM2006A9 ((congrArg (fun b => adviceLookup b ([4, 8] ++ [1, 1, 0]))
          lock_advLow_blocks).trans ((adviceLookup_skip_cseg advLow.b0 _ ([4, 8] ++ [1, 1, 0]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b1 _ ([4, 8] ++ [1, 1, 0]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b2 _ ([4, 8] ++ [1, 1, 0]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b3 _ ([4, 8] ++ [1, 1, 0]) (by
          decide +kernel)).trans ((adviceLookup_skip_cseg advLow.b4 _ ([4, 8] ++ [1, 1, 0]) (by
          decide +kernel)).trans (adviceLookup_at_cseg advLow.b5 _ ([4, 8] ++ [1, 1, 0]) 72 [4, 8,
          1, 1, 0] (.packed 112 advLow.p1072.rr advLow.p1072.ii advLow.p1072.ri advLow.p1072.ir) (by
          decide +kernel) lockM2006_advAt (by decide +kernel))))))))
      (CertPoly.mulPacked_eq_of_parts base.cfgLow.toMant base.weight 112 advLow.p1072.rr
        advLow.p1072.ii advLow.p1072.ri advLow.p1072.ir lockM2006a lockM2006b
        (ma := ((lockM2006a.toMants base.cfgLow.toMant 112).getD ([], [])))
        (mb := ((lockM2006b.toMants base.cfgLow.toMant 112).getD ([], [])))
        (pRR := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (pII := (advLow.p1072.ii.targetTerms, advLow.p1072.ii.remainderBound base.weight (2 * 112)))
        (pRI := (([] : List (CertKey × ℤ)), (0 : ℚ))) (pIR := (([] : List (CertKey × ℤ)), (0 : ℚ)))
        (tRR := ([] : List (CertKey × CC LockBackend))) (tII := lockM2006T)
        (tRI := ([] : List (CertKey × CC LockBackend)))
        (tIR := ([] : List (CertKey × CC LockBackend)))
        (eq_some_getD_cseg ([], []) lockM2006A10)
        (eq_some_getD_cseg ([], []) lockM2006A11)
        (packedRealProduct_eq_nil_left advLow.p1072.rr base.weight (2 * 112) (((lockM2006b.toMants
          base.cfgLow.toMant 112).getD ([], [])).1) lockM2006A0)
        (packedRealProduct_eq_of_sparse advLow.p1072.ii base.weight (2 * 112) (((lockM2006a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) (((lockM2006b.toMants base.cfgLow.toMant
          112).getD ([], [])).2) lockM2006A1 lockM2006A2 lockM2006A3 lockM2006A4 lockM2006_sp)
        (packedRealProduct_eq_nil_left advLow.p1072.ri base.weight (2 * 112) (((lockM2006b.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM2006A5)
        (packedRealProduct_eq_nil_right advLow.p1072.ir base.weight (2 * 112) (((lockM2006a.toMants
          base.cfgLow.toMant 112).getD ([], [])).2) lockM2006A6)
        (dyadicTerms_nil_cseg _ _ _)
        lockM2006_dec
        (dyadicTerms_nil_cseg _ _ _)
        (dyadicTerms_nil_cseg _ _ _))

end KAM.SpinOrbit.Data.LockN65
