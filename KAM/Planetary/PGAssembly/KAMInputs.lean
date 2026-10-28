/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.KAMInputsBase
public import KAM.Planetary.PGAssembly.KAMInputsFreq
public import KAM.Planetary.PGAssembly.KAMInputsKamH
public import KAM.Planetary.PGAssembly.KAMInputsF
public import KAM.Planetary.PGAssembly.KAMInputsPer

/-!
# P Part 5: the KAM hypothesis inputs (`bpP:p5:kam-hyp`)

`kam_hyp` collects the local estimates (weighted class and bound of `kamF`, holomorphy,
injectivity, reality and Hessian bounds of `kamH`), `pg_kam_hyp` assembles the P3 record `KamHyp`
for the exact scale record `pgKamScale`, and `pg_kam_dictionary` identifies its constants with
`params` and `pgD0`. Definitions and lemmas live in the `KAMInputs{Base,Freq,KamH,F,Per}` modules.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-KH.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {a b : ℕ} {d : PGData a b} {r mu : ℝ}

theorem kh_mem_dom {D : Set (Fin (a+b) → ℝ)} {rho S : ℝ} {z : PGComplexPhase (a+b)} :
    z ∈ KAM.Weighted.Dom (a+b) (KAM.realInclusion (a+b) '' D) rho S ↔
      z.1 ∈ KAM.complexStrip (a+b) S ∧ z.2 ∈ KAM.actionNbhd D rho := by
  rw [KAM.Weighted.actionNbhd_eq_polyNbhd]
  exact Iff.rfl

theorem kh_realNbhd_of_mem {D : Set (Fin (a+b) → ℝ)} {rho σ : ℝ} {x : Phase (a+b)}
    (hx : KAM.realInclusion₂ (a+b) x ∈ coefficientDom D rho σ) : x.2 ∈ realNbhd D rho := by
  have := (kh_mem_dom.1 hx).2
  obtain ⟨y, hy, hlt⟩ := mem_actionNbhd_iff.1 this
  refine ⟨y, hy, ?_⟩
  rw [dist_eq_norm, ← KAM.norm_realInclusion, map_sub]
  exact hlt

theorem kamF_inClass (h : admissible d (pgRstar d) r mu) {S : ℝ}
    (hS : S ≤ pgWidth d/(12*Real.pi)) :
    KAM.Weighted.InClass (KAM.realInclusion (a+b) '' pgActionDomain d r mu)
      (params d r mu).rho S (kamF d r mu h) := by
  have hmem : ∀ z ∈ KAM.Weighted.Dom (a+b) (KAM.realInclusion (a+b) '' pgActionDomain d r mu)
      (params d r mu).rho S, z.1 ∈ KAM.complexStrip (a+b) (pgWidth d/(12*Real.pi)) ∧
        z.2 ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho := fun z hz =>
    ⟨fun i => lt_of_lt_of_le ((kh_mem_dom.1 hz).1 i) hS, (kh_mem_dom.1 hz).2⟩
  refine ⟨(kamF_differentiableOn h).mono hmem, fun j z hz => ?_⟩
  exact kamF_periodic h (hmem z hz).1 (hmem z hz).2 j

/-- Local estimates used to prove pg_kam_hyp for the exact delivered P3 record. -/
theorem kam_hyp (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    KAM.Weighted.InClass (KAM.realInclusion (a+b) '' pgActionDomain d r mu)
      (params d r mu).rho (pgWidth d/(24*Real.pi)) (kamF d r mu h) ∧
    KAM.Weighted.WBound (KAM.realInclusion (a+b) '' pgActionDomain d r mu)
      (params d r mu).rho (pgWidth d/(24*Real.pi)) (kamF d r mu h) (kam_c1 d*mu*r^5) ∧
    DifferentiableOn ℂ (kamH d mu) (KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) ∧
    InjOn (fun J i => fderiv ℂ (kamH d mu) J (Pi.single i 1))
      (KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) ∧
    (∀ z : Phase (a+b), z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rho →
      (kamH d mu (KAM.realInclusion (a+b) z.2)).im = 0 ∧
        (kamF d r mu h (KAM.realInclusion₂ (a+b) z)).im = 0) ∧
    ∀ J ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho,
      ∃ T : (Fin (a+b) → ℂ) ≃L[ℂ] (Fin (a+b) → ℂ),
        (∀ v i, T v i = fderiv ℂ (fun J i => fderiv ℂ (kamH d mu) J (Pi.single i 1)) J v i) ∧
        ‖T.toContinuousLinearMap‖ ≤ kam_c1 d ∧
        ‖T.symm.toContinuousLinearMap‖ ≤ kam_c1 d/mu ∧
        (∀ v, ‖blockSlow (T v)‖ ≤ kam_c1 d*mu*‖v‖) ∧
        (∀ v, ‖blockFast (T.symm v)‖ ≤ kam_c1 d*‖v‖) := by
  have hw := pgWidth_pos d
  have hpi := Real.pi_pos
  have hs0 : 0 < pgWidth d/(24*Real.pi) := by positivity
  have e2 : pgWidth d/(24*Real.pi) + pgWidth d/(24*Real.pi) = pgWidth d/(12*Real.pi) := by
    field_simp; ring
  have hle0 : pgWidth d/(24*Real.pi) ≤ pgWidth d/(12*Real.pi) := by
    rw [← e2]; linarith
  have hmu0 : 0 < mu := h.2.2.1
  refine ⟨kamF_inClass h hle0, ?_, kamH_differentiableOn h, kamH_injOn h, ?_,
    fun J hJ => kamH_hessian h hJ⟩
  · have hW := KAM.Weighted.wbound_of_sup_bound hs0 hs0 (kamF_inClass h e2.le)
      (M := (2^5*(pgAnalytic d).CQ + 2*(pgAnalytic d).LP)*mu*r^5/(2*Real.pi))
      (fun z hz => by
        have hz' := kh_mem_dom.1 hz
        rw [e2] at hz'
        exact kamF_sup h hz'.1 hz'.2)
    have e3 : Real.pi * (pgWidth d/(24*Real.pi)) = pgWidth d/24 := by field_simp
    rw [e3] at hW
    refine hW.mono le_rfl le_rfl ?_
    have hK : (2^5*(pgAnalytic d).CQ + 2*(pgAnalytic d).LP)*
        KAM.Weighted.coth (pgWidth d/24)^(a+b)/(2*Real.pi) ≤ kam_c1 d :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hr5 : 0 ≤ mu*r^5 := by have := h.1; positivity
    calc KAM.Weighted.coth (pgWidth d/24)^(a+b) *
          ((2^5*(pgAnalytic d).CQ + 2*(pgAnalytic d).LP)*mu*r^5/(2*Real.pi))
        = ((2^5*(pgAnalytic d).CQ + 2*(pgAnalytic d).LP)*
            KAM.Weighted.coth (pgWidth d/24)^(a+b)/(2*Real.pi))*(mu*r^5) := by ring
      _ ≤ kam_c1 d*(mu*r^5) := mul_le_mul_of_nonneg_right hK hr5
      _ = kam_c1 d*mu*r^5 := by ring
  · intro z hz
    obtain ⟨x, hx⟩ := kamH_real h hz
    exact ⟨by rw [hx]; exact Complex.ofReal_im x, kamF_real h hz⟩

theorem pg_kam_hyp (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    KamHyp (pgActionDomain d r mu) (pgWidth d/15) (pgKamScale d r mu)
      (kamH d mu) (kamF d r mu h) := by
  obtain ⟨hIn, hWB, hdiff, hinj, hreal, hhess⟩ := kam_hyp d r mu h
  have hw := pgWidth_pos d
  have hw2 := pgWidth_lt_half d
  have hpi := Real.pi_pos
  have hmu0 : 0 < mu := h.2.2.1
  have hmu1 := mu_lt_one_of_admissible h
  have hC := one_le_kam_c1 d
  have hC0 : 0 < kam_c1 d := by linarith
  have hr0 : 0 < r := h.1
  have hk0 := pgScales_k0_pos d
  have hl1 := (kh_dyn h).2.2.2.1
  have hgw : geometricWidth (pgWidth d/15 + pgWidth d/60) = pgWidth d/(24*Real.pi) := by
    unfold geometricWidth; field_simp; ring
  have hg1 : (params d r mu).gamma1 = (pgScales d).k0*r^(5/2:ℝ) := rfl
  have hg2 : (params d r mu).gamma2 = mu*(pgScales d).k0*r^(5/2:ℝ) := rfl
  have hrp : 0 < r^(5/2:ℝ) := Real.rpow_pos_of_pos hr0 _
  refine ⟨d.ha, d.hb, ?_, ?_, ?_, ?_, ?_, ?_, hdiff, ?_, ?_, ?_, ?_, hinj, ?_, ?_⟩
  · show ((a+b:ℕ):ℝ) < pgTau a b
    unfold pgTau; linarith
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show 0 < (params d r mu).gamma2
      rw [hg2]; positivity
    · show 0 < pgWidth d/60; positivity
    · show 0 < (params d r mu).rho
      show 0 < (params d r mu).l1/2; linarith
    · show 0 < kam_c1 d*mu*r^5; positivity
    · exact hC0
    · show 0 < kam_c1 d*mu; positivity
    · show 0 < kam_c1 d/mu; positivity
    · exact hC0
    · show 0 < kam_c1 d/mu; positivity
  · show (params d r mu).gamma2 ≤ (params d r mu).gamma1
    rw [hg1, hg2]
    have : 0 < (pgScales d).k0*r^(5/2:ℝ) := by positivity
    nlinarith
  · refine ⟨?_, ?_⟩
    · show 4*(pgWidth d/60) ≤ pgWidth d/15; linarith
    · show pgWidth d/15 < 1; linarith
  · refine ⟨?_, ?_, le_rfl⟩
    · show kam_c1 d*mu ≤ kam_c1 d; nlinarith
    · show kam_c1 d ≤ kam_c1 d/mu
      rw [le_div_iff₀ hmu0]; nlinarith
  · exact le_rfl
  · intro x hx
    obtain ⟨y, hy⟩ := kamH_real h (kh_realNbhd_of_mem hx)
    show (kamH d mu (KAM.realInclusion (a+b) x.2)).im = 0
    rw [hy]; exact Complex.ofReal_im y
  · intro x hx
    exact kamF_real h (kh_realNbhd_of_mem hx)
  · show KAM.Weighted.InClass _ _ (geometricWidth (pgWidth d/15 + pgWidth d/60)) _
    rw [hgw]; exact hIn
  · show KAM.Weighted.WBound _ _ (geometricWidth (pgWidth d/15 + pgWidth d/60)) _ _
    rw [hgw]; exact hWB
  · intro I hI
    obtain ⟨T, hT, h1, h2, h3, h4⟩ := hhess I hI
    have hTe : (T : (Fin (a+b) → ℂ) →L[ℂ] (Fin (a+b) → ℂ)) =
        fderiv ℂ (KAM.NormalForm.freq (kamH d mu)) I :=
      ContinuousLinearMap.ext fun v => funext fun i => hT v i
    refine ⟨?_, ?_, T, hTe, h2, ?_, ?_⟩
    · rw [← hTe]; exact h1
    · intro v
      rw [← hTe]
      exact h3 v
    · intro v
      exact h4 v
    · intro v
      refine (pi_norm_le_iff_of_nonneg
        (mul_nonneg (div_nonneg hC0.le hmu0.le) (norm_nonneg _))).2 fun i => ?_
      refine (norm_le_pi_norm (T.symm v) _).trans ?_
      have := T.symm.toContinuousLinearMap.le_opNorm v
      exact this.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
  · have : kamConstant (a+b) (pgKamScale d r mu).τ = pgChat a b := rfl
    rw [this, pgKamScale_eHat h]
    exact (kh_dyn h).2.2.2.2.2.2.2.2

theorem pg_kam_dictionary (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    (pgKamScale d r mu).L = kam_c1 d/mu ∧
    rhoHat (pgKamScale d r mu) = (params d r mu).rhoHat ∧
    eHat (pgKamScale d r mu) = (params d r mu).Ehat ∧
    dioBase (pgActionDomain d r mu) (kamH d mu) (pgKamScale d r mu) = pgD0 d r mu := by
  refine ⟨pgKamScale_L h, pgKamScale_rhoHat h, pgKamScale_eHat h, ?_⟩
  ext J
  constructor
  · rintro ⟨hJ, hm⟩
    refine ⟨hJ, ?_⟩
    have := hm
    rw [mem_preimage, realFreq_kamH d (mu_mem_Icc h) hJ.1.1.1] at this
    exact this
  · rintro ⟨hJ, hm⟩
    refine ⟨hJ, ?_⟩
    rw [mem_preimage, realFreq_kamH d (mu_mem_Icc h) hJ.1.1.1]
    exact hm

end KAM.Planetary

end
