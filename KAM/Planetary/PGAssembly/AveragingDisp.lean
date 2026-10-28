/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingHamil

/-!
# P Part 5: chart, remainder regularity and displacement bounds (`stepP:p5:av-disp`)

The real trace of the conjugated P2 map is a chart (`hol_chart`), the conjugated remainder is
holomorphic, and the four P2 displacement estimates become the stated physical bounds
(constants `12` and `18`, each with a factor-two slack).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ} {Ψ : CPhase (a+b) → CPhase (a+b)}
  {R : CHam (a+b)}

theorem avg_rem_diff (h : admissible d (pgRstar d) r mu)
    (hcls : oscClass (checkedCore d r mu) ((params d r mu).rhoBar/2) (pgOscEpsilon d/2)
      (pgOscEpsilon d/2) (pgOscWidth d/6) R) :
    DifferentiableOn ℂ (avgRem R) (averagingDomain d r mu) := by
  have : DifferentiableOn ℂ (R ∘ pgOscUnnormalize) (averagingDomain d r mu) :=
    hcls.1.comp differentiable_pgOscUnnormalize.differentiableOn
      (fun z hz => (mem_averagingDomain_iff h).1 hz)
  exact this.const_mul _

theorem avg_chart (h : admissible d (pgRstar d) r mu)
    (hΨ : DifferentiableOn ℂ Ψ (avgV d r mu))
    (hs : ∀ z ∈ avgV d r mu, ∀ u v, KAM.Canonical.symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) =
      KAM.Canonical.symplFormC u v)
    (hr : ∀ x : Phase (a+b), KAM.realInclusion₂ (a+b) x ∈ avgV d r mu →
      Ψ (KAM.realInclusion₂ (a+b) x) ∈ range (KAM.realInclusion₂ (a+b))) :
    IsChart 1 (realAverageMap (⟨avgPsi Ψ, avgRem R⟩ : PGAveraging (a+b)))
      ((KAM.realInclusion₂ (a+b)) ⁻¹' averagingDomain d r mu) := by
  have hr' := avg_real_mem h hr
  have := hol_chart (c := 1) one_pos (isOpen_averagingDomain h) (avg_diff h hΨ)
    (fun z hz u v => by
      have := avg_sympl h hΨ hs (KAM.realInclusion₂ (a+b) z) hz u v
      exact this)
    (Ψr := realAverageMap (⟨avgPsi Ψ, avgRem R⟩ : PGAveraging (a+b)))
    (fun z hz => (realAverageMap_spec (A := (⟨avgPsi Ψ, avgRem R⟩ : PGAveraging (a+b)))
      (hr' z hz)).symm)
  exact this.2.1

theorem avg_disp (h : admissible d (pgRstar d) r mu)
    (hr : ∀ x : Phase (a+b), KAM.realInclusion₂ (a+b) x ∈ avgV d r mu →
      Ψ (KAM.realInclusion₂ (a+b) x) ∈ range (KAM.realInclusion₂ (a+b)))
    (hd : ∀ z ∈ avgV d r mu,
      2 * Real.pi * pgOscAlpha d r mu * pgOscWidth d *
        ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 * pgOscE d mu ∧
      2 * Real.pi * pgOscAlpha d r mu * pgOscEpsilon d *
        ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 9 * pgOscE d mu ∧
      2 * Real.pi * pgOscAlpha d r mu * pgOscEpsilon d *
        ‖lastBlock (a := a) ((Ψ z).1 - z.1)‖ ≤ 9 * pgOscE d mu) :
    ∀ z : Phase (a+b), KAM.realInclusion₂ (a+b) z ∈ averagingDomain d r mu →
      ‖blockFast (realAverageMap (⟨avgPsi Ψ, avgRem R⟩ : PGAveraging (a+b)) z).2 -
          blockFast z.2‖ ≤
        12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
          (pgWidth d*(params d r mu).gammaBar) ∧
      ‖(blockSlow (realAverageMap (⟨avgPsi Ψ, avgRem R⟩ : PGAveraging (a+b)) z).2 -
          blockSlow z.2,
        blockSlow (realAverageMap (⟨avgPsi Ψ, avgRem R⟩ : PGAveraging (a+b)) z).1 -
          blockSlow z.1)‖ ≤
        18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
          (pgOscRadius d*(params d r mu).gammaBar) := by
  intro z hz
  have hpi := Real.pi_pos
  have hs := sqrt_two_pi_pos
  have hs2 : Real.sqrt (2*Real.pi) ^ 2 = 2*Real.pi := Real.sq_sqrt (by positivity)
  have hw := pgWidth_pos d
  have hrad := pgOscRadius_pos d
  have hγ := av_gamma_pos h
  have hT := Real.rpow_pos_of_pos (av_Kbar_pos h) (pgTau a b)
  have hE := (pg_osc_positive d r mu h).2
  have hLP := pgAnalytic_LP_ge_one d
  have hmu := h.2.2.1
  have hy := (mem_averagingDomain_iff h).1 hz
  have hy' := hy
  rw [pgOscUnnormalize_real] at hy'
  obtain ⟨w, hw'⟩ := hr _ hy'
  have hW := realAverageMap_spec (A := (⟨avgPsi Ψ, avgRem R⟩ : PGAveraging (a+b)))
    (avg_real_mem h hr z hz)
  set W := realAverageMap (⟨avgPsi Ψ, avgRem R⟩ : PGAveraging (a+b)) z with hWdef
  have hW' : pgOscNormalize (Ψ (pgOscUnnormalize (KAM.realInclusion₂ (a+b) z))) =
      KAM.realInclusion₂ (a+b) W := hW
  set y := pgOscUnnormalize (KAM.realInclusion₂ (a+b) z) with hydef
  obtain ⟨d1, d2, d3⟩ := hd y hy
  have hs' : (Real.sqrt (2*Real.pi):ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have ey2 : blockSlow (KAM.realInclusion₂ (a+b) z).2 =
      (Real.sqrt (2*Real.pi):ℂ) • blockSlow y.2 := by
    rw [hydef, blockSlow_unnormalize_snd, smul_smul, mul_inv_cancel₀ hs', one_smul]
  have ey1 : blockSlow (KAM.realInclusion₂ (a+b) z).1 =
      (Real.sqrt (2*Real.pi):ℂ) • blockSlow y.1 := by
    rw [hydef, blockSlow_unnormalize_fst, smul_smul, mul_inv_cancel₀ hs', one_smul]
  have ef2 : blockFast (KAM.realInclusion₂ (a+b) z).2 = blockFast y.2 := by
    rw [hydef, blockFast_unnormalize_snd]
  have hn1 := congrArg (fun v => blockFast v.2) hW'
  have hn2 := congrArg (fun v => blockSlow v.2) hW'
  have hn3 := congrArg (fun v => blockSlow v.1) hW'
  simp only [blockFast_normalize_snd, blockSlow_normalize_snd, blockSlow_normalize_fst]
    at hn1 hn2 hn3
  have f1 : KAM.realInclusion a (blockFast W.2 - blockFast z.2) =
      firstBlock (b := b) ((Ψ y).2 - y.2) := by
    funext i
    have := congrFun hn1 i
    have e := congrFun ef2 i
    simp only [blockFast, KAM.realInclusion₂_apply, KAM.realInclusion_apply] at this e ⊢
    simp only [firstBlock, blockFast, Pi.sub_apply] at *
    push_cast
    rw [← this, ← e]
  have f2 : KAM.realInclusion b (blockSlow W.2 - blockSlow z.2) =
      (Real.sqrt (2*Real.pi):ℂ) • lastBlock (a := a) ((Ψ y).2 - y.2) := by
    funext i
    have := congrFun hn2 i
    have e := congrFun ey2 i
    simp only [blockSlow, KAM.realInclusion₂_apply, KAM.realInclusion_apply, Pi.smul_apply,
      smul_eq_mul] at this e ⊢
    simp only [lastBlock, blockSlow, Pi.sub_apply] at *
    push_cast
    rw [← this, e]; ring
  have f3 : KAM.realInclusion b (blockSlow W.1 - blockSlow z.1) =
      (Real.sqrt (2*Real.pi):ℂ) • lastBlock (a := a) ((Ψ y).1 - y.1) := by
    funext i
    have := congrFun hn3 i
    have e := congrFun ey1 i
    simp only [blockSlow, KAM.realInclusion₂_apply, KAM.realInclusion_apply, Pi.smul_apply,
      smul_eq_mul] at this e ⊢
    simp only [lastBlock, blockSlow, Pi.sub_apply] at *
    push_cast
    rw [← this, e]; ring
  have n1 : ‖blockFast W.2 - blockFast z.2‖ = ‖firstBlock (b := b) ((Ψ y).2 - y.2)‖ := by
    rw [← f1, KAM.norm_realInclusion]
  have n2 : ‖blockSlow W.2 - blockSlow z.2‖ =
      Real.sqrt (2*Real.pi) * ‖lastBlock (a := a) ((Ψ y).2 - y.2)‖ := by
    rw [← KAM.norm_realInclusion, f2, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs]
  have n3 : ‖blockSlow W.1 - blockSlow z.1‖ =
      Real.sqrt (2*Real.pi) * ‖lastBlock (a := a) ((Ψ y).1 - y.1)‖ := by
    rw [← KAM.norm_realInclusion, f3, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs]
  set K := (params d r mu).Kbar ^ (pgTau a b) with hK
  set γ := (params d r mu).gammaBar with hγdef
  have hLPmu : 0 ≤ (pgAnalytic d).LP * mu := by positivity
  have hα : pgOscAlpha d r mu = γ / (4*Real.pi*K) := rfl
  refine ⟨?_, ?_⟩
  · rw [n1, le_div_iff₀ (by positivity)]
    have e : ‖firstBlock (b := b) ((Ψ y).2 - y.2)‖ * (pgWidth d * γ) =
        (2 * Real.pi * pgOscAlpha d r mu * pgOscWidth d *
          ‖firstBlock (b := b) ((Ψ y).2 - y.2)‖) * (4*Real.pi*K) := by
      rw [hα]; unfold pgOscWidth; field_simp
    rw [e]
    have : (2 * Real.pi * pgOscAlpha d r mu * pgOscWidth d *
          ‖firstBlock (b := b) ((Ψ y).2 - y.2)‖) * (4*Real.pi*K) ≤
        (3 * pgOscE d mu) * (4*Real.pi*K) :=
      mul_le_mul_of_nonneg_right d1 (by positivity)
    refine this.trans ?_
    unfold pgOscE
    have : (3 * ((pgAnalytic d).LP * mu / (2 * Real.pi))) * (4*Real.pi*K) =
        6 * ((pgAnalytic d).LP * mu * K) := by field_simp; ring
    rw [this]
    have : 0 ≤ (pgAnalytic d).LP * mu * K := by positivity
    linarith
  · have hmax : ∀ x y c : ℝ, x ≤ c → y ≤ c → max x y ≤ c := fun x y c => max_le
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [n2, le_div_iff₀ (by positivity)]
      have e : Real.sqrt (2*Real.pi) * ‖lastBlock (a := a) ((Ψ y).2 - y.2)‖ *
          (pgOscRadius d * γ) = (2 * Real.pi * pgOscAlpha d r mu * pgOscEpsilon d *
          ‖lastBlock (a := a) ((Ψ y).2 - y.2)‖) * (4*Real.pi*K) := by
        rw [hα]; unfold pgOscEpsilon; field_simp
        rw [hs2]
      rw [e]
      refine (mul_le_mul_of_nonneg_right d2 (by positivity)).trans ?_
      unfold pgOscE
      have : (9 * ((pgAnalytic d).LP * mu / (2 * Real.pi))) * (4*Real.pi*K) =
          18 * ((pgAnalytic d).LP * mu * K) := by field_simp; ring
      rw [this]; linarith
    · rw [n3, le_div_iff₀ (by positivity)]
      have e : Real.sqrt (2*Real.pi) * ‖lastBlock (a := a) ((Ψ y).1 - y.1)‖ *
          (pgOscRadius d * γ) = (2 * Real.pi * pgOscAlpha d r mu * pgOscEpsilon d *
          ‖lastBlock (a := a) ((Ψ y).1 - y.1)‖) * (4*Real.pi*K) := by
        rw [hα]; unfold pgOscEpsilon; field_simp
        rw [hs2]
      rw [e]
      refine (mul_le_mul_of_nonneg_right d3 (by positivity)).trans ?_
      unfold pgOscE
      have : (9 * ((pgAnalytic d).LP * mu / (2 * Real.pi))) * (4*Real.pi*K) =
          18 * ((pgAnalytic d).LP * mu * K) := by field_simp; ring
      rw [this]; linarith

end KAM.Planetary

end
