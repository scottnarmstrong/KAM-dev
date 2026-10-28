/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingSmall
public import KAM.Planetary.PGAssembly.AveragingReal

/-!
# P Part 5: the source hypotheses of oscillator averaging (`bpP:p5:avg`)

`pg_osc_hyp` assembles the record `OscHyp` for the normalized data: holomorphy, periodicity and
reality of `pgOscE • pgOscP` on the P2 domain, its weighted bound, the divisor and smallness
conditions.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

theorem strip_mono {N : ℕ} {S S' : ℝ} (h : S ≤ S') {θ : Fin N → ℂ}
    (hθ : θ ∈ KAM.complexStrip N S) : θ ∈ KAM.complexStrip N S' :=
  fun i => (hθ i).trans_le h

theorem normalize_eq_assemble (z : CPhase (a+b)) :
    pgOscNormalize z = assembleComplex (blockFast z.2) ((2*Real.pi:ℂ) • blockFast z.1)
      ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2) ((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1) :=
  rfl

theorem normalize_mem_extensionDomain (h : admissible d (pgRstar d) r mu) {s' S : ℝ}
    (hs' : s' ≤ (pgExtension d).delta/2) (hS : S ≤ pgOscWidth d) {z : CPhase (a+b)}
    (hz : z ∈ oscDom (checkedCore d r mu) s' (pgOscEpsilon d) (pgOscEpsilon d) S) :
    pgOscNormalize z ∈ extensionDomain d (pgExtension d).delta := by
  obtain ⟨z1, z2, z3, z4⟩ := mem_oscDom_pg.1 hz
  have hs := sqrt_two_pi_pos
  have hpi := Real.pi_pos
  have hδ := (pgExtension d).delta_pos
  rw [normalize_eq_assemble]
  have hI : blockFast z.2 ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2) := by
    obtain ⟨J, hJ, hIJ⟩ := z2
    exact ⟨J, subset_closure (checkedCore_subset_V d r mu hJ), hIJ.trans_le hs'⟩
  have hε : ∀ v : Fin b → ℂ, ‖v‖ < pgOscEpsilon d →
      ‖(Real.sqrt (2*Real.pi):ℂ) • v‖ < (pgExtension d).delta/4 := by
    intro v hv
    rw [norm_real_smul_lt_iff hs]
    refine hv.trans_le ?_
    unfold pgOscEpsilon
    exact div_le_div_of_nonneg_right (pgOscRadius_le_delta d) hs.le
  have hx : ‖((Real.sqrt (2*Real.pi):ℂ) • blockSlow z.1, (Real.sqrt (2*Real.pi):ℂ) • blockSlow z.2)‖ <
      (pgExtension d).delta/4 := by
    rw [Prod.norm_def]; exact max_lt (hε _ z4) (hε _ z3)
  refine strip_mem_extensionDomain d hδ hI hx (strip_mono ?_ z1)
  unfold pgOscWidth at hS
  have : pgWidth d/(2*Real.pi) ≤ (pgExtension d).delta/(2*Real.pi) :=
    div_le_div_of_nonneg_right (by rw [pgWidth_eq]; linarith) (by positivity)
  exact hS.trans this

theorem pgOscNormalize_real (x : Phase (a+b)) :
    pgOscNormalize (KAM.realInclusion₂ (a+b) x) = KAM.realInclusion₂ (a+b)
      (Fin.append ((2*Real.pi) • blockFast x.1) ((Real.sqrt (2*Real.pi)) • blockSlow x.1),
       Fin.append (blockFast x.2) ((Real.sqrt (2*Real.pi)) • blockSlow x.2)) := by
  refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [pgOscNormalize, blockFast, blockSlow]

theorem natAdd_ne_castAdd (k : Fin b) (j : Fin a) : Fin.natAdd a k ≠ Fin.castAdd b j := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := j.isLt
  simp at h1
  omega

theorem pgOscNormalize_shift (z : CPhase (a+b)) (j : Fin a) :
    pgOscNormalize (z.1 + Pi.single (Fin.castAdd b j) 1, z.2) =
      pgOscNormalize z + KAM.realInclusion₂ (a+b) (fastShift (Pi.single j (1:ℤ))) := by
  have hna := natAdd_ne_castAdd (a := a) (b := b)
  refine Prod.ext ?_ ?_ <;> funext i <;> refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · by_cases hk : k = j
    · subst hk
      simp [pgOscNormalize, blockFast, blockSlow, fastShift]
      ring
    · simp [pgOscNormalize, blockFast, blockSlow, fastShift, hk, Pi.single_apply,
        Fin.castAdd_inj]
  · simp [pgOscNormalize, blockFast, blockSlow, fastShift, Pi.single_apply, hna k j]
  · simp [pgOscNormalize, blockFast, blockSlow, fastShift]
  · simp [pgOscNormalize, blockFast, blockSlow, fastShift]

theorem oscFunction_smul {m : ℕ} (E : ℝ) (P : CHam (a + m)) :
    oscFunction (E • P) = fun y => (E:ℂ) * oscFunction P y := by
  funext y; simp [oscFunction, Complex.real_smul]

theorem pg_osc_bound_smul (h : admissible d (pgRstar d) r mu) :
    oscBound (checkedCore d r mu) (params d r mu).rhoBar (pgOscEpsilon d) (pgOscEpsilon d)
      (0 + pgOscWidth d) (pgOscE d mu • pgOscP d mu) (pgOscE d mu) := by
  rw [zero_add]
  intro x hx
  obtain ⟨hS, hle⟩ := pg_osc_bound d r mu h x hx
  have hE := (pg_osc_positive d r mu h).2.le
  have hc : ∀ k, ‖KAM.Weighted.coeff (oscFunction (pgOscE d mu • pgOscP d mu)) x k‖ *
      KAM.Weighted.modeWeight (pgOscWidth d) k =
      pgOscE d mu * (‖KAM.Weighted.coeff (oscFunction (pgOscP d mu)) x k‖ *
        KAM.Weighted.modeWeight (pgOscWidth d) k) := by
    intro k
    rw [oscFunction_smul, coeff_const_mul_flat', norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hE]
    ring
  refine ⟨?_, ?_⟩
  · unfold KAM.Weighted.WSummable
    simp_rw [hc]
    exact hS.mul_left _
  · unfold KAM.Weighted.wsum
    simp_rw [hc]
    rw [tsum_mul_left]
    calc pgOscE d mu * ∑' k, ‖KAM.Weighted.coeff (oscFunction (pgOscP d mu)) x k‖ *
          KAM.Weighted.modeWeight (pgOscWidth d) k ≤ pgOscE d mu * 1 :=
        mul_le_mul_of_nonneg_left hle hE
      _ = _ := mul_one _

theorem pg_osc_class (h : admissible d (pgRstar d) r mu) :
    oscClass (checkedCore d r mu) (params d r mu).rhoBar (pgOscEpsilon d) (pgOscEpsilon d)
      (0 + pgOscWidth d) (pgOscE d mu • pgOscP d mu) := by
  rw [zero_add]
  have hmu := av_mu_mem h
  have hmem : ∀ z ∈ oscDom (checkedCore d r mu) (params d r mu).rhoBar (pgOscEpsilon d)
      (pgOscEpsilon d) (pgOscWidth d), pgOscNormalize z ∈
        extensionDomain d (pgExtension d).delta := fun z hz =>
    normalize_mem_extensionDomain h (by linarith [av_rhoBar_lt_delta h, (pgExtension d).delta_pos])
      le_rfl hz
  refine ⟨?_, fun j z hz => ?_⟩
  · have h1 : DifferentiableOn ℂ (fun z => (pgExtension d).P mu (pgOscNormalize z) /
        ((pgAnalytic d).LP : ℂ)) (oscDom (checkedCore d r mu)
        (params d r mu).rhoBar (pgOscEpsilon d) (pgOscEpsilon d) (pgOscWidth d)) :=
      by
        have := (((pgExtension d).holo mu hmu).comp differentiable_pgOscNormalize.differentiableOn
          hmem).mul_const (((pgAnalytic d).LP : ℂ)⁻¹)
        simpa [div_eq_mul_inv] using this
    exact h1.const_smul (pgOscE d mu)
  · have hT := hmem z hz
    show (pgOscE d mu : ℝ) • pgOscP d mu _ = (pgOscE d mu : ℝ) • pgOscP d mu z
    simp only [pgOscP]
    rw [pgOscNormalize_shift, (pgExtension d).periodic mu hmu _ hT]

theorem pg_osc_real (h : admissible d (pgRstar d) r mu) :
    KAM.Canonical.RealOn (oscDom (checkedCore d r mu) (params d r mu).rhoBar (pgOscEpsilon d)
      (pgOscEpsilon d) (0 + pgOscWidth d)) (pgOscE d mu • pgOscP d mu) := by
  rw [zero_add]
  intro x hx
  have hmu := av_mu_mem h
  have hT := normalize_mem_extensionDomain h
    (by linarith [av_rhoBar_lt_delta h, (pgExtension d).delta_pos]) le_rfl hx
  rw [pgOscNormalize_real] at hT
  have hre := ext_P_real d hmu _ hT
  show ((pgOscE d mu : ℝ) • ((pgExtension d).P mu (pgOscNormalize (KAM.realInclusion₂ (a+b) x)) /
    (pgAnalytic d).LP)).im = 0
  rw [pgOscNormalize_real, Complex.smul_im, Complex.div_ofReal_im, hre]
  simp

theorem pg_osc_hyp (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    OscHyp (checkedCore d r mu) (params d r mu).rhoBar (pgOscEpsilon d) (pgOscEpsilon d)
      0 (pgOscWidth d) (15/(Real.pi*pgOscWidth d)*Real.log (1/r))
      (pgOscAlpha d r mu) (pgOscE d mu)
      (pgOscH d) (pgOscE d mu • pgOscP d mu) := by
  have hpi := Real.pi_pos
  have hmu := av_mu_mem h
  have hδ := (pgExtension d).delta_pos
  have hρδ := av_rhoBar_lt_delta h
  have hKpos : 0 < 15/(Real.pi*pgOscWidth d)*Real.log (1/r) := by
    rw [pgOsc_K_eq, ← params_Kbar]; exact av_Kbar_pos h
  have hmono : KAM.actionNbhd (checkedCore d r mu) (params d r mu).rhoBar ⊆
      KAM.actionNbhd (closure d.V) (pgExtension d).delta :=
    actionNbhd_checkedCore_le h (by linarith)
  refine ⟨d.ha, d.hb, ⟨av_rhoBar_pos h, ?_, ?_, ?_, hKpos, ?_⟩, le_rfl,
    (pg_osc_positive d r mu h).2.le, ?_, ?_, ?_, pg_osc_class h, pg_osc_bound_smul h,
    pg_osc_real h, pg_osc_divisor h, pg_osc_small h⟩
  · unfold pgOscEpsilon; have := pgOscRadius_pos d; positivity
  · unfold pgOscEpsilon; have := pgOscRadius_pos d; positivity
  · unfold pgOscWidth; have := pgWidth_pos d; positivity
  · unfold pgOscAlpha
    have := av_gamma_pos h
    have := Real.rpow_pos_of_pos (av_Kbar_pos h) (pgTau a b)
    positivity
  · rw [pgOsc_K_eq, ← params_Kbar d r mu]
    have : 2*Real.pi*(params d r mu).Kbar*pgOscWidth d = (params d r mu).Kbar*pgWidth d := by
      unfold pgOscWidth; field_simp
    rw [this]
    exact av_Kbar_mul_width h
  · show DifferentiableOn ℂ (fun I => (pgExtension d).H0 I / (2*Real.pi:ℂ)) _
    have := ((pgExtension d).h0holo.mono hmono).mul_const ((2*Real.pi:ℂ)⁻¹)
    simpa [div_eq_mul_inv] using this
  · intro I hI
    have hI' := hmono hI
    show ((pgExtension d).H0 (KAM.realInclusion a I) / (2*Real.pi:ℂ)).im = 0
    rw [(pgExtension d).h0real I hI']
    have : ((d.H0 I : ℝ) : ℂ) / (2*Real.pi:ℂ) = ((d.H0 I / (2*Real.pi) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_im]

end KAM.Planetary

end
