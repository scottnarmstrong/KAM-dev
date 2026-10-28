/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ChartDefs

/-!
# P Part 5: the chart `phi`, domain lemmas (`bpP:p5:phi-chart`)

Parameter facts, openness of `phiDomain`, lattice invariance of the polar chart and the fact that
the polar chart maps `phiDomain` into the real trace of the averaging domain.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-CH.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ} {d : PGData a b} {r mu : ℝ}

/-- The dynamic parameter facts of `rstar` used by the chart. -/
theorem chart_dyn (h : admissible d (pgRstar d) r mu) :
    r < pgOscRadius d/4 ∧
    (params d r mu).rK + 12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
      (pgWidth d*(params d r mu).gammaBar) < Real.sqrt r ∧
    Real.sqrt 2 * (18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
      (pgOscRadius d*(params d r mu).gammaBar)) ≤ (pgScales d).k1*r^(3/2:ℝ) ∧
    0 < (params d r mu).l1 ∧ (params d r mu).rK < min (Real.sqrt r) (params d r mu).l1 ∧
    (params d r mu).rK < (params d r mu).rhoBar/2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdyn⟩ := (rstar d).choose_spec
  obtain ⟨-, h2, -, -, h5, h6, h7, -, -, -, -, -, h13, h14, -, -⟩ := hdyn r mu h
  exact ⟨h2, h5, h6, h7, h13, h14⟩

theorem chart_rK_lt_half (h : admissible d (pgRstar d) r mu) :
    (params d r mu).rK < (params d r mu).l1/2 := by
  obtain ⟨-, -, -, hl1, -, -⟩ := chart_dyn h
  have h1 := (r_k d r mu h).1
  have h2 : (params d r mu).rhoHat ≤ (params d r mu).l1/2 := by
    rw [params_rhoHat, params_l1]; exact min_le_right _ _
  have hp : 0 < (params d r mu).rhoHat := params_rhoHat_pos d h.1 mu
  rcases Nat.eq_zero_or_pos (a+b) with h0 | h0
  · rw [h0] at h1
    simp at h1
    linarith
  · have hN : (1:ℝ) ≤ 256*((a+b:ℕ):ℝ) := by
      have : (1:ℝ) ≤ ((a+b:ℕ):ℝ) := by exact_mod_cast h0
      linarith
    have : (params d r mu).rhoHat/(256*((a+b:ℕ):ℝ)) ≤ (params d r mu).rhoHat :=
      div_le_self hp.le hN
    linarith

theorem params_l2_eq (d : PGData a b) (r mu : ℝ) : (params d r mu).l2 = r^2/2 := rfl

theorem isOpen_phiDomain : IsOpen (phiDomain d r mu) := by
  refine IsOpen.inter ?_ ?_
  · exact (isOpen_actionNbhd _ _).preimage ((KAM.realInclusion a).continuous.comp
      (continuous_pi fun i => (continuous_apply _).comp continuous_snd))
  · refine (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage ?_
    exact continuous_pi fun j => (continuous_apply _).comp continuous_snd

theorem phiDomain_slow {z : Phase (a+b)} (hz : z ∈ phiDomain d r mu) (j : Fin b) :
    (params d r mu).l1/2 < blockSlow z.2 j ∧ blockSlow z.2 j < r^2 := by
  have := hz.2 j (mem_univ j)
  rw [params_l2_eq] at this
  exact ⟨this.1, by linarith [this.2]⟩

theorem oscillatorPolar_fullShift (z : Phase (a+b)) (k : Fin (a+b) → ℤ) :
    oscillatorPolar (z + fullShift k) = oscillatorPolar z + fastShift (blockFast k) := by
  refine phase_ext_blocks (fun i => ?_) (fun i => ?_) (fun j => ?_) (fun j => ?_)
  · simp [fullShift, fastShift, blockFast, Fin.append_left]
  · simp [fullShift, fastShift]
  · simp [fullShift, fastShift]
    left; rw [mul_comm (2*Real.pi)]; exact Real.sin_add_int_mul_two_pi _ _
  · simp [fullShift, fastShift]
    left; rw [mul_comm (2*Real.pi)]; exact Real.cos_add_int_mul_two_pi _ _

theorem polar_mem_averagingDomain (h : admissible d (pgRstar d) r mu) {z : Phase (a+b)}
    (hz : z ∈ phiDomain d r mu) :
    KAM.realInclusion₂ (a+b) (oscillatorPolar z) ∈ averagingDomain d r mu := by
  obtain ⟨hosc, -⟩ := chart_dyn h
  have hr0 : 0 < r := h.1
  have hw : 0 < pgWidth d := pgWidth_pos d
  refine ⟨?_, ?_, ?_⟩
  · have : blockFast (KAM.realInclusion₂ (a+b) (oscillatorPolar z)).2 =
        KAM.realInclusion a (blockFast z.2) := by
      funext i; simp [blockFast]
    rw [this]; exact hz.1
  · have : blockFast (KAM.realInclusion₂ (a+b) (oscillatorPolar z)).1 =
        KAM.realInclusion a (blockFast (oscillatorPolar z).1) := by
      funext i; simp [blockFast]
    rw [this]; exact KAM.realInclusion_mem_complexStrip (by positivity) _
  · have key : ∀ j : Fin b, Real.sqrt (2*blockSlow z.2 j) < pgOscRadius d/2 := fun j => by
      have := (phiDomain_slow hz j).2
      have h0 : 0 < pgOscRadius d := pgOscRadius_pos d
      rw [Real.sqrt_lt' (by positivity)]
      nlinarith
    have hnorm : ∀ x : ℝ, ‖(x:ℂ)‖ = |x| := fun x => by simp
    rw [Prod.norm_def, max_lt_iff]
    constructor <;> refine (pi_norm_lt_iff (by have := pgOscRadius_pos d; positivity)).2 fun j => ?_
    · simp only [blockSlow, KAM.realInclusion₂_apply, KAM.realInclusion_apply,
        oscillatorPolar_snd_natAdd, hnorm, abs_mul]
      have := key j
      simp only [blockSlow] at this
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_cos_le_one _)).trans_lt this
    · simp only [blockSlow, KAM.realInclusion₂_apply, KAM.realInclusion_apply,
        oscillatorPolar_fst_natAdd, hnorm, abs_mul]
      have := key j
      simp only [blockSlow] at this
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_sin_le_one _)).trans_lt this

end KAM.Planetary

end
