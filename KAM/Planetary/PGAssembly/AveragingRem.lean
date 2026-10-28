/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingMap
public import KAM.Planetary.Averaging.OscillatorBracket

/-!
# P Part 5: the remainder estimates of the averaging adapter (`stepP:p5:av-R1`)

The quadratic term of the P2 remainder bound is at most `L μ r^5` by the existing `G` condition
(`G² ≥ 1600 (1+b) M0 / w` and the first `gammaBar` branch), so the transformed remainder is at
most `2 L μ r^5` pointwise and in the weighted Fourier norm on the physical torus.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

/-- The P2 remainder constant. -/
def avgB (d : PGData a b) (r mu : ℝ) : ℝ :=
  400 * (1 + (b:ℝ)) * (pgOscE d mu) ^ 2 / (2 * Real.pi * pgOscAlpha d r mu *
    min ((params d r mu).rhoBar * pgOscWidth d) (pgOscEpsilon d ^ 2)) + pgOscE d mu * r ^ 5

theorem avgB_nonneg (h : admissible d (pgRstar d) r mu) : 0 ≤ avgB d r mu := by
  have hw : 0 < pgOscWidth d := by unfold pgOscWidth; have := pgWidth_pos d; positivity
  have he : 0 < pgOscEpsilon d := by unfold pgOscEpsilon; have := pgOscRadius_pos d; positivity
  have hρ := av_rhoBar_pos h
  have hα : 0 < pgOscAlpha d r mu := by
    unfold pgOscAlpha
    have := av_gamma_pos h
    have := Real.rpow_pos_of_pos (av_Kbar_pos h) (pgTau a b)
    have := Real.pi_pos
    positivity
  have hE := (pg_osc_positive d r mu h).2
  have hr := h.1
  unfold avgB
  have : 0 < min ((params d r mu).rhoBar * pgOscWidth d) (pgOscEpsilon d ^ 2) :=
    lt_min (by positivity) (by positivity)
  have := Real.pi_pos
  positivity

theorem pg_osc_min_eq (h : admissible d (pgRstar d) r mu) :
    min ((params d r mu).rhoBar * pgOscWidth d) (pgOscEpsilon d ^ 2) =
      (params d r mu).rhoBar * pgOscWidth d := by
  have hpi := Real.pi_pos
  have hs := sqrt_two_pi_pos
  have hεε : pgOscEpsilon d ^ 2 = (pgOscRadius d)^2/(2*Real.pi) := by
    unfold pgOscEpsilon
    rw [div_pow, Real.sq_sqrt (by positivity)]
  refine min_eq_left ?_
  rw [hεε]
  unfold pgOscWidth
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
  exact av_rhoBar_width h

theorem two_pi_avgB_le (h : admissible d (pgRstar d) r mu) :
    2 * Real.pi * avgB d r mu ≤ 2 * (pgAnalytic d).LP * mu * r ^ 5 := by
  have hpi := Real.pi_pos
  have hw := pgWidth_pos d
  have hr0 := h.1
  have hmu0 := h.2.2.1
  have hLP := pgAnalytic_LP_ge_one d
  have hK := av_Kbar_pos h
  have hγ := av_gamma_pos h
  have hM0 := pgAnalytic_M0_ge_one d
  have hw' : 0 < pgOscWidth d := by unfold pgOscWidth; positivity
  unfold avgB
  rw [pg_osc_min_eq h]
  set K := (params d r mu).Kbar with hKdef
  set γ := (params d r mu).gammaBar with hγdef
  have hρ : (params d r mu).rhoBar = γ/(2*(pgAnalytic d).M0*(K^(pgTau a b)*K)) := by
    rw [params_rhoBar, ← hKdef, ← hγdef, Real.rpow_add_one hK.ne']
  have hT := Real.rpow_pos_of_pos hK (pgTau a b)
  have hG2 : 1600*(1+(b:ℝ))*(pgAnalytic d).M0 ≤ (pgScales d).G^2 * pgWidth d := by
    obtain ⟨-, -, -, -, hG⟩ := pgScales_spec d
    have h1 := (le_max_right _ _).trans ((le_max_right _ _).trans hG)
    rw [Real.sqrt_le_left (pgScales_G_pos d).le, div_le_iff₀ hw] at h1
    exact h1
  have hγ2 := gammaBar_sq h
  have hr5 : 0 < r^5 := pow_pos hr0 5
  have hM : 0 < (pgAnalytic d).M0 := by linarith
  -- the key inequality
  have hkey : 1600*(1+(b:ℝ))*(pgAnalytic d).M0*((pgAnalytic d).LP*mu)*(K*(K^(pgTau a b))^2) ≤
      γ^2 * pgWidth d * r^5 := by
    rw [div_le_iff₀ hr5] at hγ2
    have hc : 0 ≤ ((pgAnalytic d).LP*mu)*((K^(pgTau a b))^2*K) := by positivity
    have := mul_le_mul_of_nonneg_right hG2 hc
    nlinarith [mul_le_mul_of_nonneg_left hγ2 hw.le]
  unfold pgOscE pgOscAlpha
  rw [← hKdef, ← hγdef, hρ]
  have hE0 : 0 < (pgAnalytic d).LP*mu := by positivity
  have e1 : 2 * Real.pi * (400 * (1 + (b:ℝ)) * ((pgAnalytic d).LP * mu / (2 * Real.pi)) ^ 2 /
      (2 * Real.pi * (γ / (4 * Real.pi * K ^ pgTau a b)) *
        (γ / (2 * (pgAnalytic d).M0 * (K ^ pgTau a b * K)) * pgOscWidth d)) +
      (pgAnalytic d).LP * mu / (2 * Real.pi) * r ^ 5) =
      1600*(1+(b:ℝ))*(pgAnalytic d).M0*((pgAnalytic d).LP*mu)^2*(K*(K^(pgTau a b))^2) /
        (γ^2 * pgWidth d) + (pgAnalytic d).LP * mu * r ^ 5 := by
    unfold pgOscWidth
    field_simp
    ring
  rw [e1]
  have : 1600*(1+(b:ℝ))*(pgAnalytic d).M0*((pgAnalytic d).LP*mu)^2*(K*(K^(pgTau a b))^2) /
      (γ^2 * pgWidth d) ≤ (pgAnalytic d).LP * mu * r ^ 5 := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hkey hE0.le
    nlinarith [this]
  linarith

end KAM.Planetary

end
