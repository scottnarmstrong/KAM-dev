/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingDiv

/-!
# P Part 5: the smallness condition of the averaging adapter (`stepP:p5:av-R2`)

`pg_osc_small`: `2^12 (1+b) K E s ≤ α min(r s, ε²)` for the data supplied to `OscHyp`. It reduces
to `G² ≥ 2^14 (1+b) M0 K r^5`, supplied by the existing `G` condition of `PGScaleSpec` and
`K r^5 ≤ 1`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ} {d : PGData a b} {r mu : ℝ}

theorem rpow_half_sq {K : ℝ} (hK : 0 < K) (τ : ℝ) :
    (K^(τ+1/2:ℝ))^2 = (K^τ)^2*K := by
  calc (K^(τ+1/2:ℝ))^2 = K^((τ+1/2)*2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]; norm_num
    _ = K^(τ*2+1) := by ring_nf
    _ = K^(τ*2) * K := by rw [Real.rpow_add_one hK.ne']
    _ = (K^τ)^2 * K := by
        rw [Real.rpow_mul hK.le]; norm_num

theorem rpow_five_halves_sq {r : ℝ} (hr : 0 < r) : (r^(5/2:ℝ))^2 = r^5 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num

theorem gammaBar_sq (h : admissible d (pgRstar d) r mu) :
    (pgScales d).G^2 * ((pgAnalytic d).LP*mu) * (((params d r mu).Kbar^(pgTau a b))^2 *
      (params d r mu).Kbar) / r^5 ≤ (params d r mu).gammaBar^2 := by
  have hr0 := h.1
  have hmu0 := h.2.2.1
  have hLP := pgAnalytic_LP_ge_one d
  have hK := av_Kbar_pos h
  have hG := pgScales_G_pos d
  set K := (params d r mu).Kbar
  have hc0 : 0 < (pgAnalytic d).LP * mu := by positivity
  have hA : (pgScales d).G * (Real.sqrt ((pgAnalytic d).LP*mu) * K^(pgTau a b+1/2:ℝ) *
      r^(-5/2:ℝ)) ≤ (params d r mu).gammaBar := by
    rw [params_gammaBar]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hG.le
  have hA0 : 0 ≤ (pgScales d).G * (Real.sqrt ((pgAnalytic d).LP*mu) * K^(pgTau a b+1/2:ℝ) *
      r^(-5/2:ℝ)) := by
    have := Real.rpow_pos_of_pos hK (pgTau a b+1/2)
    have := Real.rpow_pos_of_pos hr0 (-5/2:ℝ)
    positivity
  have hsq := pow_le_pow_left₀ hA0 hA 2
  refine le_trans (le_of_eq ?_) hsq
  have h1 : (r^(-5/2:ℝ))^2 = (r^5)⁻¹ := by
    rw [show (-5/2:ℝ) = -(5/2) by norm_num, Real.rpow_neg hr0.le, inv_pow, rpow_five_halves_sq hr0]
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hc0.le, rpow_half_sq hK, h1]
  ring

theorem pg_osc_small (h : admissible d (pgRstar d) r mu) :
    2 ^ 12 * (1 + (b : ℝ)) * (15/(Real.pi*pgOscWidth d)*Real.log (1/r)) * pgOscE d mu *
        pgOscWidth d ≤
      pgOscAlpha d r mu * min ((params d r mu).rhoBar * pgOscWidth d)
        (pgOscEpsilon d * pgOscEpsilon d) := by
  have hpi := Real.pi_pos
  have hw := pgWidth_pos d
  have hr0 := h.1
  have hmu0 := h.2.2.1
  have hLP := pgAnalytic_LP_ge_one d
  have hK := av_Kbar_pos h
  have hγ := av_gamma_pos h
  have hρ0 := av_rhoBar_pos h
  have hM0 := pgAnalytic_M0_ge_one d
  have hτ := pgTau_pos a b
  have hw' : 0 < pgOscWidth d := by unfold pgOscWidth; positivity
  have hs : 0 < Real.sqrt (2*Real.pi) := sqrt_two_pi_pos
  have hεε : pgOscEpsilon d * pgOscEpsilon d = (pgOscRadius d)^2/(2*Real.pi) := by
    unfold pgOscEpsilon
    rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity), sq]
  have hmin : min ((params d r mu).rhoBar * pgOscWidth d) (pgOscEpsilon d * pgOscEpsilon d) =
      (params d r mu).rhoBar * pgOscWidth d := by
    refine min_eq_left ?_
    rw [hεε]
    unfold pgOscWidth
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    exact av_rhoBar_width h
  rw [hmin, pgOsc_K_eq, ← params_Kbar]
  set K := (params d r mu).Kbar with hKdef
  set γ := (params d r mu).gammaBar with hγdef
  have hρ : (params d r mu).rhoBar = γ/(2*(pgAnalytic d).M0*(K^(pgTau a b)*K)) := by
    rw [params_rhoBar, ← hKdef, ← hγdef, Real.rpow_add_one hK.ne']
  rw [hρ]
  have hT := Real.rpow_pos_of_pos hK (pgTau a b)
  have hG2 : 2^14*(1+(b:ℝ))*(pgAnalytic d).M0 ≤ (pgScales d).G^2 := by
    obtain ⟨-, -, -, -, hG⟩ := pgScales_spec d
    have := (le_max_left _ _).trans ((le_max_right _ _).trans hG)
    rw [Real.sqrt_le_left (pgScales_G_pos d).le] at this
    exact this
  have hγ2 := gammaBar_sq h
  have hKr := av_K_r5 h
  have hr5 : 0 < r^5 := pow_pos hr0 5
  unfold pgOscE pgOscAlpha
  rw [← hKdef, ← hγdef]
  -- main estimate
  have hkey : 2^14*(1+(b:ℝ))*(pgAnalytic d).M0*((pgAnalytic d).LP*mu)*(K^(pgTau a b))^2*K*K ≤ γ^2 := by
    have h1 : 2^14*(1+(b:ℝ))*(pgAnalytic d).M0*K ≤ (pgScales d).G^2 / r^5 := by
      rw [le_div_iff₀ hr5]
      calc 2^14*(1+(b:ℝ))*(pgAnalytic d).M0*K*r^5 ≤ 2^14*(1+(b:ℝ))*(pgAnalytic d).M0 * 1 := by
            have : 0 ≤ 2^14*(1+(b:ℝ))*(pgAnalytic d).M0 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hKr this]
        _ ≤ _ := by linarith
    have h2 : (pgScales d).G^2 * ((pgAnalytic d).LP*mu) * ((K^(pgTau a b))^2 * K) / r^5 =
        (pgScales d).G^2 / r^5 * (((pgAnalytic d).LP*mu) * ((K^(pgTau a b))^2 * K)) := by ring
    rw [h2] at hγ2
    refine le_trans ?_ hγ2
    have h3 : 0 ≤ ((pgAnalytic d).LP*mu) * ((K^(pgTau a b))^2 * K) := by positivity
    have := mul_le_mul_of_nonneg_right h1 h3
    nlinarith [this]
  have hE : (pgAnalytic d).LP*mu/(2*Real.pi) =
      (pgAnalytic d).LP*mu/(2*Real.pi) := rfl
  rw [show γ/(4*Real.pi*K^(pgTau a b)) * (γ/(2*(pgAnalytic d).M0*(K^(pgTau a b)*K)) *
      pgOscWidth d) = γ^2/(8*Real.pi*(pgAnalytic d).M0*K*(K^(pgTau a b))^2) * pgOscWidth d by
    field_simp; ring]
  refine mul_le_mul_of_nonneg_right ?_ hw'.le
  rw [le_div_iff₀ (by positivity)]
  have hM : 0 < (pgAnalytic d).M0 := by linarith
  have e : 2 ^ 12 * (1 + (b:ℝ)) * K * ((pgAnalytic d).LP * mu / (2 * Real.pi)) *
      (8 * Real.pi * (pgAnalytic d).M0 * K * (K ^ pgTau a b) ^ 2) =
      2^14*(1+(b:ℝ))*(pgAnalytic d).M0*((pgAnalytic d).LP*mu)*(K^(pgTau a b))^2*K*K := by
    field_simp; ring
  rw [e]
  exact hkey

end KAM.Planetary

end
