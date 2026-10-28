/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Cauchy
public import KAM.Strip.Regularity
public import KAM.Planetary.MaximalStep.Basic

/-!
# First-order Taylor part in the action (P11A-C3, `bpP:p11a:taylor-cutoff`)

For `F` admissible on `D(r,s;B)` with `|F| ≤ M`, the first-order Taylor polynomial `F^{(≤1)}` in
`η` at `η = 0` is admissible, bounded by `2M`, with remainder `≤ M q²/(1-q)` on `D(r,qs;B)`, and
the `η`-derivative at `η = 0` is bounded by `M/s`.

The one-variable input (`stepP:p11a:tc-line`) is the Cauchy power series of
`ζ ↦ F(θ, ζ η, b)` on the disc of radius `1/q`: its coefficients are `≤ M q^j`
(`p11_series_remainder`). The sup bound on the first derivative is the closed-ball Cauchy estimate
(`p11_norm_fderiv_le_of_ball`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KAM.Planetary

/-- `stepP:p11a:tc-line`: remainder of a one-variable power series bounded by `M` on the disc
of radius `1/q`. -/
theorem p11_series_remainder {g : ℂ → ℂ} {M q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : DifferentiableOn ℂ g (closedBall 0 (1 / q)))
    (hb : ∀ ζ ∈ closedBall (0 : ℂ) (1 / q), ‖g ζ‖ ≤ M) :
    ‖g 1 - g 0 - deriv g 0‖ ≤ M * q ^ 2 / (1 - q) := by
  have hR : (0 : ℝ) < 1 / q := one_div_pos.mpr hq0
  set R : ℝ≥0 := (1 / q).toNNReal with hRdef
  have hRc : (R : ℝ) = 1 / q := Real.coe_toNNReal _ hR.le
  have hRpos : 0 < R := by
    rw [← NNReal.coe_pos, hRc]; exact hR
  have hp := (hRc ▸ hd : DifferentiableOn ℂ g (closedBall 0 R)).hasFPowerSeriesOnBall hRpos
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_closedBall_self hR.le))
  have hcoeff : ∀ n, ‖cauchyPowerSeries g 0 R n‖ ≤ M * q ^ n := by
    intro n
    refine (norm_cauchyPowerSeries_le g 0 R n).trans ?_
    have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, ‖g (circleMap 0 R θ)‖ ≤ M * (2 * Real.pi) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := 2 * Real.pi) (C := M) (f := fun θ => ‖g (circleMap 0 R θ)‖)
        (fun θ _ => by
          rw [norm_norm]
          refine hb _ ?_
          rw [← hRc]
          exact sphere_subset_closedBall (circleMap_mem_sphere 0 hRpos.le θ))
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      convert this using 2
      rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring
    have hinv : |(R : ℝ)|⁻¹ = q := by
      rw [hRc, abs_of_pos hR]; field_simp
    rw [hinv]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖g (circleMap 0 R θ)‖ ≤ M := by
      calc _ ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) := by gcongr
        _ = M := by field_simp
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hq0.le _)
  have hsum := hp.hasSum (y := 1) (by
    rw [Metric.mem_eball, edist_zero_right]
    have : ‖(1 : ℂ)‖₊ < R := by
      rw [← NNReal.coe_lt_coe, hRc]
      simp only [coe_nnnorm, norm_one]
      rw [lt_div_iff₀ hq0]; linarith
    exact ENNReal.coe_lt_coe.mpr this)
  rw [zero_add] at hsum
  have hsum2 := (hasSum_nat_add_iff' 2).mpr hsum
  have hgeo : HasSum (fun n : ℕ => M * q ^ 2 * q ^ n) (M * q ^ 2 * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
  have h0 : cauchyPowerSeries g 0 R 0 (fun _ => 1) = g 0 := hp.hasFPowerSeriesAt.coeff_zero _
  have h1 : cauchyPowerSeries g 0 R 1 (fun _ => 1) = deriv g 0 :=
    hp.hasFPowerSeriesAt.deriv.symm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1] at hsum2
  have := hsum2.norm_le_of_bounded hgeo (fun n => by
    calc ‖cauchyPowerSeries g 0 R (n + 2) fun _ => 1‖
        ≤ ‖cauchyPowerSeries g 0 R (n + 2)‖ * ∏ _i : Fin (n + 2), ‖(1 : ℂ)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ M * q ^ (n + 2) := by simpa using hcoeff (n + 2)
      _ = M * q ^ 2 * q ^ n := by ring)
  rw [div_eq_mul_inv]
  convert this using 2
  rw [sub_sub]

/-- `stepP:p11a:tc-a`: Cauchy bound `M / s` for the derivative at the centre of a ball. -/
theorem p11_norm_fderiv_le_of_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {φ : E → ℂ} {s M : ℝ} (hs : 0 < s) (hd : DifferentiableOn ℂ φ (ball 0 s))
    (hb : ∀ w ∈ ball (0 : E) s, ‖φ w‖ ≤ M) : ‖fderiv ℂ φ 0‖ ≤ M / s := by
  have hδ : ∀ δ, 0 < δ → δ < s → ‖fderiv ℂ φ 0‖ * δ ≤ M := by
    intro δ h0 h1
    have hsub : closedBall (0 : E) δ ⊆ ball 0 s := closedBall_subset_ball h1
    have := KAM.norm_fderiv_le_of_closedBall_bound isOpen_ball hd h0 hsub
      (fun w hw => hb w (hsub hw))
    rwa [le_div_iff₀ h0] at this
  rw [le_div_iff₀ hs]
  by_contra hcon'
  have hcon := not_le.mp hcon'
  have hL : 0 < ‖fderiv ℂ φ 0‖ := by
    by_contra h0
    have : ‖fderiv ℂ φ 0‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_ball_self hs))
    rw [this] at hcon
    linarith
  have h2 := hδ ((M / ‖fderiv ℂ φ 0‖ + s) / 2) (by
      have : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_ball_self hs))
      positivity) (by
      have : M / ‖fderiv ℂ φ 0‖ < s := by rwa [div_lt_iff₀ hL, mul_comm]
      linarith)
  have h3 : M < ‖fderiv ℂ φ 0‖ * ((M / ‖fderiv ℂ φ 0‖ + s) / 2) := by
    have : M / ‖fderiv ℂ φ 0‖ < s := by rwa [div_lt_iff₀ hL, mul_comm]
    have e : ‖fderiv ℂ φ 0‖ * (M / ‖fderiv ℂ φ 0‖) = M := mul_div_cancel₀ _ hL.ne'
    nlinarith
  linarith

/-- `stepP:p11a:tc-b`: second-order remainder of a function bounded by `M` on `ball 0 s`,
evaluated at `‖η‖ < q s`. -/
theorem p11_taylor_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {φ : E → ℂ} {s M q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : DifferentiableOn ℂ φ (ball 0 s)) (hb : ∀ w ∈ ball (0 : E) s, ‖φ w‖ ≤ M)
    {η : E} (hη : ‖η‖ < q * s) :
    ‖φ η - φ 0 - fderiv ℂ φ 0 η‖ ≤ M * q ^ 2 / (1 - q) := by
  have hs : 0 < s := by
    by_contra h
    have := norm_nonneg η
    nlinarith
  have hmem : ∀ ζ ∈ closedBall (0 : ℂ) (1 / q), ζ • η ∈ ball (0 : E) s := by
    intro ζ hζ
    rw [mem_ball_zero_iff, norm_smul]
    have hζ' : ‖ζ‖ ≤ 1 / q := mem_closedBall_zero_iff.mp hζ
    calc ‖ζ‖ * ‖η‖ ≤ (1 / q) * ‖η‖ := by gcongr
      _ < (1 / q) * (q * s) := by gcongr
      _ = s := by field_simp
  have hdiffg : ∀ ζ ∈ closedBall (0 : ℂ) (1 / q), DifferentiableAt ℂ (fun ζ : ℂ => φ (ζ • η)) ζ := by
    intro ζ hζ
    exact ((hd.differentiableAt (isOpen_ball.mem_nhds (hmem ζ hζ))).comp ζ
      (differentiableAt_id.smul_const η))
  have h := p11_series_remainder (g := fun ζ : ℂ => φ (ζ • η)) hq0 hq1
    (fun ζ hζ => (hdiffg ζ hζ).differentiableWithinAt)
    (fun ζ hζ => hb _ (hmem ζ hζ)) (M := M)
  have hφ0 : DifferentiableAt ℂ φ 0 := hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hs))
  have hder : deriv (fun ζ : ℂ => φ (ζ • η)) 0 = fderiv ℂ φ 0 η := by
    have h1 : HasDerivAt (fun ζ : ℂ => ζ • η) η 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const η
    have h2 : HasFDerivAt φ (fderiv ℂ φ 0) ((fun ζ : ℂ => ζ • η) 0) := by
      simpa using hφ0.hasFDerivAt
    exact (h2.comp_hasDerivAt 0 h1).deriv
  simpa [hder] using h

end KAM.Planetary
