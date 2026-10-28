/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ThresholdAlg
public import KAM.Planetary.PGAssembly.ThresholdLimits
public import KAM.Planetary.PGMeasure.Collar

/-!
# P Part 5: the smallness thresholds (`bpP:p5:rstar`, `bpP:p5:param-facts`, `bpP:p5:rK`)

`rstar` is the preliminary radius of `bpP:p5:rstar`: every requirement is a limit condition as
`r → 0+` (`ThrStatic`, `ThrSmall`), so one radius serves them all. `pgRstar` selects it,
`param_facts` collects the consequences of the parameter choice and `r_k` the bounds on the
enlargement radius. The numerical estimates are in `ThresholdAlg`, the scalar limits in
`ThresholdLimits`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-TH.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter Topology

namespace KAM.Planetary

variable {a b : ℕ}

/-- The radius conditions of `bpP:p5:rstar` that do not involve `mu`. -/
def ThrStatic (d : PGData a b) (R : ℝ) : Prop :=
  0 < R ∧ R < d.r0 ∧ R < Real.exp (-(pgTau a b+1)) ∧ R < Real.exp (-1) ∧ R < 1 ∧
    R^6 ≤ (2*(1+2*b*(pgAnalytic d).LN*(pgAnalytic d).LB)*a*(pgAnalytic d).LN*pgInverseL d)⁻¹ ∧
    (pgAnalytic d).LP ≤ Real.log (1/R) ∧ R^2*(Real.log (1/R))^(pgTau a b+1) ≤ 1 ∧
    Real.sqrt R < pgBoundaryD d ∧
    pgBoundaryA d*Real.sqrt R ≤ (volume d.V).toReal/2 ∧
    (pgAnalytic d).Cdio*pgCgamma d*Real.sqrt R ≤ (volume d.V).toReal/4

/-- The smallness conditions of `bpP:p5:rstar` that are used with `mu` in the admissible range. -/
def ThrSmall (d : PGData a b) (r : ℝ) : Prop :=
  r < (pgAnalytic d).r1/2 ∧ r < pgOscRadius d/4 ∧
    30/pgWidth d*Real.log (1/r)*r^5 ≤ 1 ∧
    pgCgamma d*Real.sqrt r/2*pgWidth d ≤ (pgOscRadius d)^2 ∧
    pgCgamma d*Real.sqrt r/2 ≤ (pgAnalytic d).rho ∧
    r^6 < (pgAnalytic d).muStar ∧ 12*(pgScales d).k1*Real.sqrt r ≤ 1 ∧
    (pgScales d).k1*r^2/2 + 12/pgWidth d*(r^5/((pgScales d).G*(30/pgWidth d)^(1/2:ℝ))) < 1 ∧
    Real.sqrt 2*18/(pgOscRadius d*((pgScales d).G*(30/pgWidth d)^(1/2:ℝ)))*r^4 ≤ (pgScales d).k1

theorem volume_V_pos (d : PGData a b) : 0 < (volume d.V).toReal :=
  ENNReal.toReal_pos (d.hV.measure_pos volume d.hVc.nonempty).ne'
    (d.hVb.measure_lt_top).ne

theorem ev_lt {c : ℝ} (hc : 0 < c) : ∀ᶠ r in 𝓝[>] (0:ℝ), r < c :=
  eventually_lt_of_continuousAt continuousAt_id (by simpa using hc)

theorem pgBoundary_spec (d : PGData a b) : 0 < pgBoundaryA d ∧ 0 < pgBoundaryD d ∧
    ∀ t : ℝ, 0 < t → t < pgBoundaryD d →
      volume {I : Fin a → ℝ | ∃ J ∈ frontier d.V, dist I J < t} ≤
        ENNReal.ofReal (pgBoundaryA d * t) :=
  d.hboundary.choose_spec.choose_spec

theorem eventually_static (d : PGData a b) : ∀ᶠ r in 𝓝[>] (0:ℝ), ThrStatic d r := by
  have hv := volume_V_pos d
  obtain ⟨hA, hD, -⟩ := pgBoundary_spec d
  obtain ⟨-, -, -, hM0, hAN, hLN, hLB, -, -, -, hLP1, -, -, -, -, hCd, -⟩ := pgAnalytic_spec d
  obtain ⟨hinv, -⟩ := pgInverse_spec d
  have hCg := pgCgamma_pos d
  have ha : (0:ℝ) < a := Nat.cast_pos.2 d.ha
  have hc6 : 0 < (2*(1+2*b*(pgAnalytic d).LN*(pgAnalytic d).LB)*a*(pgAnalytic d).LN*pgInverseL d)⁻¹ := by
    have : (0:ℝ) ≤ b := Nat.cast_nonneg b
    have : 0 < pgInverseL d := by linarith
    positivity
  have e6 : ∀ᶠ r in 𝓝[>] (0:ℝ), r^6 <
      (2*(1+2*b*(pgAnalytic d).LN*(pgAnalytic d).LB)*a*(pgAnalytic d).LN*pgInverseL d)⁻¹ :=
    eventually_lt_of_continuousAt (by fun_prop) (by simpa using hc6)
  have eLP : ∀ᶠ r in 𝓝[>] (0:ℝ), (pgAnalytic d).LP ≤ Real.log (1/r) := by
    have := (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).eventually_ge_atTop
      (pgAnalytic d).LP
    simpa [one_div] using this
  have e8 : ∀ᶠ r in 𝓝[>] (0:ℝ), r^2*(Real.log (1/r))^(pgTau a b+1) ≤ 1 := by
    have := ((tendsto_rpow_mul_log_rpow 2 (pgTau a b+1) two_pos).eventually
      (gt_mem_nhds one_pos))
    filter_upwards [this] with r hr
    rw [Real.rpow_two] at hr
    exact hr.le
  have eD : ∀ᶠ r in 𝓝[>] (0:ℝ), Real.sqrt r < pgBoundaryD d :=
    eventually_lt_of_continuousAt Real.continuous_sqrt.continuousAt (by simpa using hD)
  have eA : ∀ᶠ r in 𝓝[>] (0:ℝ), pgBoundaryA d*Real.sqrt r < (volume d.V).toReal/2 :=
    eventually_lt_of_continuousAt (by fun_prop) (by simpa using hv)
  have eC : ∀ᶠ r in 𝓝[>] (0:ℝ), (pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r <
      (volume d.V).toReal/4 :=
    eventually_lt_of_continuousAt (by fun_prop) (by simpa using hv)
  filter_upwards [self_mem_nhdsWithin, ev_lt d.hr0, ev_lt (Real.exp_pos (-(pgTau a b+1))),
    ev_lt (Real.exp_pos (-1)), ev_lt one_pos, e6, eLP, e8, eD, eA, eC] with
    r h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨h0, h1, h2, h3, h4, h5.le, h6, h7, h8, h9.le, h10.le⟩

theorem eventually_small (d : PGData a b) : ∀ᶠ r in 𝓝[>] (0:ℝ), ThrSmall d r := by
  obtain ⟨hrho, -, -, -, -, -, -, hmuS, -, -, -, -, -, hr1, -⟩ := pgAnalytic_spec d
  have hw := pgWidth_pos d
  have hosc := pgOscRadius_pos d
  have hCg := pgCgamma_pos d
  have hk1 := pgScales_k1_pos d
  have hG := pgScales_G_pos d
  have hκ : 0 < 30/pgWidth d := by positivity
  have hq : 0 < (pgScales d).G*(30/pgWidth d)^(1/2:ℝ) := by positivity
  have e3 : ∀ᶠ r in 𝓝[>] (0:ℝ), 30/pgWidth d*Real.log (1/r)*r^5 ≤ 1 := by
    have := ((tendsto_rpow_mul_log_rpow 5 1 (by norm_num)).eventually
      (gt_mem_nhds (inv_pos.2 hκ)))
    filter_upwards [this] with r hr
    rw [Real.rpow_one, show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast] at hr
    have h := mul_lt_mul_of_pos_left hr hκ
    rw [mul_inv_cancel₀ hκ.ne'] at h
    linarith
  have e4 : ∀ᶠ r in 𝓝[>] (0:ℝ), pgCgamma d*Real.sqrt r/2*pgWidth d < (pgOscRadius d)^2 :=
    eventually_lt_of_continuousAt (by fun_prop) (by simpa using pow_pos hosc 2)
  have e5 : ∀ᶠ r in 𝓝[>] (0:ℝ), pgCgamma d*Real.sqrt r/2 < (pgAnalytic d).rho :=
    eventually_lt_of_continuousAt (by fun_prop) (by simpa using hrho)
  have e6 : ∀ᶠ r in 𝓝[>] (0:ℝ), r^6 < (pgAnalytic d).muStar :=
    eventually_lt_of_continuousAt (by fun_prop) (by simpa using hmuS)
  have e7 : ∀ᶠ r in 𝓝[>] (0:ℝ), 12*(pgScales d).k1*Real.sqrt r < 1 :=
    eventually_lt_of_continuousAt (by fun_prop) (by simp)
  have e8 : ∀ᶠ r in 𝓝[>] (0:ℝ), (pgScales d).k1*r^2/2 +
      12/pgWidth d*(r^5/((pgScales d).G*(30/pgWidth d)^(1/2:ℝ))) < 1 :=
    eventually_lt_of_continuousAt (by fun_prop) (by simp)
  have e9 : ∀ᶠ r in 𝓝[>] (0:ℝ), Real.sqrt 2*18/(pgOscRadius d*((pgScales d).G*
      (30/pgWidth d)^(1/2:ℝ)))*r^4 < (pgScales d).k1 :=
    eventually_lt_of_continuousAt (by fun_prop) (by simpa using hk1)
  filter_upwards [ev_lt (half_pos hr1 : 0 < (pgAnalytic d).r1/2), ev_lt (by positivity : 0 < pgOscRadius d/4),
    e3, e4, e5, e6, e7, e8, e9] with r h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4.le, h5.le, h6, h7.le, h8, h9.le⟩

end KAM.Planetary

end
