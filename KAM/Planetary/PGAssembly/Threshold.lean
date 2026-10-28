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

theorem pgAnalytic_dio (d : PGData a b) : ∀ gamma : ℝ, 0 < gamma →
    volume {I ∈ d.V | ¬ KAM.IsDiophantine gamma ((a+b:ℕ)+1) (fastFrequency d.H0 I)} ≤
      ENNReal.ofReal ((pgAnalytic d).Cdio*gamma) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := pgAnalytic_spec d
  exact h

theorem gammaBar_pos {d : PGData a b} {r : ℝ} (hr0 : 0 < r) (hr : r ≤ Real.exp (-1)) (mu : ℝ) :
    0 < (params d r mu).gammaBar := by
  have hL := one_le_log_inv hr0 hr
  have hK : 0 < (params d r mu).Kbar := by
    rw [params_Kbar]; have := pgWidth_pos d; have : 0 < Real.log (1/r) := by linarith
    positivity
  have hg : (pgScales d).G * (r^(5/2:ℝ) * (params d r mu).Kbar^(pgTau a b+1)) ≤
      (params d r mu).gammaBar := by
    rw [params_gammaBar]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (pgScales_G_pos d).le
  have := pgScales_G_pos d
  have : 0 < (pgScales d).G * (r^(5/2:ℝ) * (params d r mu).Kbar^(pgTau a b+1)) := by
    have := Real.rpow_pos_of_pos hK (pgTau a b+1)
    have := Real.rpow_pos_of_pos hr0 (5/2:ℝ)
    positivity
  linarith

theorem ofReal_mul_volume {v : ENNReal} (hv : v ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal c * v = ENNReal.ofReal (c * v.toReal) := by
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hv]

theorem thr_volumes {d : PGData a b} {r mu : ℝ} (hR : ThrRange d r mu)
    (hD : Real.sqrt r < pgBoundaryD d) (hA : pgBoundaryA d*Real.sqrt r ≤ (volume d.V).toReal/2)
    (hC : (pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r ≤ (volume d.V).toReal/4) :
    ENNReal.ofReal (1/2)*volume d.V ≤ volume (innerCore d.V (Real.sqrt r)) ∧
      ENNReal.ofReal (1/4)*volume d.V ≤ volume (checkedCore d r mu) := by
  have hg := gammaBar_le hR
  obtain ⟨hr0, hr, hmu0, -⟩ := hR
  have hgpos := gammaBar_pos (d := d) hr0 hr mu
  have hvt : volume d.V ≠ ⊤ := d.hVb.measure_lt_top.ne
  have hvV := volume_V_pos d
  set v := volume d.V with hv
  have ht : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  obtain ⟨hA0, hD0, hcl⟩ := pgBoundary_spec d
  have hcol := collar d.hV d.hVb hcl
  have hd1 := (hcol.2.1 _ ht hD).1
  have hcover : d.V ⊆ innerCore d.V (Real.sqrt r) ∪ (d.V \ innerCore d.V (Real.sqrt r)) := by
    intro x hx
    by_cases h : x ∈ innerCore d.V (Real.sqrt r)
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have h1 : v ≤ volume (innerCore d.V (Real.sqrt r)) + ENNReal.ofReal (pgBoundaryA d*Real.sqrt r) :=
    (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add le_rfl hd1))
  have hA' : ENNReal.ofReal (pgBoundaryA d*Real.sqrt r) ≤ ENNReal.ofReal (v.toReal/2) :=
    ENNReal.ofReal_le_ofReal hA
  have e0 : 0 ≤ pgBoundaryA d*Real.sqrt r := by positivity
  have hvr : v = ENNReal.ofReal v.toReal := (ENNReal.ofReal_toReal hvt).symm
  refine ⟨?_, ?_⟩
  · refine (ENNReal.add_le_add_iff_right
      (ENNReal.ofReal_ne_top : ENNReal.ofReal (pgBoundaryA d*Real.sqrt r) ≠ ⊤)).1 ?_
    calc ENNReal.ofReal (1/2) * v + ENNReal.ofReal (pgBoundaryA d*Real.sqrt r)
        ≤ ENNReal.ofReal (1/2*v.toReal) + ENNReal.ofReal (v.toReal/2) := by
          rw [ofReal_mul_volume hvt (by norm_num)]; exact add_le_add le_rfl hA'
      _ = ENNReal.ofReal v.toReal := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ = v := hvr.symm
      _ ≤ _ := h1
  · have hbad := pgAnalytic_dio d _ hgpos
    have hcover2 : d.V ⊆ checkedCore d r mu ∪ ((d.V \ innerCore d.V (Real.sqrt r)) ∪
        {I ∈ d.V | ¬ KAM.IsDiophantine (params d r mu).gammaBar ((a+b:ℕ)+1)
          (fastFrequency d.H0 I)}) := by
      intro x hx
      by_cases h : x ∈ innerCore d.V (Real.sqrt r)
      · by_cases h' : KAM.IsDiophantine (params d r mu).gammaBar ((a+b:ℕ)+1) (fastFrequency d.H0 x)
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr (Or.inr ⟨hx, h'⟩)
      · exact Or.inr (Or.inl ⟨hx, h⟩)
    have hbad' : ENNReal.ofReal ((pgAnalytic d).Cdio*(params d r mu).gammaBar) ≤
        ENNReal.ofReal ((pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r) := by
      apply ENNReal.ofReal_le_ofReal
      have := (pgAnalytic_spec d).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      calc (pgAnalytic d).Cdio*(params d r mu).gammaBar ≤ (pgAnalytic d).Cdio*(pgCgamma d*Real.sqrt r) :=
            mul_le_mul_of_nonneg_left hg this.le
        _ = _ := by ring
    have h2 : v ≤ volume (checkedCore d r mu) + (ENNReal.ofReal (pgBoundaryA d*Real.sqrt r) +
        ENNReal.ofReal ((pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r)) :=
      (measure_mono hcover2).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl ((measure_union_le _ _).trans (add_le_add hd1 (hbad.trans hbad')))))
    have e1 : 0 ≤ (pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r := by
      have := (pgAnalytic_spec d).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have := pgCgamma_pos d
      positivity
    refine (ENNReal.add_le_add_iff_right
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩ :
        ENNReal.ofReal (pgBoundaryA d*Real.sqrt r) +
          ENNReal.ofReal ((pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r) ≠ ⊤)).1 ?_
    calc ENNReal.ofReal (1/4) * v + (ENNReal.ofReal (pgBoundaryA d*Real.sqrt r) +
          ENNReal.ofReal ((pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r))
        = ENNReal.ofReal (1/4*v.toReal + (pgBoundaryA d*Real.sqrt r +
            (pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r)) := by
          rw [ofReal_mul_volume hvt (by norm_num), ← ENNReal.ofReal_add e0 e1,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal v.toReal := ENNReal.ofReal_le_ofReal (by linarith)
      _ = v := hvr.symm
      _ ≤ _ := h2

theorem rpow_three_halves {r : ℝ} (hr : 0 < r) : r^(3/2:ℝ) = r * Real.sqrt r := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hr.le (by norm_num)]; norm_num

theorem thr_key {d : PGData a b} {r mu : ℝ} (c c' : ℝ) :
    c*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/(c'*(params d r mu).gammaBar) =
      c/c'*((pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/(params d r mu).gammaBar) := by
  rw [show c*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b) =
    c*((pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)) by ring]
  exact (div_mul_div_comm _ _ _ _).symm

theorem thr_q_pos (d : PGData a b) : 0 < (pgScales d).G*(30/pgWidth d)^(1/2:ℝ) := by
  have := one_le_pgKappa d
  have : 0 < (30/pgWidth d)^(1/2:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have := pgScales_G_pos d
  positivity

theorem thr_e5 {d : PGData a b} {r mu : ℝ} (hR : ThrRange d r mu) (hsq : 0 < Real.sqrt r)
    (s8 : (pgScales d).k1*r^2/2 + 12/pgWidth d*(r^5/((pgScales d).G*(30/pgWidth d)^(1/2:ℝ))) < 1)
    (hrK : (params d r mu).rK < (pgScales d).k1*(r^2*Real.sqrt r)/2) :
    (params d r mu).rK + 12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
      (pgWidth d*(params d r mu).gammaBar) < Real.sqrt r := by
  have hT := gammaBar_ratio hR
  have hw := pgWidth_pos d
  have hq := thr_q_pos d
  rw [thr_key]
  have h1 := mul_le_mul_of_nonneg_left hT (by positivity : (0:ℝ) ≤ 12/pgWidth d)
  have h2 := mul_lt_mul_of_pos_right s8 hsq
  have E : (pgScales d).k1*(r^2*Real.sqrt r)/2 +
      12/pgWidth d*(Real.sqrt r*r^5/((pgScales d).G*(30/pgWidth d)^(1/2:ℝ))) =
      ((pgScales d).k1*r^2/2 + 12/pgWidth d*(r^5/((pgScales d).G*(30/pgWidth d)^(1/2:ℝ))))*
        Real.sqrt r := by ring
  linarith

theorem thr_e6 {d : PGData a b} {r mu : ℝ} (hR : ThrRange d r mu) (h0 : 0 < r)
    (s9 : Real.sqrt 2*18/(pgOscRadius d*((pgScales d).G*(30/pgWidth d)^(1/2:ℝ)))*r^4 ≤
      (pgScales d).k1) :
    Real.sqrt 2 * (18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
      (pgOscRadius d*(params d r mu).gammaBar)) ≤ (pgScales d).k1*r^(3/2:ℝ) := by
  have hT := gammaBar_ratio hR
  have hosc := pgOscRadius_pos d
  have hq := thr_q_pos d
  rw [thr_key, rpow_three_halves h0]
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 h0
  have h1 := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ Real.sqrt 2*(18/pgOscRadius d))
  have h3 := mul_le_mul_of_nonneg_right s9 (by positivity : 0 ≤ r*Real.sqrt r)
  calc Real.sqrt 2 * (18/pgOscRadius d*((pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
        (params d r mu).gammaBar))
      = Real.sqrt 2*(18/pgOscRadius d)*((pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
        (params d r mu).gammaBar) := by ring
    _ ≤ Real.sqrt 2*(18/pgOscRadius d)*(Real.sqrt r*r^5/((pgScales d).G*(30/pgWidth d)^(1/2:ℝ))) :=
        h1
    _ = Real.sqrt 2*18/(pgOscRadius d*((pgScales d).G*(30/pgWidth d)^(1/2:ℝ)))*r^4*
        (r*Real.sqrt r) := by ring
    _ ≤ _ := h3

theorem thr_dynamic {d : PGData a b} {r mu : ℝ} (hS : ThrStatic d r) (hSm : ThrSmall d r)
    (hmu0 : 0 < mu) (hmu : mu < r^6/(Real.log (1/r))^(2*pgTau a b+2)) :
    r < (pgAnalytic d).r1/2 ∧ r < pgOscRadius d/4 ∧
      (params d r mu).Kbar*r^5 ≤ 1 ∧
      (params d r mu).rhoBar*pgWidth d ≤ (pgOscRadius d)^2 ∧
      (params d r mu).rK + 12*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
        (pgWidth d*(params d r mu).gammaBar) < Real.sqrt r ∧
      Real.sqrt 2 * (18*(pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b)/
        (pgOscRadius d*(params d r mu).gammaBar)) ≤ (pgScales d).k1*r^(3/2:ℝ) ∧
      0 < (params d r mu).l1 ∧ (params d r mu).ell ≥ r^2/4 ∧
      (params d r mu).rhoBar ≤ (pgAnalytic d).rho ∧
      (params d r mu).l1 ≤ (params d r mu).rhoBar ∧
      mu < (pgAnalytic d).muStar ∧ pgChat a b*(params d r mu).Ehat < 1 ∧
      (params d r mu).rK < min (Real.sqrt r) ((params d r mu).l1) ∧
      (params d r mu).rK < (params d r mu).rhoBar/2 ∧
      ENNReal.ofReal (1/2)*volume d.V ≤ volume (innerCore d.V (Real.sqrt r)) ∧
      ENNReal.ofReal (1/4)*volume d.V ≤ volume (checkedCore d r mu) := by
  obtain ⟨h0, -, -, hrE, hr1, -, hLP, h8, hD, hA, hC⟩ := hS
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hSm
  have hR : ThrRange d r mu := ⟨h0, hrE.le, hmu0, hLP, hmu, h8⟩
  have hw := pgWidth_pos d
  have hk1 := pgScales_k1_pos d
  have hG := pgScales_G_pos d
  have hosc := pgOscRadius_pos d
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 h0
  have hs1 : Real.sqrt r < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using hr1
  have hss : Real.sqrt r ^ 2 = r := Real.sq_sqrt h0.le
  have hrs : r < Real.sqrt r := by nlinarith
  have hl1 : (params d r mu).l1 = (pgScales d).k1*(r^2*Real.sqrt r) := by
    rw [params_l1, rpow_five_halves h0]
  have hl1pos : 0 < (params d r mu).l1 := by rw [hl1]; positivity
  have hell : (params d r mu).ell ≥ r^2/4 := by
    rw [params_ell, hl1]
    nlinarith [mul_le_mul_of_nonneg_left s7 (sq_nonneg r)]
  have hl1le : (params d r mu).l1 ≤ r^2/12 := by
    have := params_ell d r mu
    linarith
  have hr2 : r^2 < r := by nlinarith
  have hl1s : (params d r mu).l1 < Real.sqrt r := by nlinarith
  have hρ := rhoHat_pos d h0 mu
  have hn : (1:ℝ) ≤ ((a+b:ℕ):ℝ) := by
    have := d.ha; exact_mod_cast (by omega : 1 ≤ a+b)
  have hrK : (params d r mu).rK < (params d r mu).l1/2 := by
    have h1 := rK_lt (d := d) h0 mu
    have h2 : (params d r mu).rhoHat/(256*((a+b:ℕ):ℝ)) ≤ (params d r mu).rhoHat :=
      div_le_self hρ.le (by linarith)
    have h3 := rhoHat_le_l1 d r mu
    linarith
  have hlr := l1_le_rhoBar d h0 hrE.le mu
  have hbar := rhoBar_le hR
  have hT := gammaBar_ratio hR
  have hq : 0 < (pgScales d).G*(30/pgWidth d)^(1/2:ℝ) := by
    have := one_le_pgKappa d
    have : 0 < (30/pgWidth d)^(1/2:ℝ) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have e5 := thr_e5 hR hsq s8 (hl1 ▸ hrK)
  have e6 := thr_e6 hR h0 s9
  have e11 : mu < (pgAnalytic d).muStar := by
    have hX : 1 ≤ (Real.log (1/r))^(2*pgTau a b+2) :=
      Real.one_le_rpow (one_le_log_inv h0 hrE.le) (by linarith [pgTau_pos a b])
    exact lt_of_lt_of_le hmu ((div_le_self (by positivity) hX).trans s6.le) |>.trans_le' le_rfl
  obtain ⟨hv1, hv2⟩ := thr_volumes hR hD hA hC
  exact ⟨s1, s2, by rw [params_Kbar]; exact s3,
    (mul_le_mul_of_nonneg_right hbar hw.le).trans s4, e5, e6, hl1pos, hell, hbar.trans s5, hlr,
    e11, chat_Ehat_lt h0 mu, lt_min (by linarith) (by linarith), by linarith, hv1, hv2⟩

end KAM.Planetary

end
