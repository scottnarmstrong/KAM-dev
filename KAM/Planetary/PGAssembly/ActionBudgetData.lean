/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ActionBudgetReal
public import KAM.Planetary.PGAssembly.ActionBudgetDefs
public import KAM.Planetary.PGMeasure.TwoScale

/-!
# P Part 5: the P4 measure data of the Cantor budget (`stepP:p5:bu-dio`, inputs)

`pgMeasureData d core` is the S4 data of `bpP:p4:data` for the frozen data `d` on a compact core
of positive volume, with the constants `pgAnalytic`, `pgInverseL`, `pgInverseR`; its constants
`measure_c1`, `measure_c2` are bounded by `pgMeasureUpper1/2` when the core has at least half the
volume of `V`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-BU.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

def pgMu1 (d : PGData a b) : ℝ :=
  min d.mu0 ((2*(1+2*b*(pgAnalytic d).LN*(pgAnalytic d).LB)*a*(pgAnalytic d).LN*
    pgInverseL d)⁻¹)

theorem pgMu1_pos (d : PGData a b) : 0 < pgMu1 d := by
  obtain ⟨hL, -⟩ := pgInverse_spec d
  obtain ⟨-, -, -, -, -, hLN, hLB, -⟩ := pgAnalytic_spec d
  have := d.ha
  have : (0:ℝ) < a := by exact_mod_cast d.ha
  have : (0:ℝ) < 2*(1+2*b*(pgAnalytic d).LN*(pgAnalytic d).LB)*a*(pgAnalytic d).LN*
    pgInverseL d := by positivity
  exact lt_min d.hmu0 (inv_pos.2 this)

def pgMeasureData (d : PGData a b) (core : Set (Fin a → ℝ)) (hcore : IsCompact core)
    (hcoreV : core ⊆ d.V) (hvol : 0 < volume core) : MeasureData a b where
  H0 := d.H0
  W := d.W
  V := d.V
  core := core
  hW := d.hW
  hVb := d.hVb
  hVW := d.hVW
  hfreq := d.hfreq
  hcore := hcore
  hcoreV := hcoreV
  hvol := hvol
  P0 := d.P0
  Omega := d.Omega
  beta := d.beta
  tau := pgTau a b
  lambda0 := 1
  mu1 := pgMu1 d
  LN := (pgAnalytic d).LN
  LB := (pgAnalytic d).LB
  Lg := pgInverseL d
  Ry := pgInverseR d
  hRy := (pgInverse_spec d).2.1
  hRybound := (pgInverse_spec d).2.2.2.2.2.1
  ha := d.ha
  hb := d.hb
  htau := by unfold pgTau; exact lt_add_of_pos_right _ one_pos
  hlambda0 := one_pos
  hmu1 := pgMu1_pos d
  hLN := (pgAnalytic_spec d).2.2.2.2.2.1
  hLB := (pgAnalytic_spec d).2.2.2.2.2.2.1
  hLg := (pgInverse_spec d).1
  g := pgInverse d
  hinv := (pgInverse_spec d).2.2.2.2.1
  hglip := (pgInverse_spec d).2.2.2.2.2.2
  small := min_le_right _ _
  N1 := fun mu hmu I hI I' hI' xi hxi =>
    real_N1 d ⟨hmu.1.le, hmu.2.trans (min_le_left _ _)⟩ (hcoreV hI) (hcoreV hI') hxi
  N2 := fun mu hmu I hI xi xi' hxi hxi' =>
    real_N2 d ⟨hmu.1.le, hmu.2.trans (min_le_left _ _)⟩ (hcoreV hI) hxi hxi'
  N3 := fun mu hmu I hI v =>
    real_N3 d ⟨hmu.1.le, hmu.2.trans (min_le_left _ _)⟩ (hcoreV hI) v

/-- Parameter facts of the budget, read off `rstar`, `kh_dyn` and `rK`. -/
theorem budget_facts (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    0 < r ∧ r < 1 ∧ 0 < mu ∧ mu < r^6 ∧ mu ≤ pgMu1 d ∧ 0 < (params d r mu).l1 ∧
    (params d r mu).l1 ≤ r^2/12 ∧ r^2/4 ≤ (params d r mu).ell ∧ 0 < (params d r mu).rK ∧
    (params d r mu).rK < (params d r mu).l1 ∧ (params d r mu).rK < Real.sqrt r ∧
    ENNReal.ofReal (1/2)*volume d.V ≤ volume (innerCore d.V (Real.sqrt r)) ∧
    ENNReal.ofReal (1/4)*volume d.V ≤ volume (checkedCore d r mu) := by
  obtain ⟨-, -, -, -, -, hR6, -, -, -, -, -, hdyn⟩ := (rstar d).choose_spec
  obtain ⟨-, -, -, -, -, -, hl1, hell, -, -, -, -, hrK, -, hv1, hv2⟩ := hdyn r mu h
  have hh := h
  obtain ⟨hr0, hrR, hmu0, hmu0', hmulog⟩ := hh
  have hR1 := (rstar d).choose_spec.2.2.2.1
  have hlog : 1 ≤ Real.log (1/r) := one_le_log_inv hr0 (hrR.trans hR1).le
  have hmur6 : mu < r^6 := by
    refine hmulog.trans_le ?_
    refine div_le_self (by positivity) ?_
    exact Real.one_le_rpow hlog (by have := pgTau_pos a b; positivity)
  have hr1 : r < 1 := by
    exact hrR.trans (rstar d).choose_spec.2.2.2.2.1
  have hl1' := (kh_dyn h).2.2.2.2.1
  have hrKpos : 0 < (params d r mu).rK := by
    rw [params_rK, params_Ehat]
    have := params_rhoHat_pos d hr0 mu
    have := one_le_kam_c1 d
    positivity
  refine ⟨hr0, hr1, hmu0, hmur6, ?_, hl1, hl1', hell, hrKpos, ?_, ?_, hv1, hv2⟩
  · exact le_min hmu0'.le ((hmur6.le.trans (pow_le_pow_left₀ hr0.le hrR.le 6)).trans hR6)
  · exact (lt_min_iff.1 hrK).2
  · exact (lt_min_iff.1 hrK).1

theorem measure_c1_nonneg (d : PGData a b) {core : Set (Fin a → ℝ)} (hcore : IsCompact core)
    (hcoreV : core ⊆ d.V) (hvol : 0 < volume core) :
    0 ≤ measure_c1 (pgMeasureData d core hcore hcoreV hvol) := by
  unfold measure_c1 pgMeasureData
  dsimp only
  have hS : 0 ≤ latticeS (a+b) (pgTau a b) :=
    latticeS_nonneg (by unfold pgTau; exact lt_add_of_pos_right _ one_pos)
  have := (pgInverse_spec d).2.1
  have := (pgInverse_spec d).1
  refine mul_nonneg (div_nonneg (by positivity) ENNReal.toReal_nonneg)
    (le_max_of_le_left ?_)
  positivity

theorem measure_c1_le (d : PGData a b) {core : Set (Fin a → ℝ)} (hcore : IsCompact core)
    (hcoreV : core ⊆ d.V) (hvol : 0 < volume core)
    (hhalf : ENNReal.ofReal (1/2) * volume d.V ≤ volume core) :
    measure_c1 (pgMeasureData d core hcore hcoreV hvol) ≤ pgMeasureUpper1 d := by
  have hvV := volume_V_pos d
  have hvt : volume d.V ≠ ⊤ := d.hVb.measure_lt_top.ne
  have hc : (volume d.V).toReal/2 ≤ (volume core).toReal := by
    have h := ENNReal.toReal_mono (ne_top_of_le_ne_top hvt (measure_mono hcoreV)) hhalf
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h
    linarith
  have hcpos : 0 < (volume core).toReal :=
    ENNReal.toReal_pos hvol.ne' (ne_top_of_le_ne_top hvt (measure_mono hcoreV))
  unfold measure_c1 pgMeasureUpper1 pgMeasureData
  dsimp only
  have hM : 0 ≤ max (4*(2*pgInverseR d)^(a-1)*latticeS (a+b) (pgTau a b))
      (4*(b:ℝ)^2*(pgAnalytic d).LB*(2*pgInverseR d)^a *
        (2*3^(a+b-1)/(pgTau a b+1-(a+b:ℕ))) *
        (4*(pgAnalytic d).LN*pgInverseL d)^(pgTau a b+1-(a+b:ℕ))) := by
    refine le_max_of_le_left ?_
    have hS : 0 ≤ latticeS (a+b) (pgTau a b) :=
      latticeS_nonneg (by unfold pgTau; exact lt_add_of_pos_right _ one_pos)
    have := (pgInverse_spec d).2.1
    positivity
  have hL := (pgInverse_spec d).1
  gcongr

end KAM.Planetary

end
