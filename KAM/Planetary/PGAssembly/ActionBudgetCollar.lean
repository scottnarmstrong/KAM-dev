/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ActionBudgetDio

/-!
# P Part 5: the collar part of the budget (`stepP:p5:bu-collar`)

The enlargement `N_{rK}(D) \ D` of the Cantor domain `D = checkedCore × shell` is bounded through
`domain_collar_helper`: the fast part is controlled by the boundary collar of the inner core
(`collar`) and the Diophantine loss `dio_one`-type estimate `pgAnalytic_dio`, the slow part by the
relative enlargement of the shell (`r_k`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-BU.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

theorem one_add_pow_sub_one_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1+x)^n - 1 ≤ n*x*(1+x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ (1+x)^(n+1) := one_le_pow₀ (by linarith)
    have h2 : (1+x)^(n+1) = (1+x)*(1+x)^n := pow_succ' _ _
    push_cast
    nlinarith [mul_nonneg hx (sub_nonneg.2 h1), mul_nonneg hx (by positivity : (0:ℝ) ≤ (1+x)^n),
      mul_nonneg (mul_nonneg hx (Nat.cast_nonneg n)) (by positivity : (0:ℝ) ≤ (1+x)^n)]

theorem checkedCore_isClosed (d : PGData a b) (r mu : ℝ) (hr : 0 < r) :
    IsClosed (checkedCore d r mu) := by
  obtain ⟨hA0, hD0, hcl⟩ := pgBoundary_spec d
  have hcol := collar d.hV d.hVb hcl
  have hcomp := (hcol.1 _ (Real.sqrt_pos.2 hr)).1
  have hcont : ContinuousOn (fastFrequency d.H0) (innerCore d.V (Real.sqrt r)) :=
    (pgInverse_spec d).2.2.1.mono ((hcol.1 _ (Real.sqrt_pos.2 hr)).2.1.trans
      (subset_closure.trans d.hVW))
  exact hcont.preimage_isClosed_of_isClosed hcomp.isClosed (fam_isClosed_dio a _ _)

theorem budget_collar_fast (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    volume (realNbhd (checkedCore d r mu) (params d r mu).rK \ checkedCore d r mu) ≤
      ENNReal.ofReal ((pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)*Real.sqrt r) := by
  obtain ⟨hr0, hr1, hmu0, hmur6, hmu1, hl1, hl1', hell, hrK0, hrKl, hrKs, -, -⟩ :=
    budget_facts d h
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  obtain ⟨hA0, hD0, hcl⟩ := pgBoundary_spec d
  have hcol := collar d.hV d.hVb hcl
  have hRD : Real.sqrt r < pgBoundaryD d := by
    have := (rstar d).choose_spec.2.2.2.2.2.2.2.2.1
    exact lt_of_lt_of_le (Real.sqrt_lt_sqrt hr0.le h.2.1) this.le
  have h1 := (hcol.2.2.2 (Real.sqrt r) (params d r mu).rK hrK0 hrKs hRD)
  have hbad := pgAnalytic_dio d (params d r mu).gammaBar
    (gammaBar_pos hr0 (h.2.1.trans (rstar d).choose_spec.2.2.2.1).le mu)
  have hg := (param_facts d).2 r mu h
  have hCd := (pgAnalytic_spec d).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbad' : volume {I ∈ d.V | ¬ KAM.IsDiophantine (params d r mu).gammaBar
      ((a+b:ℕ)+1) (fastFrequency d.H0 I)} ≤
      ENNReal.ofReal ((pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r) := by
    refine hbad.trans (ENNReal.ofReal_le_ofReal ?_)
    calc (pgAnalytic d).Cdio*(params d r mu).gammaBar
        ≤ (pgAnalytic d).Cdio*(pgCgamma d*Real.sqrt r) :=
          mul_le_mul_of_nonneg_left hg.2.2.1 hCd.le
      _ = _ := by ring
  have hsub : realNbhd (checkedCore d r mu) (params d r mu).rK \ checkedCore d r mu ⊆
      (realNbhd (innerCore d.V (Real.sqrt r)) (params d r mu).rK \ innerCore d.V (Real.sqrt r)) ∪
        {I ∈ d.V | ¬ KAM.IsDiophantine (params d r mu).gammaBar ((a+b:ℕ)+1)
          (fastFrequency d.H0 I)} := by
    rintro x ⟨⟨y, hy, hxy⟩, hx⟩
    by_cases hxc : x ∈ innerCore d.V (Real.sqrt r)
    · right
      refine ⟨hxc.1, fun hdio => hx ⟨hxc, hdio⟩⟩
    · left
      exact ⟨⟨y, hy.1, hxy⟩, hxc⟩
  have hA : 0 ≤ pgBoundaryA d*Real.sqrt r := by positivity
  have hC : 0 ≤ (pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r := by
    have := pgCgamma_pos d; positivity
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (pgBoundaryA d*Real.sqrt r) +
        ENNReal.ofReal ((pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r) := add_le_add h1 hbad'
    _ = _ := by rw [← ENNReal.ofReal_add hA hC]; congr 1; ring

theorem budget_collar (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    volume (realNbhd (pgActionDomain d r mu) (params d r mu).rK \ pgActionDomain d r mu) ≤
      ENNReal.ofReal ((8*(pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/(volume d.V).toReal +
        b*(pgScales d).k1/16)*Real.sqrt r) * volume (pgActionDomain d r mu) := by
  obtain ⟨hr0, hr1, hmu0, hmur6, hmu1, hl1, hl1', hell, hrK0, hrKl, hrKs, -, hquart⟩ :=
    budget_facts d h
  obtain ⟨-, hx, hxb⟩ := r_k d r mu h
  set p := params d r mu with hp
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hell0 : 0 < p.ell := lt_of_lt_of_le (by positivity) hell
  have hlu : p.l1 < p.l2top := by rw [params_l2top]; rw [params_ell] at hell0; linarith
  have hul : p.l2top - p.l1 = p.ell := by rw [params_l2top, params_ell]; ring
  have hXm : MeasurableSet (checkedCore d r mu) := (checkedCore_isClosed d r mu hr0).measurableSet
  have hXsub : checkedCore d r mu ⊆ d.V :=
    (checkedCore_subset d r mu).trans
      ((collar d.hV d.hVb (pgBoundary_spec d).2.2).1 _ hsq).2.1
  have hXfin : volume (checkedCore d r mu) < ⊤ :=
    lt_of_le_of_lt (measure_mono hXsub) d.hVb.measure_lt_top
  have hcoll := domain_collar_helper (b := b) hXm hl1 hlu hrK0 hrKl hXfin (budget_collar_fast d h)
  rw [hul] at hcoll
  have hV := volume_V_pos d
  have hvt : volume d.V ≠ ⊤ := d.hVb.measure_lt_top.ne
  have hXr : volume (checkedCore d r mu) = ENNReal.ofReal (volume (checkedCore d r mu)).toReal :=
    (ENNReal.ofReal_toReal hXfin.ne).symm
  have hXq : (volume d.V).toReal/4 ≤ (volume (checkedCore d r mu)).toReal := by
    have h' := ENNReal.toReal_mono hXfin.ne hquart
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at h'
    linarith
  set c := pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d with hc
  have hc0 : 0 < c := by
    have := (pgBoundary_spec d).1
    have := (pgAnalytic_spec d).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have := pgCgamma_pos d
    positivity
  set x := 2*p.rK/p.ell with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hexp : (p.ell+2*p.rK)^b = p.ell^b*(1+x)^b := by
    rw [← mul_pow]; congr 1; rw [hxdef]; field_simp
  have hk1 := pgScales_k1_pos d
  have hn : (1:ℝ) ≤ ((a+b:ℕ):ℝ) := by
    have := d.ha; exact_mod_cast (by omega : 1 ≤ a+b)
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast d.hb
  have hellb : 0 < p.ell^b := pow_pos hell0 b
  -- the fast term
  have hA : c*Real.sqrt r*(p.ell+2*p.rK)^b ≤
      8*c/(volume d.V).toReal*Real.sqrt r*((volume (checkedCore d r mu)).toReal*p.ell^b) := by
    rw [hexp]
    calc c*Real.sqrt r*(p.ell^b*(1+x)^b) ≤ c*Real.sqrt r*(p.ell^b*2) := by gcongr
      _ = 8*c/(volume d.V).toReal*Real.sqrt r*(((volume d.V).toReal/4)*p.ell^b) := by
          field_simp; ring
      _ ≤ _ := by gcongr
  -- the slow term
  have hB : (p.ell+2*p.rK)^b - p.ell^b ≤ (b*(pgScales d).k1/16*Real.sqrt r)*p.ell^b := by
    rw [hexp]
    have h1 := one_add_pow_sub_one_le hx0 b
    have h2 : (1+x)^b - 1 ≤ 2*b*x := by
      have : (b:ℝ)*x*(1+x)^b ≤ b*x*2 := by gcongr
      linarith
    have h3 : 2*(b:ℝ)*x ≤ b*(pgScales d).k1/16*Real.sqrt r := by
      calc 2*(b:ℝ)*x ≤ 2*b*((pgScales d).k1/(64*((a+b:ℕ):ℝ))*Real.sqrt r) := by gcongr
        _ ≤ 2*b*((pgScales d).k1/(64*1)*Real.sqrt r) := by gcongr
        _ ≤ _ := by nlinarith [mul_pos hk1 hsq]
    calc p.ell^b*(1+x)^b - p.ell^b = p.ell^b*((1+x)^b - 1) := by ring
      _ ≤ p.ell^b*(b*(pgScales d).k1/16*Real.sqrt r) := by gcongr; linarith
      _ = _ := by ring
  have hRA : ENNReal.ofReal ((pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)*Real.sqrt r*
      (p.ell+2*p.rK)^b) ≤ ENNReal.ofReal (8*c/(volume d.V).toReal*Real.sqrt r) *
        (volume (checkedCore d r mu) * ENNReal.ofReal (p.ell^b)) := by
    rw [hXr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hA
  have hRB : volume (checkedCore d r mu) * ENNReal.ofReal ((p.ell+2*p.rK)^b - p.ell^b) ≤
      ENNReal.ofReal (b*(pgScales d).k1/16*Real.sqrt r) *
        (volume (checkedCore d r mu) * ENNReal.ofReal (p.ell^b)) := by
    calc _ ≤ volume (checkedCore d r mu) *
          ENNReal.ofReal ((b*(pgScales d).k1/16*Real.sqrt r)*p.ell^b) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hB)
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ring
  rw [volume_pgActionDomain d h]
  calc _ ≤ _ := hcoll
    _ ≤ _ := add_le_add hRA hRB
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2; ring

end KAM.Planetary

end
