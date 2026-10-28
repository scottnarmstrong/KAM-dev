/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.CellTransfer
public import KAM.Planetary.PGAssembly.ActionBudget
public import KAM.Planetary.PGMeasure.Polar

/-!
# P Part 5: the lower bound on the surviving tori (`bpP:p5:lower`)

`pgLoss` is the exact constant `C_*` of `bpP:p5:lower`, a data-only sum chosen before `r` and
`mu`; `lower` proves `meas(S ∩ 𝓕) ≥ (1 - C_* √r) meas 𝓕`. The proof follows the source steps:
`stepP:p5:lo-setup` (cell transfer and the exact cell volume `disc_measure`),
`stepP:p5:lo-bad` (the bad actions `V \ D`, through the collar and Diophantine loss, and the
shell ends `6 b κ₁ √r`) and `stepP:p5:lo-lost` (the lost tori, `budget`). `finalRadius` is the
data-only shrink of the preliminary radius `pgRstar`. Declarations are copied verbatim from
`P45Signatures.lean`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-LO.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- Exact Closs formula of the blueprint, with data-only selected component bounds. -/
def pgLoss (d : PGData a b) : ℝ :=
  (pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/(volume d.V).toReal +
    6*b*(pgScales d).k1 + kamMeasureConstant (a+b)*pgBudget d

private theorem lo_volume_unitCube (n : ℕ) : volume (unitCube n) = 1 := by
  rw [unitCube, volume_pi_pi]
  simp

/-- `stepP:p5:lo-bad`, action side: the checked core misses at most `(A + C_dio C_γ) √r` of `V`. -/
private theorem lo_core_bad (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    volume d.V ≤ volume (checkedCore d r mu) +
      ENNReal.ofReal ((pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)*Real.sqrt r) := by
  obtain ⟨hr0, hr1, -, -, -, -, -, -, -, -, -, -, -⟩ := budget_facts d h
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  obtain ⟨hA0, hD0, hcl⟩ := pgBoundary_spec d
  have hcol := collar d.hV d.hVb hcl
  have hRD : Real.sqrt r < pgBoundaryD d := by
    have := (rstar d).choose_spec.2.2.2.2.2.2.2.2.1
    exact lt_of_lt_of_le (Real.sqrt_lt_sqrt hr0.le h.2.1) this.le
  have h1 := (hcol.2.1 (Real.sqrt r) hsq hRD).1
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
  have hsub : d.V \ checkedCore d r mu ⊆ (d.V \ innerCore d.V (Real.sqrt r)) ∪
      {I ∈ d.V | ¬ KAM.IsDiophantine (params d r mu).gammaBar ((a+b:ℕ)+1)
        (fastFrequency d.H0 I)} := by
    rintro x ⟨hxV, hx⟩
    by_cases hxc : x ∈ innerCore d.V (Real.sqrt r)
    · right
      exact ⟨hxV, fun hdio => hx ⟨hxc, hdio⟩⟩
    · left
      exact ⟨hxV, hxc⟩
  have hA : 0 ≤ pgBoundaryA d*Real.sqrt r := by positivity
  have hC : 0 ≤ (pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r := by
    have := pgCgamma_pos d; positivity
  calc volume d.V ≤ volume (checkedCore d r mu ∪ (d.V \ checkedCore d r mu)) :=
        measure_mono (fun x hx => by
          by_cases hxc : x ∈ checkedCore d r mu
          · exact Or.inl hxc
          · exact Or.inr ⟨hx, hxc⟩)
    _ ≤ volume (checkedCore d r mu) + volume (d.V \ checkedCore d r mu) := measure_union_le _ _
    _ ≤ volume (checkedCore d r mu) + (ENNReal.ofReal (pgBoundaryA d*Real.sqrt r) +
        ENNReal.ofReal ((pgAnalytic d).Cdio*pgCgamma d*Real.sqrt r)) := by
      gcongr
      exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h1 hbad'))
    _ = _ := by
      rw [← ENNReal.ofReal_add hA hC]; congr 2; ring

/-- Elementary inequality: the product of three factors in `[0,1]` beats one minus the sum. -/
private theorem lo_prod_ge {p q w : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hw : 0 ≤ w)
    (hs : p + q + w ≤ 1) : 1 - (p + q + w) ≤ (1 - p) * (1 - q) * (1 - w) := by
  nlinarith [mul_nonneg hp hq, mul_nonneg hp hw, mul_nonneg hq hw, mul_nonneg (mul_nonneg hp hq) hw]

private theorem lo_ell_pow (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    (r^2/2)^b * (1 - 6*b*(pgScales d).k1*Real.sqrt r) ≤ (params d r mu).ell ^ b := by
  obtain ⟨hr0, -, -, -, -, -, hl1', -, -, -, -, -, -⟩ := budget_facts d h
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have h52 : r^(5/2:ℝ) = r^2*Real.sqrt r := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hr0]; norm_num
  have hl : (params d r mu).l1 = (pgScales d).k1*(r^2*Real.sqrt r) := by
    rw [params_l1, h52]
  have hx : (params d r mu).ell = r^2/2 * (1 + (-(6*(pgScales d).k1*Real.sqrt r))) := by
    rw [params_ell, hl]; ring
  have hr2 : 0 < r^2/2 := by positivity
  have hxb : -2 ≤ -(6*(pgScales d).k1*Real.sqrt r) := by
    have : 0 < (params d r mu).l1 := by
      rw [hl]; have := pgScales_k1_pos d; positivity
    have h12 : (params d r mu).l1 ≤ r^2/12 := hl1'
    rw [hl] at h12
    nlinarith
  have hb := one_add_mul_le_pow hxb b
  rw [hx, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc 1 - 6*b*(pgScales d).k1*Real.sqrt r
      = 1 + (b:ℝ) * (-(6*(pgScales d).k1*Real.sqrt r)) := by ring
    _ ≤ _ := hb

theorem lower (d : PGData a b) : 0 < pgLoss d ∧ ∀ r mu : ℝ,
    ∀ h : admissible d (pgRstar d) r mu,
      ENNReal.ofReal (1-pgLoss d*Real.sqrt r)*volume (cylinderCell (b:=b) d.V r) ≤
        volume (kset d r mu h (pgD0 d r mu) ∩ cylinderCell d.V r) := by
  have hv := volume_V_pos d
  have hk1 := pgScales_k1_pos d
  have hbud := budget d
  have hcn : 0 < kamMeasureConstant (a+b) := by unfold kamMeasureConstant; positivity
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast d.hb
  have hA := (pgBoundary_spec d).1
  have hCd := (pgAnalytic_spec d).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCg := pgCgamma_pos d
  have hX : 0 < (pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/(volume d.V).toReal := by
    positivity
  refine ⟨?_, fun r mu h => ?_⟩
  · unfold pgLoss
    have := hbud.1
    positivity
  obtain ⟨hr0, hr1, -, -, -, -, -, hell, -, -, -, -, -⟩ := budget_facts d h
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  set s := Real.sqrt r with hs
  set c := pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d with hc
  set X := c/(volume d.V).toReal with hXdef
  set κ := kamMeasureConstant (a+b)*pgBudget d with hκ
  have hκ0 : 0 < κ := mul_pos hcn hbud.1
  have hc0 : 0 < c := by positivity
  set C := pgLoss d with hC
  have hCeq : C = X + 6*b*(pgScales d).k1 + κ := rfl
  -- cell transfer and exact cell volume
  obtain ⟨-, -, -, hvol⟩ := cell_transfer d r mu h (fam_isSigmaCompact_D0 h) (fun _ hJ => hJ)
  have hVm : MeasurableSet d.V := d.hV.measurableSet
  have hcell := (disc_measure (b := b) hVm hr0).1
  rw [hvol, hcell]
  have hVfin : volume d.V ≠ ⊤ := d.hVb.measure_lt_top.ne
  have hVr : volume d.V = ENNReal.ofReal (volume d.V).toReal := (ENNReal.ofReal_toReal hVfin).symm
  set v := (volume d.V).toReal with hvdef
  by_cases hRep : volume (outputRepresentative d r mu h (pgD0 d r mu)) = ⊤
  · rw [hRep, ENNReal.mul_top (by simp; positivity)]
    exact le_top
  by_cases hCs : 1 - C*s < 0
  · rw [ENNReal.ofReal_of_nonpos hCs.le, zero_mul]
    exact zero_le
  push Not at hCs
  have hCs1 : C*s ≤ 1 := by linarith
  -- the budget
  have hbd := hbud.2 r mu h
  set D := pgActionDomain d r mu with hD
  set Rep := outputRepresentative d r mu h (pgD0 d r mu) with hRepdef
  obtain ⟨-, -, -, hDpos, hDfin⟩ := (param_facts d).2 r mu h
  have hQ : {z : Phase (a+b) | z.2 ∈ D ∧ z.1 ∈ unitCube (a+b)} = unitCube (a+b) ×ˢ D := by
    ext z; simp [and_comm]
  have hQvol : volume {z : Phase (a+b) | z.2 ∈ D ∧ z.1 ∈ unitCube (a+b)} = volume D := by
    rw [hQ, Measure.volume_eq_prod, Measure.prod_prod, lo_volume_unitCube, one_mul]
  have hsplit : volume D ≤ volume Rep + ENNReal.ofReal (κ*s) * volume D := by
    refine hQvol.symm.le.trans (le_trans (measure_mono (t := Rep ∪
      (({z : Phase (a+b) | z.2 ∈ D ∧ z.1 ∈ unitCube (a+b)}) \
        rawUnion d r mu h (pgD0 d r mu))) (fun z hz => by
          by_cases hzr : z ∈ rawUnion d r mu h (pgD0 d r mu)
          · exact Or.inl ⟨hzr, hz.2⟩
          · exact Or.inr ⟨hz, hzr⟩))
      ((measure_union_le _ _).trans (add_le_add le_rfl hbd)))
  -- pass to reals
  set R := (volume Rep).toReal with hRdef
  have hDr : volume D = ENNReal.ofReal (volume D).toReal := (ENNReal.ofReal_toReal hDfin.ne).symm
  have hκs0 : 0 ≤ κ*s := mul_nonneg hκ0.le hsq.le
  have hDR : (volume D).toReal ≤ R + κ*s*(volume D).toReal := by
    have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hRep, ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top hDfin.ne⟩) hsplit
    rwa [ENNReal.toReal_add hRep (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hκs0] at h'
  -- the measure of the action domain
  have hXsub : checkedCore d r mu ⊆ d.V := checkedCore_subset_V d r mu
  have hXfin : volume (checkedCore d r mu) ≠ ⊤ := (lt_of_le_of_lt (measure_mono hXsub)
    d.hVb.measure_lt_top).ne
  have hDvol : (volume D).toReal = (volume (checkedCore d r mu)).toReal *
      (params d r mu).ell ^ b := by
    rw [hD, volume_pgActionDomain d h, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (pow_nonneg (le_trans (by positivity) hell) _)]
  have hm : v - c*s ≤ (volume (checkedCore d r mu)).toReal := by
    have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hXfin, ENNReal.ofReal_ne_top⟩)
      (lo_core_bad d h)
    have hc' : 0 ≤ c*s := by positivity
    rw [ENNReal.toReal_add hXfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc'] at h'
    linarith
  have hell0 : 0 < (params d r mu).ell := lt_of_lt_of_le (by positivity) hell
  have hLb := lo_ell_pow d h
  -- the sizes
  have hw6 : 0 < 6*b*(pgScales d).k1 := by positivity
  have hXs0 : 0 ≤ X*s := mul_nonneg hX.le hsq.le
  have hw0 : 0 ≤ 6*b*(pgScales d).k1*s := mul_nonneg hw6.le hsq.le
  have hCsum : C*s = X*s + 6*b*(pgScales d).k1*s + κ*s := by rw [hCeq]; ring
  have hXs : X*s ≤ 1 := by linarith
  have hXm : v*(1 - X*s) ≤ (volume (checkedCore d r mu)).toReal := by
    have : v*(X*s) = c*s := by rw [hXdef]; field_simp
    linarith
  have hP : 0 < (r^2/2)^b := by positivity
  have hRlow : (1 - κ*s) * (v*(1 - X*s)) * ((r^2/2)^b*(1 - 6*b*(pgScales d).k1*s)) ≤ R := by
    have h1 : (1 - κ*s) * (volume D).toReal ≤ R := by nlinarith
    refine le_trans ?_ h1
    rw [hDvol]
    have hm0 : 0 ≤ v*(1 - X*s) := mul_nonneg hv.le (by linarith)
    have hw1 : 0 ≤ (r^2/2)^b*(1 - 6*b*(pgScales d).k1*s) := mul_nonneg hP.le (by linarith)
    calc (1 - κ*s) * (v*(1 - X*s)) * ((r^2/2)^b*(1 - 6*b*(pgScales d).k1*s))
        = (1 - κ*s) * ((v*(1 - X*s)) * ((r^2/2)^b*(1 - 6*b*(pgScales d).k1*s))) := by ring
      _ ≤ (1 - κ*s) * ((volume (checkedCore d r mu)).toReal * (params d r mu).ell ^ b) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact mul_le_mul hXm hLb hw1 ENNReal.toReal_nonneg
  have hprod := lo_prod_ge (p := X*s) (q := 6*b*(pgScales d).k1*s) (w := κ*s)
    hXs0 hw0 hκs0 (by linarith)
  have hfin : (1 - C*s) * (v * (r^2/2)^b) ≤ R := by
    have : 1 - (X*s + 6*b*(pgScales d).k1*s + κ*s) = 1 - C*s := by rw [hCeq]; ring
    rw [this] at hprod
    have h2 : (1 - C*s) * (v * (r^2/2)^b) ≤
        (1 - X*s) * (1 - 6*b*(pgScales d).k1*s) * (1 - κ*s) * (v*(r^2/2)^b) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine le_trans (le_trans h2 (le_of_eq ?_)) hRlow
    ring
  -- conclude in ENNReal
  have hRr : volume Rep = ENNReal.ofReal R := (ENNReal.ofReal_toReal hRep).symm
  rw [hRr, hVr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpi : 0 < (2*Real.pi)^(a+b) := by positivity
  calc (1 - C*s) * ((2*Real.pi)^(a+b)*(r^2/2)^b * v)
      = (2*Real.pi)^(a+b) * ((1 - C*s) * (v * (r^2/2)^b)) := by ring
    _ ≤ (2*Real.pi)^(a+b) * R := mul_le_mul_of_nonneg_left hfin hpi.le

def finalRadius (d : PGData a b) : ℝ := min (pgRstar d) (((2*(pgLoss d+1))⁻¹)^2)

end KAM.Planetary

end
