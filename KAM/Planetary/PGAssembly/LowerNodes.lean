/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Lower
public import KAM.Planetary.PGMeasure.Collar

/-!
# P Part 5: literal exports of the lower-bound steps (GAP-P5b)

Append-only exports stating the literal conclusions of `stepP:p5:lo-bad` (`lo_bad_ratio`),
`stepP:p5:lo-lost` (`lo_lost_budget`) and `stepP:p4:dc-prod` (`dc_prod_node`). The private
helpers of `Lower.lean` that these steps need are re-proved privately here.
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

private theorem lbn_volume_unitCube (n : ℕ) : volume (unitCube n) = 1 := by
  rw [unitCube, volume_pi_pi]
  simp

/-- The checked core misses at most `(A + C_dio C_γ) √r` of `V` (`stepP:p5:lo-bad`, action side). -/
private theorem lbn_core_bad (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
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

/-- Bernoulli bound for the shell side length (`stepP:p5:lo-bad`, shell ends). -/
private theorem lbn_ell_pow (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
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

/-- `stepP:p5:lo-bad`: the relative loss of the action domain `D = Ď × A_sh` against
`V × (0, λ₂)^b`, in the ratio form of the source, with `λ₂ = (params d r mu).l2`. -/
theorem lo_bad_ratio (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    ((volume d.V).toReal * (params d r mu).l2 ^ b -
        (volume (pgActionDomain d r mu)).toReal) /
      ((volume d.V).toReal * (params d r mu).l2 ^ b) ≤
    ((pgBoundaryA d + (pgAnalytic d).Cdio * pgCgamma d) / (volume d.V).toReal +
      6 * b * (pgScales d).k1) * Real.sqrt r := by
  have hv := volume_V_pos d
  have hk1 := pgScales_k1_pos d
  have hCg := pgCgamma_pos d
  have hA := (pgBoundary_spec d).1
  have hCd := (pgAnalytic_spec d).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hr0, -, -, -, -, -, -, hell, -, -, -, -, -⟩ := budget_facts d h
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg b
  have hl2 : (params d r mu).l2 = r^2/2 := rfl
  rw [hl2]
  set s := Real.sqrt r with hs
  set v := (volume d.V).toReal with hvdef
  set c := pgBoundaryA d + (pgAnalytic d).Cdio * pgCgamma d with hc
  set w := 6 * (b:ℝ) * (pgScales d).k1 with hw
  have hc0 : 0 < c := by positivity
  have hw0 : 0 ≤ w := by positivity
  set P := (r^2/2)^b with hP
  have hP0 : 0 < P := by positivity
  set core := (volume (checkedCore d r mu)).toReal with hcore
  have hXsub : checkedCore d r mu ⊆ d.V := checkedCore_subset_V d r mu
  have hXfin : volume (checkedCore d r mu) ≠ ⊤ := (lt_of_le_of_lt (measure_mono hXsub)
    d.hVb.measure_lt_top).ne
  have hDvol : (volume (pgActionDomain d r mu)).toReal = core * (params d r mu).ell ^ b := by
    rw [volume_pgActionDomain d h, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (pow_nonneg (le_trans (by positivity) hell) _)]
  have hcv : core ≤ v := ENNReal.toReal_mono d.hVb.measure_lt_top.ne (measure_mono hXsub)
  have hm : v - c*s ≤ core := by
    have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hXfin, ENNReal.ofReal_ne_top⟩)
      (lbn_core_bad d h)
    have hc' : 0 ≤ c*s := by positivity
    rw [ENNReal.toReal_add hXfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc'] at h'
    linarith
  have hLb : P*(1 - w*s) ≤ (params d r mu).ell ^ b := by
    have := lbn_ell_pow d h
    rw [hP, hw, hs]; convert this using 2
  have hcore0 : 0 ≤ core := ENNReal.toReal_nonneg
  set m := max (v - c*s) 0 with hmdef
  have hm1 : v - c*s ≤ m := le_max_left _ _
  have hm0 : 0 ≤ m := le_max_right _ _
  have hmc : m ≤ core := max_le hm hcore0
  have hws : 0 ≤ w*s := by positivity
  have hell0 : 0 ≤ (params d r mu).ell ^ b := pow_nonneg (le_trans (by positivity) hell) _
  have hmv : m ≤ v := max_le (by nlinarith [mul_nonneg hc0.le hsq.le]) hv.le
  have h1 : m * (P*(1 - w*s)) ≤ core * (params d r mu).ell ^ b :=
    (mul_le_mul_of_nonneg_left hLb hm0).trans (mul_le_mul hmc le_rfl hell0 hcore0)
  have h2 : v*P - core * (params d r mu).ell ^ b ≤ P*(c*s + v*w*s) := by
    have e : m * (P*(1 - w*s)) = P*(m - m*(w*s)) := by ring
    have h3 : m*(w*s) ≤ v*(w*s) := mul_le_mul_of_nonneg_right hmv hws
    nlinarith
  rw [hDvol, div_le_iff₀ (by positivity)]
  have e : ((c / v + w) * s) * (v * P) = P*(c*s + v*w*s) := by
    field_simp
  rw [e]
  exact h2

/-- `stepP:p5:lo-lost`, in the `(angle, action)` coordinates of `Phase`: the cell
`D × [0,1)^n` minus the output representative `L` of the surviving tori has measure
`≤ c_n C_b √r meas D`, and `meas D ≤ meas F'` for the cell `F' = V × (0, λ₂)^b × [0,1)^n`;
hence the same bound holds with `meas F'` in place of `meas D`. -/
theorem lo_lost_budget (d : PGData a b) {r mu : ℝ} (h : admissible d (pgRstar d) r mu) :
    volume ({z : Phase (a+b) | z.2 ∈ pgActionDomain d r mu ∧ z.1 ∈ unitCube (a+b)} \
        outputRepresentative d r mu h (pgD0 d r mu)) ≤
      ENNReal.ofReal (kamMeasureConstant (a+b) * pgBudget d * Real.sqrt r) *
        volume (pgActionDomain d r mu) ∧
    volume (pgActionDomain d r mu) ≤
      volume {z : Phase (a+b) | blockFast z.2 ∈ d.V ∧
        blockSlow z.2 ∈ actionShell b 0 (r^2/2) ∧ z.1 ∈ unitCube (a+b)} ∧
    volume ({z : Phase (a+b) | z.2 ∈ pgActionDomain d r mu ∧ z.1 ∈ unitCube (a+b)} \
        outputRepresentative d r mu h (pgD0 d r mu)) ≤
      ENNReal.ofReal (kamMeasureConstant (a+b) * pgBudget d * Real.sqrt r) *
        volume {z : Phase (a+b) | blockFast z.2 ∈ d.V ∧
          blockSlow z.2 ∈ actionShell b 0 (r^2/2) ∧ z.1 ∈ unitCube (a+b)} := by
  obtain ⟨hr0, -, -, -, -, hl1, -, -, -, -, -, -, -⟩ := budget_facts d h
  set Q := {z : Phase (a+b) | z.2 ∈ pgActionDomain d r mu ∧ z.1 ∈ unitCube (a+b)} with hQ
  set F := {z : Phase (a+b) | blockFast z.2 ∈ d.V ∧
    blockSlow z.2 ∈ actionShell b 0 (r^2/2) ∧ z.1 ∈ unitCube (a+b)} with hF
  have hdiff : Q \ outputRepresentative d r mu h (pgD0 d r mu) ⊆
      Q \ rawUnion d r mu h (pgD0 d r mu) := by
    rintro z ⟨hz, hn⟩
    exact ⟨hz, fun hr => hn ⟨hr, hz.2⟩⟩
  have h1 : volume (Q \ outputRepresentative d r mu h (pgD0 d r mu)) ≤
      ENNReal.ofReal (kamMeasureConstant (a+b) * pgBudget d * Real.sqrt r) *
        volume (pgActionDomain d r mu) :=
    (measure_mono hdiff).trans ((budget d).2 r mu h)
  have hQ' : Q = unitCube (a+b) ×ˢ pgActionDomain d r mu := by
    ext z; simp [hQ, and_comm]
  have hQvol : volume Q = volume (pgActionDomain d r mu) := by
    rw [hQ', Measure.volume_eq_prod, Measure.prod_prod, lbn_volume_unitCube, one_mul]
  have hQF : Q ⊆ F := by
    rintro z ⟨hz2, hz1⟩
    obtain ⟨⟨⟨hV, -⟩, -⟩, hsh⟩ := hz2
    refine ⟨hV, fun j _ => ?_, hz1⟩
    have hj := hsh j (mem_univ j)
    have := params_l2top d r mu
    have hl : (params d r mu).l2top ≤ r^2/2 := by
      rw [this]; linarith [(budget_facts d h).2.2.2.2.2.2.2.1]
    exact ⟨by linarith [hj.1], by linarith [hj.2]⟩
  have h2 : volume (pgActionDomain d r mu) ≤ volume F := hQvol ▸ measure_mono hQF
  exact ⟨h1, h2, h1.trans (by gcongr)⟩

/-- Coordinatewise real neighbourhood of an open interval. -/
private theorem dcn_nbhd_Ioo {l u s y : ℝ} (hlu : l < u) (hs : 0 < s) :
    (∃ x ∈ Ioo l u, |y - x| < s) ↔ y ∈ Ioo (l - s) (u + s) := by
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, h3⟩
    rw [abs_lt] at h3
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    by_cases hy1 : y ≤ l
    · refine ⟨l + min ((u - l)/2) ((s - (l - y))/2), ⟨?_, ?_⟩, ?_⟩
      · have : 0 < min ((u - l)/2) ((s - (l - y))/2) := lt_min (by linarith) (by linarith)
        linarith
      · linarith [min_le_left ((u - l)/2) ((s - (l - y))/2)]
      · have h3 := min_le_right ((u - l)/2) ((s - (l - y))/2)
        have h4 : 0 < min ((u - l)/2) ((s - (l - y))/2) := lt_min (by linarith) (by linarith)
        rw [abs_lt]; constructor <;> linarith
    · by_cases hy2 : u ≤ y
      · refine ⟨u - min ((u - l)/2) ((s - (y - u))/2), ⟨?_, ?_⟩, ?_⟩
        · linarith [min_le_left ((u - l)/2) ((s - (y - u))/2)]
        · have : 0 < min ((u - l)/2) ((s - (y - u))/2) := lt_min (by linarith) (by linarith)
          linarith
        · have h3 := min_le_right ((u - l)/2) ((s - (y - u))/2)
          have h4 : 0 < min ((u - l)/2) ((s - (y - u))/2) := lt_min (by linarith) (by linarith)
          rw [abs_lt]; constructor <;> linarith
      · push Not at hy1 hy2
        exact ⟨y, ⟨hy1, hy2⟩, by simpa using hs⟩

private theorem dcn_nbhd_shell {b : ℕ} {l u s : ℝ} (hlu : l < u) (hs : 0 < s) :
    realNbhd (actionShell b l u) s = actionShell b (l - s) (u + s) := by
  ext y
  simp only [realNbhd, actionShell, mem_pi, mem_univ, true_imp_iff, mem_Ioo]
  constructor
  · rintro ⟨x, hx, hd⟩
    rw [dist_pi_lt_iff hs] at hd
    intro i
    have := (dcn_nbhd_Ioo hlu hs (y := y i)).1 ⟨x i, hx i, by simpa [Real.dist_eq] using hd i⟩
    exact this
  · intro hy
    choose x hx hxd using fun i => (dcn_nbhd_Ioo hlu hs (y := y i)).2 (hy i)
    refine ⟨x, hx, ?_⟩
    rw [dist_pi_lt_iff hs]
    intro i
    simpa [Real.dist_eq] using hxd i

/-- `stepP:p4:dc-prod`: for `0 < t < d` and `0 < r_K < min {t, λ₁}` (and `λ₁ < λ₂`), the real
neighbourhood of `D = D_t × A_sh` is the product of the real neighbourhoods, and it lies in
`V × (0,∞)^b`. -/
theorem dc_prod_node {V : Set (Fin a → ℝ)} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {A d : ℝ}
    (hc : ∀ s : ℝ, 0 < s → s < d →
      volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < s} ≤ ENNReal.ofReal (A*s))
    {t rK l1 l2 : ℝ} (_ht : 0 < t) (_htd : t < d) (hrK : 0 < rK) (hrKt : rK < t)
    (hrKl : rK < l1) (hl : l1 < l2) :
    realNbhd (joinedActions (innerCore V t) (actionShell b l1 l2)) rK =
      joinedActions (realNbhd (innerCore V t) rK) (actionShell b (l1 - rK) (l2 + rK)) ∧
    joinedActions (realNbhd (innerCore V t) rK) (actionShell b (l1 - rK) (l2 + rK)) ⊆
      joinedActions V (pi univ fun _ : Fin b => Ioi (0:ℝ)) := by
  have hcol := collar hV hVb hc
  have hN := (hcol.2.2.1 t rK hrK hrKt).1
  have heq : realNbhd (joinedActions (innerCore V t) (actionShell b l1 l2)) rK =
      joinedActions (realNbhd (innerCore V t) rK) (actionShell b (l1 - rK) (l2 + rK)) := by
    rw [realNbhd_joinedActions, dcn_nbhd_shell hl hrK]
  refine ⟨heq, ?_⟩
  rintro J ⟨h1, h2⟩
  refine ⟨hN h1, fun j _ => ?_⟩
  have := h2 j (mem_univ j)
  exact lt_trans (by linarith) this.1

end KAM.Planetary

end
