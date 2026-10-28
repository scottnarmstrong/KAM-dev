/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.PlanarTorsion.PairJet.Defs
public import KAM.Planetary.SecularForm.Analytic
public import KAM.Planetary.SecularForm.Symmetry

/-!
# Planar quartic torsion: the pair average as a Part-8 secular average

Blueprint P, Part 11b (`stepP:p11b:pj-formal`, via `bpP:p8:perturbation-analytic` and symmetry (S1)
of `bpP:p8:symmetries`): for the data `G = m₀ = m₁ = m₂ = 1` and the axes `(a, 1)`, the fixed-center
secular average of Part 8, evaluated at the slow variable `x(z)` whose regular eccentricity vectors are
`z`, is `-p11c_pairAverage a z`.  Hence `p11c_pairAverage a` is real analytic at `0` and even.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function KAM KAM.Kepler
open scoped Topology ContDiff
namespace KAM.Planetary
open SecularForm

/-- Unit constants and two unit masses. -/
def p11cPJD : Data 2 := ⟨1, 1, fun _ => 1, one_pos, one_pos, fun _ => one_pos, two_pos⟩

/-- The axes `(a, 1)`. -/
def p11cPJax (a : ℝ) : Vec 2 := ![a, 1]

theorem p11cPJax_mem {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : p11cPJax a ∈ axes 2 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · simpa [p11cPJax] using ha.1
    · simp [p11cPJax]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p11cPJax] at hij ⊢
    exact ha.2

/-- The scale taking the regular eccentricity vector `v` to the Poincaré variables `(ξ, η)` at the
action `L`. -/
def p11cPJscale (L v0 v1 : ℝ) : ℝ := √(2 * L / (1 + √(1 - (v0 ^ 2 + v1 ^ 2))))

/-- The slow variable whose regular eccentricity vectors are `z`. -/
def p11cPJx (a : ℝ) (z : Phase 2) : Slow 2 :=
  (fun i => p11cPJscale (action p11cPJD (p11cPJax a) i) (z.1 i) (z.2 i) * z.1 i,
    action p11cPJD (p11cPJax a),
    fun i => p11cPJscale (action p11cPJD (p11cPJax a) i) (z.1 i) (z.2 i) * z.2 i)

theorem p11cPJ_action (a : ℝ) (i : Fin 2) :
    action p11cPJD (p11cPJax a) i = √(p11cPJax a i) := by
  simp [action, p11cPJD]

theorem p11cPJ_poincareV {L v0 v1 : ℝ} (hL : 0 < L) (hv : v0 ^ 2 + v1 ^ 2 < 1) (φ : ℝ) :
    poincareV ((![φ, p11cPJscale L v0 v1 * v0] : Fin 2 → ℝ),
      (![L, p11cPJscale L v0 v1 * v1] : Fin 2 → ℝ)) = ![v0, v1] ∧
    ((![φ, p11cPJscale L v0 v1 * v0] : Fin 2 → ℝ),
      (![L, p11cPJscale L v0 v1 * v1] : Fin 2 → ℝ)) ∈ poincareDom ∧
    poincareK ((![φ, p11cPJscale L v0 v1 * v0] : Fin 2 → ℝ),
      (![L, p11cPJscale L v0 v1 * v1] : Fin 2 → ℝ)) = √(1 - (v0 ^ 2 + v1 ^ 2)) := by
  set k := √(1 - (v0 ^ 2 + v1 ^ 2)) with hk
  have hk0 : 0 < k := Real.sqrt_pos.2 (by linarith)
  have hk2 : k ^ 2 = 1 - (v0 ^ 2 + v1 ^ 2) := Real.sq_sqrt (by linarith)
  set s := p11cPJscale L v0 v1 with hs
  have hs2 : s ^ 2 = 2 * L / (1 + k) := by
    rw [hs, p11cPJscale, Real.sq_sqrt (by positivity)]
  have hΓ : poincareGamma ((![φ, s * v0] : Fin 2 → ℝ), (![L, s * v1] : Fin 2 → ℝ)) =
      L * (1 - k) := by
    simp only [poincareGamma, Matrix.cons_val_one, Matrix.cons_val_zero]
    have : (s * v0) ^ 2 + (s * v1) ^ 2 = s ^ 2 * (v0 ^ 2 + v1 ^ 2) := by ring
    rw [this, hs2]
    have h1 : v0 ^ 2 + v1 ^ 2 = 1 - k ^ 2 := by linarith
    rw [h1]
    field_simp
    ring
  have hK : poincareK ((![φ, s * v0] : Fin 2 → ℝ), (![L, s * v1] : Fin 2 → ℝ)) = k := by
    simp only [poincareK, hΓ, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
    ring
  refine ⟨?_, ⟨?_, ?_⟩, hK⟩
  · simp only [poincareV, hΓ, Matrix.cons_val_one, Matrix.cons_val_zero]
    have h2 : (1 - L * (1 - k) / (2 * L)) / L = (1 + k) / (2 * L) := by
      field_simp; ring
    rw [h2]
    have h3 : √((1 + k) / (2 * L)) * s = 1 := by
      rw [hs, p11cPJscale, ← Real.sqrt_mul (by positivity)]
      have : (1 + k) / (2 * L) * (2 * L / (1 + k)) = 1 := by field_simp
      rw [this, Real.sqrt_one]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
      rw [← mul_assoc, h3, one_mul]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← mul_assoc, h3, one_mul]
  · simpa using hL
  · simp only [poincareDom, mem_setOf_eq, hΓ, Matrix.cons_val_one, Matrix.cons_val_zero]
    nlinarith

private theorem pjB_planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

theorem p11cPJ_position {L v0 v1 : ℝ} (hL : 0 < L) (hv : v0 ^ 2 + v1 ^ 2 < 1) (φ : ℝ) :
    (((poincare 1 1 ((![φ, p11cPJscale L v0 v1 * v0] : Fin 2 → ℝ),
        (![L, p11cPJscale L v0 v1 * v1] : Fin 2 → ℝ))).1 0 : ℝ) : ℂ) +
      Complex.I * (((poincare 1 1 ((![φ, p11cPJscale L v0 v1 * v0] : Fin 2 → ℝ),
        (![L, p11cPJscale L v0 v1 * v1] : Fin 2 → ℝ))).1 1 : ℝ) : ℂ) =
      ((L ^ 2 : ℝ) : ℂ) * p11c_orbit φ ![v0, v1] := by
  obtain ⟨hV, -, hK⟩ := p11cPJ_poincareV hL hv φ
  set w : Phase 2 := ((![φ, p11cPJscale L v0 v1 * v0] : Fin 2 → ℝ),
    (![L, p11cPJscale L v0 v1 * v1] : Fin 2 → ℝ)) with hw
  have hF : poincareF w = keplerLong φ ![v0, v1] := by
    unfold poincareF; rw [hV]; rfl
  have hsq : planeSq (![v0, v1] : Fin 2 → ℝ) = v0 ^ 2 + v1 ^ 2 := by
    rw [pjB_planeSq_two]; simp
  have hw2 : w.2 0 = L := rfl
  simp only [poincare, hV, hK, hF, p11c_orbit, hsq, hw2, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

theorem p11cPJ_planeLength_sub (q q' : Fin 2 → ℝ) :
    planeLength (q - q') =
      ‖(((q 0 : ℝ) : ℂ) + Complex.I * ((q 1 : ℝ) : ℂ)) -
        (((q' 0 : ℝ) : ℂ) + Complex.I * ((q' 1 : ℝ) : ℂ))‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  unfold planeLength
  rw [pjB_planeSq_two]
  simp

theorem p11cPJ_pairPotential_two (q : Fin (2 * 2) → ℝ) :
    pairPotential 1 (fun _ : Fin 2 => (1 : ℝ)) q =
      (planeLength (bodyVector q 0 - bodyVector q 1))⁻¹ := by
  have e0 : Finset.univ.filter (fun j : Fin 2 => (0 : Fin 2) < j) = {1} := by decide
  have e1 : Finset.univ.filter (fun j : Fin 2 => (1 : Fin 2) < j) = ∅ := by decide
  simp [pairPotential, Fin.sum_univ_two, e0, e1]

theorem p11cPJ_action_pos {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (i : Fin 2) :
    0 < action p11cPJD (p11cPJax a) i := by
  rw [p11cPJ_action]
  fin_cases i
  · simpa [p11cPJax] using ha.1
  · simp [p11cPJax]

theorem p11cPJ_perturbation {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {z : Phase 2}
    (hz : ∀ i, z.1 i ^ 2 + z.2 i ^ 2 < 1) (φ : Vec 2) :
    perturbation p11cPJD false (assemble (p11cPJx a z).2.1 φ (p11cPJx a z).2.2
        (p11cPJx a z).1) =
      -‖(a : ℂ) * p11c_orbit (φ 0) ![z.1 0, z.2 0] - p11c_orbit (φ 1) ![z.1 1, z.2 1]‖⁻¹ := by
  have hpos0 := p11cPJ_position (p11cPJ_action_pos ha 0) (hz 0) (φ 0)
  have hpos1 := p11cPJ_position (p11cPJ_action_pos ha 1) (hz 1) (φ 1)
  have hb : ∀ i : Fin 2, bodyVector (poincareProd p11cPJD.m (p11cPJD.G * p11cPJD.m0)
      (assemble (action p11cPJD (p11cPJax a)) φ (p11cPJx a z).2.2 (p11cPJx a z).1)).1 i =
      (poincare 1 1 ((![φ i, p11cPJscale (action p11cPJD (p11cPJax a) i) (z.1 i) (z.2 i) * z.1 i] :
          Fin 2 → ℝ), (![action p11cPJD (p11cPJax a) i,
            p11cPJscale (action p11cPJD (p11cPJax a) i) (z.1 i) (z.2 i) * z.2 i] :
          Fin 2 → ℝ))).1 := by
    intro i
    have := congrArg Prod.fst (poincareProd_block p11cPJD.m (p11cPJD.G * p11cPJD.m0)
      (assemble (action p11cPJD (p11cPJax a)) φ (p11cPJx a z).2.2 (p11cPJx a z).1) i)
    rw [planetBlock_assemble] at this
    simpa [p11cPJD, p11cPJx] using this
  have hpert : perturbation p11cPJD false (assemble (action p11cPJD (p11cPJax a)) φ
      (p11cPJx a z).2.2 (p11cPJx a z).1) = -(planeLength (bodyVector (poincareProd p11cPJD.m
        (p11cPJD.G * p11cPJD.m0) (assemble (action p11cPJD (p11cPJax a)) φ (p11cPJx a z).2.2
          (p11cPJx a z).1)).1 0 - bodyVector (poincareProd p11cPJD.m
        (p11cPJD.G * p11cPJD.m0) (assemble (action p11cPJD (p11cPJax a)) φ (p11cPJx a z).2.2
          (p11cPJx a z).1)).1 1))⁻¹ := by
    simp only [perturbation, fFix, Bool.false_eq_true, ite_false]
    rw [show p11cPJD.G = 1 from rfl]
    have := p11cPJ_pairPotential_two (poincareProd p11cPJD.m (p11cPJD.G * p11cPJD.m0)
      (assemble (action p11cPJD (p11cPJax a)) φ (p11cPJx a z).2.2 (p11cPJx a z).1)).1
    simpa [p11cPJD] using congrArg Neg.neg this
  rw [hpert, hb 0, hb 1, p11cPJ_planeLength_sub, hpos0, hpos1]
  have hl0 : (action p11cPJD (p11cPJax a) 0) ^ 2 = a := by
    rw [p11cPJ_action]; simp [p11cPJax, Real.sq_sqrt ha.1.le]
  have hl1 : (action p11cPJD (p11cPJax a) 1) ^ 2 = 1 := by
    rw [p11cPJ_action]; simp [p11cPJax]
  rw [hl0, hl1]
  simp

theorem p11cPJ_secular_eq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {z : Phase 2}
    (hz : ∀ i, z.1 i ^ 2 + z.2 i ^ 2 < 1) :
    secular p11cPJD false (p11cPJx a z) = -p11c_pairAverage a z := by
  unfold secular secularAverage p11c_pairAverage
  simp only [p11cPJ_perturbation ha hz]
  rw [integral_neg]
  simp

theorem p11cPJ_mem_slowDom {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {z : Phase 2}
    (hz : ∀ i, z.1 i ^ 2 + z.2 i ^ 2 < 1) : p11cPJx a z ∈ slowDom p11cPJD := by
  rw [mem_slowDom_iff]
  intro i
  obtain ⟨-, hdom, -⟩ := p11cPJ_poincareV (p11cPJ_action_pos ha i) (hz i) 0
  refine ⟨p11cPJ_action_pos ha i, ?_⟩
  have := hdom.2
  simp only [poincareGamma, Matrix.cons_val_one, Matrix.cons_val_zero] at this
  simpa [p11cPJx] using this

private theorem pjB_analyticAt_fst (i : Fin 2) (z : Phase 2) :
    AnalyticAt ℝ (fun z : Phase 2 => z.1 i) z :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt z

private theorem pjB_analyticAt_snd (i : Fin 2) (z : Phase 2) :
    AnalyticAt ℝ (fun z : Phase 2 => z.2 i) z :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt z

theorem p11cPJscale_analyticAt {L : ℝ} (hL : 0 < L) (i : Fin 2) :
    AnalyticAt ℝ (fun z : Phase 2 => p11cPJscale L (z.1 i) (z.2 i)) 0 := by
  have hq : AnalyticAt ℝ (fun z : Phase 2 => z.1 i ^ 2 + z.2 i ^ 2) 0 :=
    ((pjB_analyticAt_fst i 0).pow 2).add ((pjB_analyticAt_snd i 0).pow 2)
  have hk : AnalyticAt ℝ (fun z : Phase 2 => √(1 - (z.1 i ^ 2 + z.2 i ^ 2))) 0 :=
    (((analyticAt_const.sub hq).contDiffAt (n := ω)).sqrt (by simp)).analyticAt
  have hd : AnalyticAt ℝ (fun z : Phase 2 => 2 * L / (1 + √(1 - (z.1 i ^ 2 + z.2 i ^ 2)))) 0 :=
    analyticAt_const.div (analyticAt_const.add hk) (by simp)
  unfold p11cPJscale
  exact ((hd.contDiffAt (n := ω)).sqrt (by simp; positivity)).analyticAt

theorem p11cPJx_analyticAt {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    AnalyticAt ℝ (p11cPJx a) 0 := by
  unfold p11cPJx
  refine AnalyticAt.prod ?_ (AnalyticAt.prod analyticAt_const ?_)
  · rw [analyticAt_pi_iff]
    intro i
    exact (p11cPJscale_analyticAt (p11cPJ_action_pos ha i) i).mul (pjB_analyticAt_fst i 0)
  · rw [analyticAt_pi_iff]
    intro i
    exact (p11cPJscale_analyticAt (p11cPJ_action_pos ha i) i).mul (pjB_analyticAt_snd i 0)

theorem p11cPJ_eventually_small : ∀ᶠ z in 𝓝 (0 : Phase 2), ∀ i, z.1 i ^ 2 + z.2 i ^ 2 < 1 := by
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous fun z : Phase 2 => z.1 i ^ 2 + z.2 i ^ 2 := by fun_prop
  exact hc.continuousAt.eventually_lt continuousAt_const (by simp)

/-- The pair average is real analytic at `0`. -/
theorem p11cPJ_pairAverage_analyticAt {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    AnalyticAt ℝ (p11c_pairAverage a) 0 := by
  obtain ⟨r, hr0, hrho, -, hP⟩ := perturbation_analytic p11cPJD (p11cPJax_mem ha)
  have hmem : p11cPJx a 0 ∈ realDisc p11cPJD (p11cPJax a) r := by
    show inclusion (p11cPJx a 0) ∈ polydisc p11cPJD (p11cPJax a) r
    rw [polydisc_eq_ball _ _ hr0]
    have : inclusion (p11cPJx a 0) = SecularForm.center p11cPJD (p11cPJax a) := by
      simp [center, p11cPJx]
    rw [this]
    exact Metric.mem_ball_self hr0
  have hS : AnalyticAt ℝ (secular p11cPJD false) (p11cPJx a 0) :=
    (hP false).2.2.2.2.1 _ hmem
  have hc := hS.comp (p11cPJx_analyticAt ha)
  have hev : p11c_pairAverage a =ᶠ[𝓝 0]
      fun z => -(secular p11cPJD false (p11cPJx a z)) := by
    filter_upwards [p11cPJ_eventually_small] with z hz
    rw [p11cPJ_secular_eq ha hz]; ring
  exact (hc.neg).congr hev.symm

theorem p11cPJx_neg {a : ℝ} (z : Phase 2) :
    p11cPJx a (-z) = (-(p11cPJx a z).1, (p11cPJx a z).2.1, -(p11cPJx a z).2.2) := by
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · funext i; simp [p11cPJx, p11cPJscale]
  · funext i; simp [p11cPJx, p11cPJscale]

/-- The pair average is even near `0`. -/
theorem p11cPJ_pairAverage_even {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_pairAverage a =ᶠ[𝓝 0] fun z => p11c_pairAverage a (-z) := by
  filter_upwards [p11cPJ_eventually_small] with z hz
  have hz' : ∀ i, (-z).1 i ^ 2 + (-z).2 i ^ 2 < 1 := fun i => by simpa using hz i
  have hx := p11cPJ_mem_slowDom ha hz
  have h1 := (evenness p11cPJD hx false 0).1
  have h2 := p11cPJ_secular_eq ha hz
  have h3 := p11cPJ_secular_eq ha hz'
  rw [p11cPJx_neg] at h3
  rw [h1] at h3
  linarith

end KAM.Planetary

end
