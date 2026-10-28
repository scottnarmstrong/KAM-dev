/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.AnalyticGeometry
public import KAM.Planetary.SecularForm.AnalyticRegularity
public import KAM.Planetary.SecularForm.AnalyticReal
public import KAM.Strip.AnalyticTaylor

/-!
# Secular form: analyticity of the perturbation and of its average

Blueprint P, Part 8, Proposition `bpP:p8:perturbation-analytic` (steps `pa-circ`, `pa-unif`,
`pa-hol`, `pa-avg`). The geometry (common radius, separation bound) is in `AnalyticGeometry`, the
holomorphy/continuity of the complexified perturbation in `AnalyticRegularity`, and its restriction
to real points in `AnalyticReal`; this module integrates over the angle cell (`e_param_cslow`) and
restricts the average to the real disc.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

/-- The real inclusion `Slow n → CSlow n` as a real-linear map. -/
def inclusionLM (n : ℕ) : Slow n →ₗ[ℝ] CSlow n where
  toFun := inclusion
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) <;>
      simp [inclusion]
  map_smul' c x := by
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) <;>
      simp [inclusion]

/-- The real inclusion `Slow n → CSlow n` as a continuous real-linear map. -/
def inclusionCLM (n : ℕ) : Slow n →L[ℝ] CSlow n := LinearMap.toContinuousLinearMap (inclusionLM n)

theorem inclusionCLM_apply (x : Slow n) : inclusionCLM n x = inclusion x := rfl

theorem isOpen_realDisc (D : Data n) (a : Vec n) {r : ℝ} (hr : 0 < r) :
    IsOpen (realDisc D a r) := by
  rw [realDisc, polydisc_eq_ball D a hr]
  exact Metric.isOpen_ball.preimage (inclusionCLM n).continuous

theorem secularC_inclusion (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ} (hr : r < rho D a)
    (b : Bool) {x : Slow n} (hx : x ∈ realDisc D a r) :
    secularC D b (inclusion x) = (secular D b x : ℂ) := by
  have h : ∀ t, perturbationC D b t (inclusion x) =
      (perturbation D b (assemble x.2.1 t x.2.2 x.1) : ℂ) := fun t =>
    perturbationC_inclusion D ha hr b hx t
  unfold secularC secular secularAverage
  simp only [h]
  rw [integral_complex_ofReal, Complex.real_smul]
  push_cast
  rfl

theorem perturbation_analytic (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a ∧
    (∀ t x, x ∈ polydisc D a r → ∀ i j, i < j →
      ((a j-a i)^2 / 2) ≤ (separationC D t x i j).re) ∧
    (∀ b : Bool, (∀ t, DifferentiableOn ℂ (perturbationC D b t) (polydisc D a r)) ∧
      ContinuousOn (fun z : Vec n × CSlow n => perturbationC D b z.1 z.2)
        (univ ×ˢ polydisc D a r) ∧
      DifferentiableOn ℂ (secularC D b) (polydisc D a r) ∧
      (∀ x ∈ realDisc D a r, secularC D b (inclusion x) = (secular D b x : ℂ)) ∧
      AnalyticOnNhd ℝ (secular D b) (realDisc D a r) ∧
      (∀ x ∈ realDisc D a r, ∀ t,
        perturbationC D b t (inclusion x) =
          (perturbation D b (assemble x.2.1 t x.2.2 x.1) : ℂ)) ∧
      (∀ x ∈ realDisc D a r,
        IntegrableOn (fun t => perturbation D b (assemble x.2.1 t x.2.2 x.1)) (cell n))) := by
  obtain ⟨r, hr0, hrho, hsep⟩ := exists_radius D ha
  refine ⟨r, hr0, hrho, hsep, fun b => ?_⟩
  have hU : IsOpen (polydisc D a r) := by
    rw [polydisc_eq_ball D a hr0]; exact Metric.isOpen_ball
  have hol := differentiableOn_perturbationC D ha hrho hsep hr0 b
  have hcont := continuousOn_perturbationC D ha hrho hsep b
  have hS : DifferentiableOn ℂ (secularC D b) (polydisc D a r) := by
    unfold secularC
    exact (e_param_cslow hU (f := fun t x => perturbationC D b t x)
      (hcont.mono (prod_mono (subset_univ (cell n)) subset_rfl))
      fun t _ => hol t).const_smul ((2 * π) ^ (-(n : ℤ)))
  have hreal : ∀ x ∈ realDisc D a r, secularC D b (inclusion x) = (secular D b x : ℂ) :=
    fun x hx => secularC_inclusion D ha hrho b hx
  refine ⟨hol, hcont, hS, hreal, ?_, fun x hx t => perturbationC_inclusion D ha hrho b hx t,
    fun x hx => ?_⟩
  · intro x hx
    have hA' : AnalyticOnNhd ℂ (secularC D b) (polydisc D a r) :=
      analyticOnNhd_of_differentiableOn hU hS
    have hA : AnalyticAt ℂ (secularC D b) (inclusion x) := hA' _ hx
    have h1 : AnalyticAt ℝ (fun y => (secularC D b (inclusion y)).re) x :=
      (Complex.reCLM.analyticAt _).comp
        ((hA.restrictScalars (𝕜 := ℝ)).comp ((inclusionCLM n).analyticAt x))
    refine h1.congr ?_
    filter_upwards [(isOpen_realDisc D a hr0).mem_nhds hx] with y hy
    rw [hreal y hy, Complex.ofReal_re]
  · have hm : ContinuousOn (fun t : Vec n => (t, inclusion x)) (cell n) :=
      continuousOn_id.prodMk continuousOn_const
    have hmaps : MapsTo (fun t : Vec n => (t, inclusion x)) (cell n)
        (univ ×ˢ polydisc D a r) := fun t _ => ⟨mem_univ _, hx⟩
    have hc := hcont.comp hm hmaps
    have hre : ContinuousOn (fun t => (perturbationC D b t (inclusion x)).re) (cell n) :=
      Complex.continuous_re.comp_continuousOn hc
    have heq : (fun t => perturbation D b (assemble x.2.1 t x.2.2 x.1)) =
        fun t => (perturbationC D b t (inclusion x)).re := by
      funext t
      rw [perturbationC_inclusion D ha hrho b hx t, Complex.ofReal_re]
    rw [heq]
    exact hre.integrableOn_compact isCompact_cell

end SecularForm
end KAM.Planetary
end
