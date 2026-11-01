/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.FlowSmooth
public import KAM.Wave.KamStep.FlowVariational

/-!
# Holomorphy and derivative bounds of the smoothing displacement (`bpW:w5:flow` (i), (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

In the setting of `FlowSmooth` (`X = ι ∘ Z`, `Z : F → G`), the displacement `Ψ^t = smoothDisp ι Z t`
is `G`-valued holomorphic on `U` (`hasFDerivAt_smoothDisp`: differentiation under the integral
sign, steps `f-flow` of the blueprint), so the Cauchy estimate on balls inside `U` gives the
`G`-norm bounds on `DΨ^t` (`norm_fderiv_smoothDisp_le`, and for parameter differences
`norm_fderiv_smoothDisp_sub_le`), and `Dφ^t = I + ι ∘ DΨ^t` (`fderiv_holoFlow_smooth`).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {ι : G →L[ℂ] F} {Z : F → G} {V U : Set F} {M δ : ℝ}
  (h : FlowHyp (smoothField ι Z) V U M δ) (hZ : DifferentiableOn ℂ Z V)
  (hb : ∀ z ∈ V, ‖Z z‖ ≤ M)
include h hZ hb

omit [CompleteSpace G] in
/-- Differentiation under the integral sign: `DΨ^t(w) = ∫₀ᵗ DZ(φ^σ w) Dφ^σ(w) dσ`. -/
theorem hasFDerivAt_smoothDisp {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasFDerivAt (smoothDisp ι Z t)
      (∫ σ in (0 : ℝ)..t, (fderiv ℂ Z (holoFlow (smoothField ι Z) σ w)).comp
        (fderiv ℂ (holoFlow (smoothField ι Z) σ) w)) w := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp h.isOpen_U w hw
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  set φ := holoFlow (smoothField ι Z) with hφ
  have hZc : ContinuousOn (fun σ => Z (φ σ w)) (Icc (-1 : ℝ) 1) :=
    continuousOn_smooth_integrand h hZ hw
  have hmeas : ∀ x ∈ U, AEStronglyMeasurable (fun σ => Z (φ σ x)) (volume.restrict (Ι 0 t)) :=
    fun x hx => ((continuousOn_smooth_integrand h hZ hx).mono (uIoc_subset_Icc
      ht)).aestronglyMeasurable
      measurableSet_uIoc
  have hG : ContinuousOn (fun σ => (fderiv ℂ Z (φ σ w)).comp (fderiv ℂ (φ σ) w))
      (Icc (-1 : ℝ) 1) :=
    ((continuousOn_fderiv_of_holomorphic h.isOpen_V hZ).comp (continuousOn_holoFlow_time h hw)
      fun σ hσ => h.mem_V_of_ball hw (holoFlow_mem_ball h hw hσ)).clm_comp
      (continuousOn_fderiv_holoFlow_time h hw)
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := volume) (a := 0) (b := t) (s := ball w ε) (x₀ := w)
    (F := fun x σ => Z (φ σ x)) (F' := fun x σ => (fderiv ℂ Z (φ σ x)).comp (fderiv ℂ (φ σ) x))
    (bound := fun _ => M / δ * Real.exp (M / δ))
    (ball_mem_nhds w hε)
    (Filter.eventually_of_mem (h.isOpen_U.mem_nhds hw) fun x hx => hmeas x hx)
    ((hZc.mono (uIcc_subset_Icc' ht)).intervalIntegrable)
    ((hG.mono (uIoc_subset_Icc ht)).aestronglyMeasurable measurableSet_uIoc)
    (Filter.Eventually.of_forall fun σ hσ x hx => by
      have hxU : x ∈ U := hεU hx
      have hσ' := uIoc_subset_Icc ht hσ
      have hz := holoFlow_mem_ball h hxU hσ'
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h1 : ‖fderiv ℂ Z (φ σ x)‖ ≤ M / δ :=
        norm_fderiv_le_div_of_ball_subset h.delta_pos h.M_pos.le hZ hb (h.ball_subset_V hxU hz)
      have h2 := norm_fderiv_holoFlow_le h hxU hσ'
      have : |σ| ≤ 1 := abs_le.mpr ⟨hσ'.1, hσ'.2⟩
      refine (mul_le_mul h1 (h2.trans (Real.exp_le_exp.mpr (by nlinarith))) (norm_nonneg _) hL))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun σ hσ x hx => by
      have hxU : x ∈ U := hεU hx
      have hσ' := uIoc_subset_Icc ht hσ
      have hz : φ σ x ∈ V := h.mem_V_of_ball hxU (holoFlow_mem_ball h hxU hσ')
      have h1 : HasFDerivAt Z (fderiv ℂ Z (φ σ x)) (φ σ x) :=
        (hZ.differentiableAt (h.isOpen_V.mem_nhds hz)).hasFDerivAt
      have h2 : HasFDerivAt (fun x' => φ σ x') (fderiv ℂ (φ σ) x) x :=
        ((holomorphicOn_holoFlow h hσ').differentiableAt (h.isOpen_U.mem_nhds hxU)).hasFDerivAt
      exact h1.comp x h2)
  exact hmain


omit [CompleteSpace G] in
/-- `Ψ^t` is holomorphic on `U` (`G`-valued). -/
theorem differentiableOn_smoothDisp {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    DifferentiableOn ℂ (smoothDisp ι Z t) U := fun _ hw =>
  (hasFDerivAt_smoothDisp h hZ hb hw ht).differentiableAt.differentiableWithinAt

omit [CompleteSpace G] in
/-- **Cauchy estimate for the displacement** (`bpW:w5:flow` (ii)): if `B(w, ρ) ⊆ U` then
`‖DΨ^t(w)‖_{F→G} ≤ M |t| / ρ`. -/
theorem norm_fderiv_smoothDisp_le {w : F} {ρ : ℝ} (hρ : 0 < ρ) (hball : ball w ρ ⊆ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) : ‖fderiv ℂ (smoothDisp ι Z t) w‖ ≤ M * |t| / ρ :=
  norm_fderiv_le_div_of_ball_subset hρ (mul_nonneg h.M_pos.le (abs_nonneg t))
    (differentiableOn_smoothDisp h hZ hb ht)
    (fun _ hz => norm_smoothDisp_le h hb hz ht) hball

/-- **`Dφ^t = I + ι ∘ DΨ^t`**: the derivative of the flow gains the smoothing (`bpW:w5:flow` (ii)).
-/
theorem fderiv_holoFlow_smooth {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    fderiv ℂ (holoFlow (smoothField ι Z) t) w =
      ContinuousLinearMap.id ℂ F + ι.comp (fderiv ℂ (smoothDisp ι Z t) w) := by
  have hev : holoFlow (smoothField ι Z) t =ᶠ[𝓝 w] fun x => x + ι (smoothDisp ι Z t x) :=
    Filter.eventually_of_mem (h.isOpen_U.mem_nhds hw) fun x hx =>
      holoFlow_smooth_eq h hZ hx ht
  rw [hev.fderiv_eq]
  have hd := (hasFDerivAt_smoothDisp h hZ hb hw ht).differentiableAt
  exact ((hasFDerivAt_id w).add (ι.hasFDerivAt.comp w hd.hasFDerivAt)).fderiv

section Param

variable {Z' : F → G} (h' : FlowHyp (smoothField ι Z') V U M δ) (hZ' : DifferentiableOn ℂ Z' V)
  (hb' : ∀ z ∈ V, ‖Z' z‖ ≤ M) (hι : ∀ g, ‖ι g‖ ≤ ‖g‖)
include h' hZ' hb' hι
omit [CompleteSpace G] in

/-- **Cauchy estimate for parameter differences** (`bpW:w5:flow` (ii), step `f-der`): if
`‖Z - Z'‖ ≤ N` on `V` and `B(w, ρ) ⊆ U`, then
`‖DΨ_Z^t(w) - DΨ_{Z'}^t(w)‖ ≤ |t| N (1 + L e^L) / ρ` with `L = M/δ`. -/
theorem norm_fderiv_smoothDisp_sub_le {N : ℝ} (hN : 0 ≤ N) (hZZ : ∀ z ∈ V, ‖Z z - Z' z‖ ≤ N)
    {w : F} {ρ : ℝ} (hρ : 0 < ρ) (hball : ball w ρ ⊆ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖fderiv ℂ (smoothDisp ι Z t) w - fderiv ℂ (smoothDisp ι Z' t) w‖ ≤
      |t| * (N * (1 + M / δ * Real.exp (M / δ))) / ρ := by
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have hd1 := differentiableOn_smoothDisp h hZ hb ht
  have hd2 := differentiableOn_smoothDisp h' hZ' hb' ht
  have hw : w ∈ U := hball (mem_ball_self hρ)
  have hU := h.isOpen_U.mem_nhds hw
  rw [← fderiv_sub (hd1.differentiableAt hU) (hd2.differentiableAt hU)]
  refine norm_fderiv_le_div_of_ball_subset hρ (by positivity) (hd1.sub hd2) (fun z hz => ?_) hball
  exact norm_smoothDisp_sub_le h h' hZ hZ' hι hb' hN hZZ hz ht

end Param

end KAM.Wave
