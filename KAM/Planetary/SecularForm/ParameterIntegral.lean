/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic

/-!
# Secular form: parameter integrals over the angle cell

Blueprint P, Part 8 (`bpP:p8:e-param`, `bpP:p8:e-diff`) and the two published-graph adapters
`compact_uniform` (`bpP:p12:f-unif`) and `periodic_derivative_integral` (`K:bp:p1:ext-integral`).
Holomorphic and finite-order differentiable dependence of the cell integral on a parameter, by
dominated differentiation under the integral sign.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n d : ℕ}

theorem isCompact_cell : IsCompact (cell n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem measurableSet_cell : MeasurableSet (cell n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- Differentiation under the cell integral when the derivative is jointly continuous. -/
theorem hasFDerivAt_cell_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {U : Set (Vec d)} (hU : IsOpen U) {G : Vec n → Vec d → E}
    (hG : ContinuousOn (fun z : Vec n × Vec d => G z.1 z.2) (cell n ×ˢ U))
    (hGd : ∀ t ∈ cell n, DifferentiableOn ℝ (G t) U)
    (hG' : ContinuousOn (fun z : Vec n × Vec d => fderiv ℝ (G z.1) z.2) (cell n ×ˢ U))
    {x : Vec d} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t in cell n, G t y) (∫ t in cell n, fderiv ℝ (G t) x) x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hsub : Metric.closedBall x (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (cell n ×ˢ Metric.closedBall x (ε / 2)) :=
    isCompact_cell.prod (isCompact_closedBall x (ε / 2))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG'.mono (prod_mono subset_rfl hsub))
  have hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun t => G t y) (volume.restrict (cell n)) := by
    intro y hy
    have : ContinuousOn (fun t => G t y) (cell n) :=
      hG.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hy⟩
    exact this.aestronglyMeasurable measurableSet_cell
  have hfin : volume.restrict (cell n) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]; exact isCompact_cell.measure_lt_top
  have : IsFiniteMeasure (volume.restrict (cell n)) := ⟨hfin⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => G t y) (F' := fun y t => fderiv ℝ (G t) y) (bound := fun _ => C)
    (s := Metric.closedBall x (ε / 2)) (Metric.closedBall_mem_nhds x (by linarith))
    ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · exact Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hmeas y hy
  · have : ContinuousOn (fun t => G t x) (cell n) :=
      hG.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hx⟩
    exact this.integrableOn_compact isCompact_cell
  · have : ContinuousOn (fun t => fderiv ℝ (G t) x) (cell n) :=
      hG'.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hx⟩
    exact this.aestronglyMeasurable measurableSet_cell
  · refine (ae_restrict_iff' measurableSet_cell).2 (Eventually.of_forall fun t ht y hy => ?_)
    exact hC (t, y) ⟨ht, hy⟩
  · refine (ae_restrict_iff' measurableSet_cell).2 (Eventually.of_forall fun t ht y hy => ?_)
    exact ((hGd t ht).differentiableAt (hU.mem_nhds (hsub hy))).hasFDerivAt

/-- Finite-order differentiation under the cell integral. -/
theorem e_diff {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec n → Vec d → ℝ} (k : ℕ)
    (hCont : ∀ j : ℕ, j ≤ k → ContinuousOn
      (fun z : Vec n × Vec d => iteratedFDeriv ℝ j (f z.1) z.2)
      (cell n ×ˢ U))
    (hSmooth : ∀ t ∈ cell n, ContDiffOn ℝ k (f t) U)
    {x : Vec d} (hx : x ∈ U) :
    iteratedFDeriv ℝ k (fun y => ∫ t in cell n, f t y) x =
      ∫ t in cell n, iteratedFDeriv ℝ k (f t) x := by
  have key : ∀ j : ℕ, j ≤ k → ∀ y ∈ U,
      iteratedFDeriv ℝ j (fun y => ∫ t in cell n, f t y) y =
        ∫ t in cell n, iteratedFDeriv ℝ j (f t) y := by
    intro j
    induction j with
    | zero =>
      intro _ y _
      exact ((continuousMultilinearCurryFin0 ℝ (Vec d) ℝ).symm.toContinuousLinearEquiv
        |>.integral_comp_comm (fun t => f t y)).symm
    | succ j ih =>
      intro hj y hy
      have hjk : j ≤ k := (Nat.le_succ j).trans hj
      let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Vec d) ℝ
      have hdiff : ∀ t ∈ cell n, DifferentiableOn ℝ (iteratedFDeriv ℝ j (f t)) U := by
        intro t ht
        have h := (hSmooth t ht).differentiableOn_iteratedFDerivWithin
          (m := j) (by exact_mod_cast Nat.lt_of_succ_le hj) hU.uniqueDiffOn
        exact h.congr fun z hz => (iteratedFDerivWithin_of_isOpen j hU hz).symm
      have hfd : ∀ z : Vec n × Vec d, fderiv ℝ (iteratedFDeriv ℝ j (f z.1)) z.2 =
          e (iteratedFDeriv ℝ (j + 1) (f z.1) z.2) := fun z => rfl
      have hG' : ContinuousOn (fun z : Vec n × Vec d => fderiv ℝ (iteratedFDeriv ℝ j (f z.1)) z.2)
          (cell n ×ˢ U) := by
        simp_rw [hfd]
        exact e.continuous.comp_continuousOn (hCont (j + 1) hj)
      have hD := hasFDerivAt_cell_integral hU (hCont j hjk) hdiff hG' hy
      have heq : iteratedFDeriv ℝ j (fun y => ∫ t in cell n, f t y) =ᶠ[𝓝 y]
          fun y => ∫ t in cell n, iteratedFDeriv ℝ j (f t) y :=
        Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz => ih hjk z hz
      have h1 : fderiv ℝ (iteratedFDeriv ℝ j (fun y => ∫ t in cell n, f t y)) y =
          ∫ t in cell n, fderiv ℝ (iteratedFDeriv ℝ j (f t)) y := by
        rw [heq.fderiv_eq]; exact hD.fderiv
      show e.symm (fderiv ℝ (iteratedFDeriv ℝ j (fun y => ∫ t in cell n, f t y)) y) = _
      rw [h1]
      have : CompleteSpace (Vec d →L[ℝ] Vec d [×j]→L[ℝ] ℝ) := inferInstance
      exact (LinearIsometry.integral_comp_comm (𝕜 := ℝ) e.symm.toLinearIsometry
        (fun t => fderiv ℝ (iteratedFDeriv ℝ j (f t)) y)).symm
  exact key k le_rfl x hx

/-- G1: uniform continuity on a compact set. -/
theorem compact_uniform {E F : Type*} [MetricSpace E] [MetricSpace F]
    {K : Set E} (hK : IsCompact K) {f : E → F} (hf : ContinuousOn f K) :
    UniformContinuousOn f K :=
  hK.uniformContinuousOn_of_continuous hf

/-- G2, instantiated with the analytic periodic position map. -/
theorem periodic_derivative_integral {q : ℝ → (Fin 2 → ℝ)}
    (hq : ContDiff ℝ 1 q) (hp : Function.Periodic q (2*π)) :
    ∫ t in (0:ℝ)..2*π, deriv q t = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => (hq.differentiable (by simp)) x)
    ((hq.continuous_deriv (by simp)).intervalIntegrable _ _)]
  have := hp 0
  simp only [zero_add] at this
  rw [this, sub_self]

end SecularForm
end KAM.Planetary
