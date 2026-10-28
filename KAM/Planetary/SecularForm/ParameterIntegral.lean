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

/-- The complex derivative in the parameter is measurable on the cell (difference quotients). -/
theorem aestronglyMeasurable_fderiv_cell {U : Set (CVec d)} (hU : IsOpen U)
    {f : Vec n → CVec d → ℂ}
    (hCont : ContinuousOn (fun z : Vec n × CVec d => f z.1 z.2) (cell n ×ˢ U))
    (hHol : ∀ t ∈ cell n, DifferentiableOn ℂ (f t) U) {x : CVec d} (hx : x ∈ U) :
    AEStronglyMeasurable (fun t => fderiv ℂ (f t) x) (volume.restrict (cell n)) := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  let e : Fin d → CVec d := fun i j => if i = j then 1 else 0
  have hfun : ∀ t, fderiv ℂ (f t) x =
      ∑ i, (fderiv ℂ (f t) x (e i)) • (ContinuousLinearMap.proj i : CVec d →L[ℂ] ℂ) := by
    intro t
    ext v
    have := (fderiv ℂ (f t) x).toLinearMap.pi_apply_eq_sum_univ v
    simp only [ContinuousLinearMap.coe_coe] at this
    simp only [this, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hcont : ∀ y ∈ U, ContinuousOn (fun t => f t y) (cell n) := fun y hy =>
    hCont.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hy⟩
  have hq : ∀ i, AEStronglyMeasurable (fun t => fderiv ℂ (f t) x (e i))
      (volume.restrict (cell n)) := by
    intro i
    let s : ℕ → ℂ := fun m => ((ε / 2 * (1 / ((m : ℝ) + 1)) : ℝ) : ℂ)
    have hsne : ∀ m, s m ≠ 0 := fun m => by
      have : 0 < ε / 2 * (1 / ((m : ℝ) + 1)) := by positivity
      exact Complex.ofReal_ne_zero.2 this.ne'
    have hs0 : Tendsto s atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hsne⟩
      have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2)
      rw [mul_zero] at h1
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at h2
      exact h2
    have hy : ∀ m, x + s m • e i ∈ U := by
      intro m
      apply hball
      rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
      have h2 : ‖e i‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
        by_cases h : i = j <;> simp [e, h]
      have h3 : ‖s m‖ ≤ ε / 2 := by
        simp only [s, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity)]
        have : 1 / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
        nlinarith
      calc ‖s m‖ * ‖e i‖ ≤ ε / 2 * 1 := mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
        _ < ε := by linarith
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun m t => (s m)⁻¹ • (f t (x + s m • e i) - f t x)) (fun m => ?_) ?_
    · have h := ((hcont _ (hy m)).sub (hcont x hx)).const_smul (s m)⁻¹
      exact h.aestronglyMeasurable measurableSet_cell
    · refine (ae_restrict_iff' measurableSet_cell).2 (Eventually.of_forall fun t ht => ?_)
      have hF : HasFDerivAt (f t) (fderiv ℂ (f t) x) x :=
        ((hHol t ht).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
      have hg : HasDerivAt (fun r : ℂ => x + r • e i) (e i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (e i)).const_add x
      have hd : HasDerivAt (fun r : ℂ => f t (x + r • e i)) (fderiv ℂ (f t) x (e i)) 0 :=
        hF.comp_hasDerivAt_of_eq (0 : ℂ) hg (by simp)
      have := hasDerivAt_iff_tendsto_slope_zero.1 hd
      simpa only [zero_add, zero_smul, add_zero, Function.comp_def] using this.comp hs0
  rw [funext hfun]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hq i).smul_const _

/-- Cauchy estimate for the complex derivative, uniformly over the cell. -/
theorem norm_fderiv_le_cell {U : Set (CVec d)} (hU : IsOpen U) {f : Vec n → CVec d → ℂ}
    (hHol : ∀ t ∈ cell n, DifferentiableOn ℂ (f t) U) {x : CVec d} {r M : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall x (2 * r) ⊆ U)
    (hM : ∀ z ∈ cell n ×ˢ Metric.closedBall x (2 * r), ‖f z.1 z.2‖ ≤ M)
    {t : Vec n} (ht : t ∈ cell n) {z : CVec d} (hz : z ∈ Metric.ball x r) :
    ‖fderiv ℂ (f t) z‖ ≤ M / r := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _)
    (hM (t, x) ⟨ht, Metric.mem_closedBall_self (by linarith)⟩)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set R := r / ‖v‖ with hR
  have hRpos : 0 < R := by positivity
  have hRv : R * ‖v‖ = r := by rw [hR]; field_simp
  have h1 : ‖z - x‖ < r := mem_ball_iff_norm.1 hz
  have hmem : ∀ w : ℂ, ‖w‖ ≤ R → z + w • v ∈ Metric.closedBall x (2 * r) := by
    intro w hw
    rw [mem_closedBall_iff_norm]
    calc ‖z + w • v - x‖ = ‖(z - x) + w • v‖ := by rw [add_sub_right_comm]
      _ ≤ ‖z - x‖ + ‖w • v‖ := norm_add_le _ _
      _ ≤ 2 * r := by
        rw [norm_smul]
        nlinarith [mul_le_mul_of_nonneg_right hw (norm_nonneg v)]
  have hzU : z ∈ U := hsub (by
    rw [mem_closedBall_iff_norm]; linarith)
  have hgd : DifferentiableOn ℂ (fun w : ℂ => f t (z + w • v)) (Metric.closedBall 0 R) :=
    (hHol t ht).comp (by fun_prop : DifferentiableOn ℂ (fun w : ℂ => z + w • v) _)
      fun w hw => hsub (hmem w (by simpa using hw))
  have hdc : DiffContOnCl ℂ (fun w : ℂ => f t (z + w • v)) (Metric.ball 0 R) :=
    ⟨hgd.mono Metric.ball_subset_closedBall, by
      rw [closure_ball _ hRpos.ne']; exact hgd.continuousOn⟩
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdc
    (C := M) fun w hw => hM (t, z + w • v) ⟨ht, hmem w (by simpa using hw.le)⟩
  have hF : HasFDerivAt (f t) (fderiv ℂ (f t) z) z :=
    ((hHol t ht).differentiableAt (hU.mem_nhds hzU)).hasFDerivAt
  have hg : HasDerivAt (fun r : ℂ => z + r • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hd : HasDerivAt (fun w : ℂ => f t (z + w • v)) (fderiv ℂ (f t) z v) 0 :=
    hF.comp_hasDerivAt_of_eq (0 : ℂ) hg (by simp)
  rw [hd.deriv] at hcau
  calc ‖fderiv ℂ (f t) z v‖ ≤ M / R := hcau
    _ = M / r * ‖v‖ := by rw [hR]; field_simp

/-- A holomorphic parameter integral over the compact cell is holomorphic. -/
theorem e_param {U : Set (CVec d)} (hU : IsOpen U) {f : Vec n → CVec d → ℂ}
    (hCont : ContinuousOn (fun z : Vec n × CVec d => f z.1 z.2) (cell n ×ˢ U))
    (hHol : ∀ t ∈ cell n, DifferentiableOn ℂ (f t) U) :
    DifferentiableOn ℂ (fun z => ∫ t in cell n, f t z) U := by
  intro x hx
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hr : 0 < ε / 4 := by positivity
  have hsub : Metric.closedBall x (2 * (ε / 4)) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact (cell n ×ˢ Metric.closedBall x (2 * (ε / 4))) :=
    isCompact_cell.prod (isCompact_closedBall x _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hCont.mono (prod_mono subset_rfl hsub))
  have hcont : ∀ y ∈ U, ContinuousOn (fun t => f t y) (cell n) := fun y hy =>
    hCont.comp (continuousOn_id.prodMk continuousOn_const) fun t ht => ⟨ht, hy⟩
  have hfin : volume.restrict (cell n) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]; exact isCompact_cell.measure_lt_top
  have : IsFiniteMeasure (volume.restrict (cell n)) := ⟨hfin⟩
  have hD := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := volume.restrict (cell n))
    (F := fun y t => f t y) (F' := fun y t => fderiv ℂ (f t) y) (bound := fun _ => M / (ε / 4))
    (s := Metric.ball x (ε / 4)) (Metric.ball_mem_nhds x hr) ?_ ?_ ?_ ?_
    (integrable_const _) ?_
  · exact hD.differentiableAt
  · exact Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy =>
      (hcont y hy).aestronglyMeasurable measurableSet_cell
  · exact (hcont x hx).integrableOn_compact isCompact_cell
  · exact aestronglyMeasurable_fderiv_cell hU hCont hHol hx
  · refine (ae_restrict_iff' measurableSet_cell).2 (Eventually.of_forall fun t ht y hy => ?_)
    exact norm_fderiv_le_cell hU hHol hr hsub hM ht hy
  · refine (ae_restrict_iff' measurableSet_cell).2 (Eventually.of_forall fun t ht y hy => ?_)
    have hyU : y ∈ U := hsub (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (by linarith) hy))
    exact ((hHol t ht).differentiableAt (hU.mem_nhds hyU)).hasFDerivAt

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
