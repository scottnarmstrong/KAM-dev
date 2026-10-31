/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Flow.PicardHolo
public import KAM.Wave.Analytic.Flow.Holomorphic
public import KAM.Wave.Analytic.UniformLimit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The variational equation of the flow (`bpW:w5:flow-calc` (i), steps `c-cont`, `c-var`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

For `h : FlowHyp X V U M δ` and `w ∈ U`:
`D φ^t(w) = I + ∫₀ᵗ DX(φ^σ w) Dφ^σ(w) dσ` (`fderiv_holoFlow_eq`), and `t ↦ Dφ^t(w)` is continuous on
`[-1, 1]` (`continuousOn_fderiv_holoFlow_time`). The proof passes to the limit in the Picard
recursion `picardD_succ` (the derivatives converge pointwise by `holomorphic_of_tendstoUniformlyOn`)
by dominated convergence, using the uniform bound `(M/δ) e^{M/δ}`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

/-- The integrand `DX(φ^σ w) ∘ Dφ^σ(w)` of the variational equation. -/
def flowVarG (X : F → F) (w : F) (σ : ℝ) : F →L[ℂ] F :=
  (fderiv ℂ X (holoFlow X σ w)).comp (fderiv ℂ (holoFlow X σ) w)

theorem tendsto_picardD {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun k => picardD X k t w) atTop (𝓝 (fderiv ℂ (holoFlow X t) w)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h.isOpen_U w hw
  have hsub : ball w (2 * (ε / 2)) ⊆ U := by
    rw [show 2 * (ε / 2) = ε by ring]; exact hball
  have hT := (holomorphic_of_tendstoUniformlyOn h.isOpen_U (fun k => (picard_holo h k).diff t ht)
    (tendstoUniformlyOn_picard_U h ht)).2 (by positivity) hsub
  exact hT.tendsto_at (mem_ball_self (by positivity))

theorem tendsto_picardG {w : F} (hw : w ∈ U) {σ : ℝ} (hσ : σ ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun k => picardG X w k σ) atTop (𝓝 (flowVarG X w σ)) := by
  have hV : holoFlow X σ w ∈ V := h.mem_V_of_ball hw (holoFlow_mem_ball h hw hσ)
  have h1 : Tendsto (fun k => fderiv ℂ X (wavePicard X w k σ)) atTop
      (𝓝 (fderiv ℂ X (holoFlow X σ w))) :=
    (((continuousOn_fderiv_of_holomorphic h.isOpen_V h.holo).continuousAt
      (h.isOpen_V.mem_nhds hV)).tendsto).comp (tendsto_picard h hw hσ)
  have h2 := tendsto_picardD h hw hσ
  have hc := (ContinuousLinearMap.compL ℂ F F F).continuous₂.tendsto
    (fderiv ℂ X (holoFlow X σ w), fderiv ℂ (holoFlow X σ) w)
  exact hc.comp (h1.prodMk_nhds h2)

theorem aestronglyMeasurable_flowVarG {w : F} (hw : w ∈ U) :
    AEStronglyMeasurable (flowVarG X w) (volume.restrict (Icc (-1 : ℝ) 1)) :=
  aestronglyMeasurable_of_tendsto_ae atTop
    (fun k => (continuousOn_picardG h (picard_holo h k) hw).aestronglyMeasurable
      measurableSet_Icc)
    (ae_restrict_of_forall_mem measurableSet_Icc fun _ hσ => tendsto_picardG h hw hσ)

theorem norm_flowVarG_le {w : F} (hw : w ∈ U) {σ : ℝ} (hσ : σ ∈ Icc (-1 : ℝ) 1) :
    ‖flowVarG X w σ‖ ≤ M / δ * Real.exp (M / δ) := by
  refine le_of_tendsto (tendsto_picardG h hw hσ).norm (Eventually.of_forall fun k => ?_)
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  refine (norm_picardG_le h (picard_holo h k) hw hσ).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hL
  have : |σ| ≤ 1 := abs_le.mpr ⟨hσ.1, hσ.2⟩
  nlinarith

theorem intervalIntegrable_flowVarG {w : F} (hw : w ∈ U) :
    IntervalIntegrable (flowVarG X w) volume (-1) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
  refine Integrable.of_bound (C := M / δ * Real.exp (M / δ)) (aestronglyMeasurable_flowVarG h hw) ?_
  exact ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ => norm_flowVarG_le h hw hσ

/-- **The variational equation** (`bpW:w5:flow-calc` (i), step `c-var`). -/
theorem fderiv_holoFlow_eq {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    fderiv ℂ (holoFlow X t) w =
      ContinuousLinearMap.id ℂ F + ∫ σ in (0 : ℝ)..t, flowVarG X w σ := by
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have hlim := (tendsto_picardD h hw ht).comp (tendsto_add_atTop_nat 1)
  have hdom : Tendsto (fun k => ∫ σ in (0 : ℝ)..t, picardG X w k σ) atTop
      (𝓝 (∫ σ in (0 : ℝ)..t, flowVarG X w σ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M / δ * Real.exp (M / δ)) (Eventually.of_forall fun k => ?_)
      (Eventually.of_forall fun k => Eventually.of_forall fun σ hσ => ?_) intervalIntegrable_const
      (Eventually.of_forall fun σ hσ => tendsto_picardG h hw (uIoc_subset_Icc ht hσ))
    · exact ((continuousOn_picardG h (picard_holo h k) hw).mono
        (uIoc_subset_Icc ht)).aestronglyMeasurable measurableSet_uIoc
    · have hσ' := uIoc_subset_Icc ht hσ
      refine (norm_picardG_le h (picard_holo h k) hw hσ').trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hL
      have : |σ| ≤ 1 := abs_le.mpr ⟨hσ'.1, hσ'.2⟩
      nlinarith
  have hstep : (fun k => picardD X (k + 1) t w) =
      fun k => ContinuousLinearMap.id ℂ F + ∫ σ in (0 : ℝ)..t, picardG X w k σ :=
    funext fun k => picardD_succ h (picard_holo h k) hw ht
  have h2 : Tendsto (fun k => picardD X (k + 1) t w) atTop
      (𝓝 (ContinuousLinearMap.id ℂ F + ∫ σ in (0 : ℝ)..t, flowVarG X w σ)) := by
    rw [hstep]; exact hdom.const_add _
  exact tendsto_nhds_unique hlim h2

/-- `t ↦ Dφ^t(w)` is continuous (`bpW:w5:flow-calc` (i), step `c-cont`). -/
theorem continuousOn_fderiv_holoFlow_time {w : F} (hw : w ∈ U) :
    ContinuousOn (fun t => fderiv ℂ (holoFlow X t) w) (Icc (-1 : ℝ) 1) := by
  have hI : Icc (-1 : ℝ) 1 = uIcc (-1) 1 := (uIcc_of_le (by norm_num)).symm
  have hc : ContinuousOn (fun b => ∫ x in (0 : ℝ)..b, flowVarG X w x) (uIcc (-1) 1) :=
    intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_flowVarG h hw)
      (by rw [mem_uIcc]; left; constructor <;> norm_num)
  rw [hI]
  exact (continuousOn_const.add hc).congr fun t ht => fderiv_holoFlow_eq h hw (by rwa [hI])

end KAM.Wave
