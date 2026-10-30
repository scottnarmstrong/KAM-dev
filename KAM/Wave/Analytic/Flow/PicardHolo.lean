/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.Flow.Picard
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Holomorphy of the Picard iterates

Blueprint-W `bpW:w1:flow`, step `stepW:w1:picardholo` (package W1-ANALYTIC). This is source-faithful
infrastructure used by several nodes; the dependency graph is still being built.

By induction on `k`: for `t ∈ [-1, 1]`, `w ↦ φ_k(w, t)` is holomorphic on `U`, its derivative
`D_w φ_k(w, t)` has norm at most `e^{L |t|}` (`L = M / δ`) and is continuous in `t`
(`KAM.Wave.picard_holo`). The step differentiates under the integral sign with
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`; the integrand's derivative is
`DX(φ_k) ∘ D_w φ_k`, dominated by `L e^L` because `φ_k(w, σ) ∈ B(w, δ)` where `‖DX‖ ≤ L`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory intervalIntegral Filter Topology
open scoped Interval

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {X : F → F} {V U : Set F} {M δ : ℝ}

/-- The `w`-derivative of the `k`-th Picard iterate at time `t`. -/
def picardD (X : F → F) (k : ℕ) (t : ℝ) (w : F) : F →L[ℂ] F :=
  fderiv ℂ (fun w' => picard X w' k t) w

/-- The induction hypothesis of `KAM.Wave.picard_holo`. -/
structure PicardInv (X : F → F) (U : Set F) (L : ℝ) (k : ℕ) : Prop where
  diff : ∀ t ∈ Icc (-1 : ℝ) 1, DifferentiableOn ℂ (fun w' => picard X w' k t) U
  bound : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ w ∈ U, ‖picardD X k t w‖ ≤ Real.exp (L * |t|)
  cont : ∀ w ∈ U, ContinuousOn (fun t => picardD X k t w) (Icc (-1) 1)

variable (h : FlowHyp X V U M δ)
include h

theorem picardInv_zero : PicardInv X U (M / δ) 0 where
  diff := fun _ _ => differentiableOn_id
  bound := fun t _ w _ => by
    have : picardD X 0 t w = ContinuousLinearMap.id ℂ F := by
      simp [picardD]
    rw [this]
    refine (ContinuousLinearMap.norm_id_le).trans ?_
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by
      have := div_nonneg h.M_pos.le h.delta_pos.le
      positivity)
  cont := fun w _ => by
    have : (fun t => picardD X 0 t w) = fun _ => ContinuousLinearMap.id ℂ F := by
      funext t; simp [picardD]
    rw [this]; exact continuousOn_const


/-- The `w`-derivative of the integrand `X (φ_k (w, σ))`. -/
def picardG (X : F → F) (w : F) (k : ℕ) (σ : ℝ) : F →L[ℂ] F :=
  (fderiv ℂ X (picard X w k σ)).comp (picardD X k σ w)

theorem continuousOn_picardG {k : ℕ} (hk : PicardInv X U (M / δ) k) {w : F} (hw : w ∈ U) :
    ContinuousOn (picardG X w k) (Icc (-1) 1) := by
  have h1 : ContinuousOn (fun σ => fderiv ℂ X (picard X w k σ)) (Icc (-1) 1) :=
    (continuousOn_fderiv_of_holomorphic h.isOpen_V h.holo).comp (norm_picard_sub_le h hw k).2
      fun σ hσ => h.mem_V hw (picard_mem_ball h hw k hσ)
  exact h1.clm_comp (hk.cont w hw)

theorem norm_picardG_le {k : ℕ} (hk : PicardInv X U (M / δ) k) {w : F} (hw : w ∈ U) {σ : ℝ}
    (hσ : σ ∈ Icc (-1 : ℝ) 1) : ‖picardG X w k σ‖ ≤ M / δ * Real.exp (M / δ * |σ|) :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (h.fderiv_le hw (picard_mem_ball h hw k hσ)) (hk.bound σ hσ w hw)
      (norm_nonneg _) (div_nonneg h.M_pos.le h.delta_pos.le))

/-- The derivative of `Φ_{k+1}` in `w`, by differentiation under the integral sign. -/
theorem hasFDerivAt_picard_succ {k : ℕ} (hk : PicardInv X U (M / δ) k) {w : F} (hw : w ∈ U)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    HasFDerivAt (fun w' => picard X w' (k + 1) t)
      (ContinuousLinearMap.id ℂ F + ∫ σ in (0 : ℝ)..t, picardG X w k σ) w := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp h.isOpen_U w hw
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have hmeas : ∀ x ∈ U, AEStronglyMeasurable (fun σ => X (picard X x k σ))
      (volume.restrict (Ι 0 t)) := fun x hx =>
    ((continuousOn_X_picard h hx k).mono (uIoc_subset_Icc ht)).aestronglyMeasurable measurableSet_uIoc
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
    (μ := volume) (a := 0) (b := t) (s := ball w ε) (x₀ := w)
    (F := fun x σ => X (picard X x k σ)) (F' := fun x σ => picardG X x k σ)
    (bound := fun _ => M / δ * Real.exp (M / δ))
    (ball_mem_nhds w hε)
    (Filter.eventually_of_mem (h.isOpen_U.mem_nhds hw) fun x hx => hmeas x hx)
    (((continuousOn_X_picard h hw k).mono (uIcc_subset_Icc' ht)).intervalIntegrable)
    (((continuousOn_picardG h hk hw).mono (uIoc_subset_Icc ht)).aestronglyMeasurable
      measurableSet_uIoc)
    (Filter.Eventually.of_forall fun σ hσ x hx => by
      have hxU : x ∈ U := hεU hx
      have hσ' := uIoc_subset_Icc ht hσ
      refine (norm_picardG_le h hk hxU hσ').trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hL
      have : |σ| ≤ 1 := abs_le.mpr ⟨hσ'.1, hσ'.2⟩
      nlinarith)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun σ hσ x hx => by
      have hxU : x ∈ U := hεU hx
      have hσ' := uIoc_subset_Icc ht hσ
      have hz : picard X x k σ ∈ V := h.mem_V hxU (picard_mem_ball h hxU k hσ')
      have h1 : HasFDerivAt X (fderiv ℂ X (picard X x k σ)) (picard X x k σ) :=
        (h.holo.differentiableAt (h.isOpen_V.mem_nhds hz)).hasFDerivAt
      have h2 : HasFDerivAt (fun x' => picard X x' k σ) (picardD X k σ x) x :=
        ((hk.diff σ hσ').differentiableAt (h.isOpen_U.mem_nhds hxU)).hasFDerivAt
      exact h1.comp x h2)
  exact (hasFDerivAt_id w).add hmain


theorem picardD_succ {k : ℕ} (hk : PicardInv X U (M / δ) k) {w : F} (hw : w ∈ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    picardD X (k + 1) t w = ContinuousLinearMap.id ℂ F + ∫ σ in (0 : ℝ)..t, picardG X w k σ :=
  (hasFDerivAt_picard_succ h hk hw ht).fderiv

/-- Blueprint `stepW:w1:picardholo`: the Picard iterates are holomorphic in `w` with
`‖D_w φ_k‖ ≤ e^{L |t|}`, and `D_w φ_k` is continuous in `t`. -/
theorem picard_holo : ∀ k : ℕ, PicardInv X U (M / δ) k
  | 0 => picardInv_zero h
  | k + 1 => by
    have hk := picard_holo k
    have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
    refine ⟨fun t ht => fun w hw => (hasFDerivAt_picard_succ h hk hw ht).differentiableAt
      |>.differentiableWithinAt, fun t ht w hw => ?_, fun w hw => ?_⟩
    · rw [picardD_succ h hk hw ht]
      have h1 : ‖∫ σ in (0 : ℝ)..t, picardG X w k σ‖ ≤ Real.exp (M / δ * |t|) - 1 :=
        norm_integral_le_exp fun σ hσ => norm_picardG_le h hk hw (uIoc_subset_Icc ht hσ)
      calc ‖ContinuousLinearMap.id ℂ F + ∫ σ in (0 : ℝ)..t, picardG X w k σ‖
          ≤ ‖ContinuousLinearMap.id ℂ F‖ + ‖∫ σ in (0 : ℝ)..t, picardG X w k σ‖ := norm_add_le _ _
        _ ≤ 1 + (Real.exp (M / δ * |t|) - 1) :=
            add_le_add ContinuousLinearMap.norm_id_le h1
        _ = Real.exp (M / δ * |t|) := by ring
    · have : ContinuousOn (fun t => ContinuousLinearMap.id ℂ F + ∫ σ in (0 : ℝ)..t, picardG X w k σ)
          (Icc (-1) 1) :=
        continuousOn_const.add (continuousOn_primitive (continuousOn_picardG h hk hw))
      refine this.congr fun t ht => ?_
      exact picardD_succ h hk hw ht

end KAM.Wave
