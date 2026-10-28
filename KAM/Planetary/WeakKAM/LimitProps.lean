/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.LimitSeries
public import KAM.Planetary.WeakKAM.ExtensionNorm
public import KAM.Planetary.WeakKAM.IterationStage

/-! # P11B limit map: properties of the zero-section limit

Equivariance, the exported angle and action bounds, the derivative bound `‖D(Φ - id)‖ ≤ 2⁻¹¹`
(source step `lm-bounds`), reality of the limit on the real torus and the Lipschitz bound of the
angle defect, all obtained by passing to the limit in the finite-stage estimates of
`SelectionComposition` on the strip `T_(s/4)`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The angle defect of the limit map on the real torus, in real phase coordinates. -/
def selectionLimDefect (c : SelectionChain n) (b : SelectionR n) (θ : SelectionR n) : Phase n :=
  (selectionRe (selectionLimMap c b (selectionReal θ)).1 - θ,
    selectionRe (selectionLimMap c b (selectionReal θ)).2)

theorem selectionReal_mem_complexStrip {ρ : ℝ} (hρ : 0 < ρ) (θ : SelectionR n) :
    selectionReal θ ∈ complexStrip n ρ := fun i => by simpa [selectionReal] using hρ

section Props
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
variable (cx : WeakBudgetCtx d a) (c : SelectionComposition d f a) {b : SelectionR n}

include cx

theorem selectionLim_sub_mem {θ : SelectionC n} (hθ : θ ∈ complexStrip n (a.strip / 4)) :
    θ ∈ complexStrip n (a.strip / 2) := fun i => (hθ i).trans (by linarith [cx.hyp.hstrip])

theorem selectionLim_tendsto (hb : b ∈ c.Kinf) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 4)) :
    Tendsto (fun ν => selectionLimStage c.toSelectionChain b ν θ) atTop
      (𝓝 (selectionLimMap c.toSelectionChain b θ)) :=
  (selectionLim_unif cx c hb).tendsto_at hθ

theorem selectionLim_equivariant (hb : b ∈ c.Kinf) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 4)) (k : Fin n → ℤ) :
    selectionLimMap c.toSelectionChain b (θ + fun i => (k i : ℂ)) =
      selectionLimMap c.toSelectionChain b θ + ((fun i => (k i : ℂ)), 0) := by
  have h1 := selectionLim_tendsto cx c hb (add_intCast_mem_complexStrip hθ k)
  have h2 := (selectionLim_tendsto cx c hb hθ).add_const (((fun i => (k i : ℂ)), 0) :
    SelectionPhaseC n)
  have he : ∀ ν, selectionLimStage c.toSelectionChain b ν (θ + fun i => (k i : ℂ)) =
      selectionLimStage c.toSelectionChain b ν θ + ((fun i => (k i : ℂ)), 0) := fun ν => by
    have := c.composition_periodic ν ((θ, 0), selectionReal b)
      (selectionLim_mem cx c hb ν (selectionLim_sub_mem cx hθ)) k
    have e : ((θ + fun i => (k i : ℂ), 0) : SelectionPhaseC n) =
        (θ, 0) + ((fun i => (k i : ℂ)), 0) := by ext <;> simp
    unfold selectionLimStage
    rw [e]
    exact this
  simp only [he] at h1
  exact tendsto_nhds_unique h1 h2

theorem selectionLim_angle_bound (hb : b ∈ c.Kinf) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 4)) :
    ‖(selectionLimMap c.toSelectionChain b θ).1 - θ‖ ≤ ∑' j, selectionA a j := by
  obtain ⟨hA, -, -, -⟩ := wbud_sums_Aα cx
  have hc : Continuous fun z : SelectionPhaseC n => ‖z.1 - θ‖ :=
    (continuous_fst.sub continuous_const).norm
  have ht := (hc.tendsto _).comp (selectionLim_tendsto cx c hb hθ)
  refine le_of_tendsto' ht fun ν => ?_
  have := c.composition_angle ν ((θ, 0), selectionReal b)
    (selectionLim_mem cx c hb ν (selectionLim_sub_mem cx hθ))
  exact this.trans (hA.sum_le_tsum _ fun j _ => (wbud_stage cx.hyp j).2.1)

theorem selectionLim_action_bound (hb : b ∈ c.Kinf) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 4)) :
    ‖(selectionLimMap c.toSelectionChain b θ).2‖ ≤ ∑' j, selectionAlpha a j := by
  obtain ⟨-, hα, -, -⟩ := wbud_sums_Aα cx
  have ht := (continuous_snd.norm.tendsto _).comp (selectionLim_tendsto cx c hb hθ)
  refine le_of_tendsto' ht fun ν => ?_
  have := c.composition_action ν ((θ, 0), selectionReal b)
    (selectionLim_mem cx c hb ν (selectionLim_sub_mem cx hθ))
  simp only [sub_zero] at this
  refine this.trans (hα.sum_le_tsum _ fun j _ => ?_)
  have hs := wbud_s_pos cx.hyp j
  have hk := (wbud_stage cx.hyp j).2.2.2.1
  rw [(wbud_stage cx.hyp j).2.2.2.2.2.1]
  positivity

theorem selectionLim_fiber_diffAt (hb : b ∈ c.Kinf) (ν : ℕ) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 2)) :
    DifferentiableAt ℂ (selectionCompose c.toSelectionChain (selectionReal b) ν) (θ, 0) := by
  have hx := selectionLim_mem cx c hb ν hθ
  have h := (c.composition_holo ν).differentiableAt
    ((isOpen_selectionCompDom a c.K ν).mem_nhds hx)
  have hf : DifferentiableAt ℂ (fun v : SelectionPhaseC n => (v, selectionReal b)) (θ, 0) :=
    differentiableAt_id.prodMk (differentiableAt_const _)
  have h2 := DifferentiableAt.comp (θ, 0) h hf
  exact h2

omit cx in
theorem norm_inl_apply (v : SelectionC n) :
    ‖ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) v‖ = ‖v‖ := by
  simp [Prod.norm_def]

theorem selectionLim_stage_fderiv (hb : b ∈ c.Kinf) (ν : ℕ) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 2)) :
    fderiv ℂ (selectionLimStage c.toSelectionChain b ν) θ =
      (fderiv ℂ (selectionCompose c.toSelectionChain (selectionReal b) ν) (θ, 0)).comp
        (ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n)) := by
  have hi : HasFDerivAt (fun v : SelectionC n => ((v, 0) : SelectionPhaseC n))
      (ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n)) θ :=
    (hasFDerivAt_id θ).prodMk (hasFDerivAt_const (0 : SelectionC n) θ)
  exact ((selectionLim_fiber_diffAt cx c hb ν hθ).hasFDerivAt.comp θ hi).fderiv

theorem selectionLim_derivative_bound (hb : b ∈ c.Kinf) {θ : SelectionC n}
    (hθ : θ ∈ complexStrip n (a.strip / 4)) :
    ‖fderiv ℂ (fun v => selectionLimMap c.toSelectionChain b v - (v, 0)) θ‖ ≤
      (2 : ℝ)⁻¹ ^ 11 := by
  have hθ2 := selectionLim_sub_mem cx hθ
  have hopen : (complexStrip n (a.strip / 4)) ∈ 𝓝 θ :=
    (KAM.isOpen_complexStrip n _).mem_nhds hθ
  have hdl := ((selectionLim_holo cx c hb).1.differentiableAt hopen)
  have hi : HasFDerivAt (fun v : SelectionC n => ((v, 0) : SelectionPhaseC n))
      (ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n)) θ :=
    (hasFDerivAt_id θ).prodMk (hasFDerivAt_const (0 : SelectionC n) θ)
  have e : fderiv ℂ (fun v => selectionLimMap c.toSelectionChain b v - (v, 0)) θ =
      selectionLimDMap c.toSelectionChain b θ -
        ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) := by
    rw [fderiv_fun_sub hdl hi.differentiableAt, (selectionLim_holo cx c hb).2 θ hθ, hi.fderiv]
  rw [e]
  have ht := ((continuous_norm.tendsto _).comp
    (((selectionLim_dunif cx c hb).tendsto_at hθ).sub_const
      (ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n))))
  refine le_of_tendsto' ht fun ν => ?_
  simp only [comp_apply]
  rw [selectionLim_stage_fderiv cx c hb ν hθ2]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hL := c.composition_small ν ((θ, 0), selectionReal b)
    (selectionLim_mem cx c hb ν hθ2)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  have h1 := (fderiv ℂ (selectionCompose c.toSelectionChain (selectionReal b) ν) (θ, 0) -
    ContinuousLinearMap.id ℂ (SelectionPhaseC n)).le_opNorm
      (ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) v)
  rw [norm_inl_apply] at h1
  have e2 : fderiv ℂ (selectionCompose c.toSelectionChain (selectionReal b) ν) (θ, 0)
      (ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) v) -
        ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) v =
      (fderiv ℂ (selectionCompose c.toSelectionChain (selectionReal b) ν) (θ, 0) -
        ContinuousLinearMap.id ℂ (SelectionPhaseC n))
          (ContinuousLinearMap.inl ℂ (SelectionC n) (SelectionC n) v) := rfl
  rw [e2]
  exact h1.trans (by gcongr)

end Props

end KAM.Planetary

end
