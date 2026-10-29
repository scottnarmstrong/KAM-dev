/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.LimitProps

/-! # P11B limit: the output record `SelectionLimit` and `limit_map`

Fixed-strip zero-section limits of the finite compositions (`bpP:p11a:limit-map`): holomorphy and
uniform convergence of values and derivatives on `T_(s/4)`, reality and periodicity of the angle
defect, the angle/action bounds and the Lipschitz bound `2⁻¹¹` of the defect. No common positive
action radius is asserted.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- Original coordinates, with the parameter in the action block. -/
def selectionEvaluation (u : SelectionR n → SelectionR n → Phase n)
    (b θ : SelectionR n) : Phase n := (θ, b) + u b θ

def sec_limit_data (u : SelectionR n → SelectionR n → Phase n) := selectionEvaluation u

/-- Fixed-strip zero-section limits; no common positive action radius is asserted. -/
structure SelectionLimit (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionComposition d f a where
  limitC : SelectionR n → SelectionC n → SelectionPhaseC n
  limit_holo : ∀ b ∈ Kinf, DifferentiableOn ℂ (limitC b) (complexStrip n (d.strip / 4))
  limit_equivariant : ∀ b ∈ Kinf, ∀ θ ∈ complexStrip n (d.strip / 4),
    ∀ k : Fin n → ℤ, limitC b (θ + (fun i => (k i : ℂ))) =
      limitC b θ + ((fun i => (k i : ℂ)), 0)
  limit_uniform : ∀ b ∈ Kinf, TendstoUniformlyOn
    (fun ν θ => selectionCompose toSelectionChain (selectionReal b) ν (θ, 0))
    (limitC b) atTop (complexStrip n (d.strip / 4))
  derivative_uniform : ∀ b ∈ Kinf, TendstoUniformlyOn
    (fun ν θ => fderiv ℂ
      (fun v => selectionCompose toSelectionChain (selectionReal b) ν (v, 0)) θ)
    (fderiv ℂ (limitC b)) atTop (complexStrip n (d.strip / 4))
  defect : SelectionR n → SelectionR n → Phase n
  limit_real : ∀ b ∈ Kinf, ∀ θ,
    limitC b (selectionReal θ) = phaseToC ((θ, 0) + defect b θ)
  periodic : ∀ b ∈ Kinf, ∀ θ, ∀ k : Fin n → ℤ,
    defect b (θ + (fun i => (k i : ℝ))) = defect b θ
  complex_angle_bound : ∀ b ∈ Kinf, ∀ θ ∈ complexStrip n (d.strip / 4),
    ‖(limitC b θ).1 - θ‖ ≤ ∑' j, selectionA a j
  complex_action_bound : ∀ b ∈ Kinf, ∀ θ ∈ complexStrip n (d.strip / 4),
    ‖(limitC b θ).2‖ ≤ ∑' j, selectionAlpha a j
  complex_derivative_bound : ∀ b ∈ Kinf, ∀ θ ∈ complexStrip n (d.strip / 4),
    ‖fderiv ℂ (fun v => limitC b v - (v, 0)) θ‖ ≤ (2 : ℝ)⁻¹ ^ 11
  angle_lipschitz : ∀ b ∈ Kinf, ∀ θ θ',
    ‖defect b θ - defect b θ'‖ ≤ (2 : ℝ)⁻¹ ^ 11 * ‖θ - θ'‖

section Assemble
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
variable (cx : WeakBudgetCtx d a) (c : SelectionComposition d f a) {b : SelectionR n}

include cx

theorem selectionLim_real_im (hb : b ∈ c.Kinf) (θ : SelectionR n) (i : Fin n) :
    ((selectionLimMap c.toSelectionChain b (selectionReal θ)).1 i).im = 0 ∧
    ((selectionLimMap c.toSelectionChain b (selectionReal θ)).2 i).im = 0 := by
  have hθ : selectionReal θ ∈ complexStrip n (a.strip / 4) :=
    selectionReal_mem_complexStrip (by linarith [cx.hyp.hstrip]) θ
  have hst : ∀ ν, ((selectionLimStage c.toSelectionChain b ν (selectionReal θ)).1 i).im = 0 ∧
      ((selectionLimStage c.toSelectionChain b ν (selectionReal θ)).2 i).im = 0 := fun ν => by
    have hz : phaseToC ((θ, 0) : Phase n) = (selectionReal θ, 0) := by
      ext j <;> simp [phaseToC, selectionReal]
    have hm := selectionLim_mem cx c hb ν (selectionLim_sub_mem cx hθ)
    rw [← hz] at hm
    obtain ⟨w, hw⟩ := c.composition_real ν (θ, 0) b hm
    unfold selectionLimStage
    rw [← hz, hw]
    simp [phaseToC]
  have ht := selectionLim_tendsto cx c hb hθ
  have h1 : Continuous fun z : SelectionPhaseC n => (z.1 i).im :=
    Complex.continuous_im.comp ((continuous_apply i).comp continuous_fst)
  have h2 : Continuous fun z : SelectionPhaseC n => (z.2 i).im :=
    Complex.continuous_im.comp ((continuous_apply i).comp continuous_snd)
  refine ⟨tendsto_nhds_unique ((h1.tendsto _).comp ht) ?_,
    tendsto_nhds_unique ((h2.tendsto _).comp ht) ?_⟩
  · simp only [Function.comp_def, (hst _).1]
    exact tendsto_const_nhds
  · simp only [Function.comp_def, (hst _).2]
    exact tendsto_const_nhds

theorem selectionLim_defect_spec (hb : b ∈ c.Kinf) (θ : SelectionR n) :
    selectionLimMap c.toSelectionChain b (selectionReal θ) =
      phaseToC ((θ, 0) + selectionLimDefect c.toSelectionChain b θ) := by
  have h := selectionLim_real_im cx c hb θ
  refine Prod.ext (funext fun i => Complex.ext ?_ ?_) (funext fun i => Complex.ext ?_ ?_)
  · simp [phaseToC, selectionLimDefect, selectionRe]
  · simp [phaseToC, selectionLimDefect, (h i).1]
  · simp [phaseToC, selectionLimDefect, selectionRe]
  · simp [phaseToC, selectionLimDefect, (h i).2]

theorem selectionLim_defect_periodic (hb : b ∈ c.Kinf) (θ : SelectionR n) (k : Fin n → ℤ) :
    selectionLimDefect c.toSelectionChain b (θ + fun i => (k i : ℝ)) =
      selectionLimDefect c.toSelectionChain b θ := by
  have hθ : selectionReal θ ∈ complexStrip n (a.strip / 4) :=
    selectionReal_mem_complexStrip (by linarith [cx.hyp.hstrip]) θ
  have e : selectionReal (θ + fun i => (k i : ℝ)) =
      selectionReal θ + fun i => (k i : ℂ) := by
    funext i; simp [selectionReal]
  unfold selectionLimDefect
  rw [e, selectionLim_equivariant cx c hb hθ k]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp [selectionRe]
  · simp [selectionRe]

theorem selectionLim_defect_lipschitz (hb : b ∈ c.Kinf) (θ θ' : SelectionR n) :
    ‖selectionLimDefect c.toSelectionChain b θ - selectionLimDefect c.toSelectionChain b θ'‖ ≤
      (2 : ℝ)⁻¹ ^ 11 * ‖θ - θ'‖ := by
  have hs : 0 < a.strip / 4 := by linarith [cx.hyp.hstrip]
  set g : SelectionC n → SelectionPhaseC n :=
    fun v => selectionLimMap c.toSelectionChain b v - (v, 0) with hg
  have hgd : ∀ v ∈ complexStrip n (a.strip / 4), DifferentiableAt ℂ g v := fun v hv =>
    ((selectionLim_holo cx c hb).1.differentiableAt
      ((KAM.isOpen_complexStrip n _).mem_nhds hv)).sub
      ((hasFDerivAt_id v).prodMk (hasFDerivAt_const (0 : SelectionC n) v)).differentiableAt
  have hmv := (KAM.convex_complexStrip n (a.strip / 4)).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℂ) hgd (fun v hv => selectionLim_derivative_bound cx c hb hv)
    (selectionReal_mem_complexStrip hs θ') (selectionReal_mem_complexStrip hs θ)
  have hgdef : ∀ θ : SelectionR n, g (selectionReal θ) =
      phaseToC (selectionLimDefect c.toSelectionChain b θ) := fun θ => by
    have h := selectionLim_defect_spec cx c hb θ
    have hz : phaseToC ((θ, 0) : Phase n) = (selectionReal θ, 0) := by
      ext j <;> simp [phaseToC, selectionReal]
    rw [phaseToC_eq_realInclusion₂, map_add, ← phaseToC_eq_realInclusion₂, hz] at h
    rw [hg]
    simp only
    rw [h]
    abel
  have hn : ‖selectionReal θ - selectionReal θ'‖ = ‖θ - θ'‖ := by
    rw [← norm_selectionReal]
    congr 1
    funext i; simp [selectionReal]
  rw [hgdef, hgdef] at hmv
  rw [← norm_realInclusion₂, map_sub, ← phaseToC_eq_realInclusion₂,
    ← phaseToC_eq_realInclusion₂, ← hn]
  exact hmv

include c in
/-- Assembly of the limit record from the composition record (source `limit_map`). -/
theorem selectionLimit_of_composition : Nonempty (SelectionLimit d f a) := by
  have hst : d.strip = a.strip := cx.hstrip.symm
  refine ⟨{ c with
    limitC := fun b => selectionLimMap c.toSelectionChain b
    limit_holo := fun b hb => by
      rw [hst]; exact (selectionLim_holo cx c hb).1
    limit_equivariant := fun b hb θ hθ k => by
      rw [hst] at hθ; exact selectionLim_equivariant cx c hb hθ k
    limit_uniform := fun b hb => by
      rw [hst]; exact selectionLim_unif cx c hb
    derivative_uniform := fun b hb => by
      rw [hst]
      refine (selectionLim_dunif cx c hb).congr_right fun θ hθ => ?_
      exact ((selectionLim_holo cx c hb).2 θ hθ).symm
    defect := fun b θ => selectionLimDefect c.toSelectionChain b θ
    limit_real := fun b hb θ => selectionLim_defect_spec cx c hb θ
    periodic := fun b hb θ k => selectionLim_defect_periodic cx c hb θ k
    complex_angle_bound := fun b hb θ hθ => by
      rw [hst] at hθ; exact selectionLim_angle_bound cx c hb hθ
    complex_action_bound := fun b hb θ hθ => by
      rw [hst] at hθ; exact selectionLim_action_bound cx c hb hθ
    complex_derivative_bound := fun b hb θ hθ => by
      rw [hst] at hθ; exact selectionLim_derivative_bound cx c hb hθ
    angle_lipschitz := fun b hb θ θ' => selectionLim_defect_lipschitz cx c hb θ θ' }⟩

end Assemble

theorem limit_map (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionLimit d f (selectionAdapted d ε)) := by
  obtain ⟨hadm, hs, -⟩ := free_radius d ε he hsmall
  have he' : 0 < (selectionAdapted d ε).ε₀ := by
    show 0 < 2 * ε
    positivity
  obtain ⟨o⟩ := parameter_selection_adapted d ε he hsmall f hf
  have cx := weakBudgetCtx_of d (selectionAdapted d ε) hadm rfl rfl rfl rfl rfl rfl hs he'
  obtain ⟨c⟩ := selectionComposition_of_output cx o
  exact selectionLimit_of_composition cx c

end KAM.Planetary

end
