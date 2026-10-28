/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.CompositionStep

/-! # P11B composition: quantitative bounds

The derivative product recursion `D(C_{ν+1}) - 1 = (D C_ν - 1) D X_ν + (D X_ν - 1)` gives
`‖D C_ν - 1‖ ≤ exp (∑_{j<ν} m_j) - 1 ≤ 2⁻¹¹`; the angle and action defects add up stage by stage,
and the increment `C_{ν+1} - C_ν` is bounded by the mean value theorem on the convex fibre
(source steps `co-deriv`, `co-disp`, `co-inc`).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

section Bounds
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}

theorem selectionComp_derivative (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a)
    (ν : ℕ) : ∀ x ∈ selectionCompDom a o.K ν,
    ‖fderiv ℂ (selectionCompose o.toSelectionChain x.2 ν) x.1 -
      ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ ≤
      Real.exp (∑ j ∈ Finset.range ν, selectionMapBudget a j) - 1 := by
  induction ν with
  | zero =>
    intro x _
    simp [selectionCompose]
  | succ ν ih =>
    rintro ⟨z, b⟩ hx
    have hL := ih _ (selectionComp_map_mem cx o ν hx)
    have hM := o.map_derivative_bound ν (z, b) hx
    simp only at hL hM
    rw [selectionComp_fderiv_succ cx o ν hx]
    set L := fderiv ℂ (selectionCompose o.toSelectionChain b ν) (o.X ν b z)
    set M := fderiv ℂ (o.X ν b) z
    set S := ∑ j ∈ Finset.range ν, selectionMapBudget a j
    set m := selectionMapBudget a ν
    have hid : ‖ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have hMn : ‖M‖ ≤ m + 1 := by
      have := norm_le_insert' M (ContinuousLinearMap.id ℂ (SelectionPhaseC n))
      linarith
    have hE : 0 ≤ Real.exp S - 1 := (norm_nonneg _).trans hL
    have e : L.comp M - ContinuousLinearMap.id ℂ (SelectionPhaseC n) =
        (L - ContinuousLinearMap.id ℂ (SelectionPhaseC n)).comp M +
          (M - ContinuousLinearMap.id ℂ (SelectionPhaseC n)) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [sub_apply, ContinuousLinearMap.comp_apply,
        add_apply, ContinuousLinearMap.id_apply]
      abel
    rw [e, Finset.sum_range_succ, Real.exp_add]
    calc _ ≤ ‖(L - ContinuousLinearMap.id ℂ (SelectionPhaseC n)).comp M‖ +
          ‖M - ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ := norm_add_le _ _
      _ ≤ ‖L - ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ * ‖M‖ + m :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) hM
      _ ≤ (Real.exp S - 1) * (m + 1) + m :=
        add_le_add (mul_le_mul hL hMn (norm_nonneg _) hE) le_rfl
      _ ≤ (Real.exp S - 1) * Real.exp m + m := by
        have := Real.add_one_le_exp m
        nlinarith
      _ ≤ Real.exp S * Real.exp m - 1 := by
        have := Real.add_one_le_exp m
        nlinarith

/-- The partial sums of the map budgets stay below the exported total. -/
theorem selectionComp_budget_sum_le (cx : WeakBudgetCtx d a) (ν : ℕ) :
    ∑ j ∈ Finset.range ν, selectionMapBudget a j ≤ (2 : ℝ)⁻¹ ^ 12 := by
  obtain ⟨-, -, hsM, -, hM, -⟩ := wbud_exported cx
  have h0 : ∀ j, 0 ≤ selectionMapBudget a j := fun j => by
    have hκ0 := (wbud_stage cx.hyp j).2.2.2.1
    have := wbud_σ_pos cx.hyp j
    have := wbud_s_pos cx.hyp j
    unfold selectionMapBudget
    positivity
  exact (hsM.sum_le_tsum _ fun j _ => h0 j).trans hM

theorem selectionComp_small (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    ∀ x ∈ selectionCompDom a o.K ν,
    ‖fderiv ℂ (selectionCompose o.toSelectionChain x.2 ν) x.1 -
      ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ ≤ (2 : ℝ)⁻¹ ^ 11 := by
  intro x hx
  refine (selectionComp_derivative cx o ν x hx).trans ?_
  have hS := selectionComp_budget_sum_le cx ν
  have h := Real.exp_bound_div_one_sub_of_interval (x := ∑ j ∈ Finset.range ν,
    selectionMapBudget a j) ?_ (by linarith [hS, show (2 : ℝ)⁻¹ ^ 12 < 1 by norm_num])
  · have h1 : 1 / (1 - ∑ j ∈ Finset.range ν, selectionMapBudget a j) ≤ 1 + (2 : ℝ)⁻¹ ^ 11 := by
      rw [div_le_iff₀ (by linarith [show (2 : ℝ)⁻¹ ^ 12 < 1 by norm_num])]
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 11 by positivity,
        show (2 : ℝ)⁻¹ ^ 12 = (2 : ℝ)⁻¹ ^ 11 / 2 by norm_num, hS]
    linarith
  · exact Finset.sum_nonneg fun j _ => by
      have hκ0 := (wbud_stage cx.hyp j).2.2.2.1
      have := wbud_σ_pos cx.hyp j
      have := wbud_s_pos cx.hyp j
      unfold selectionMapBudget
      positivity

theorem selectionComp_angle (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    ∀ x ∈ selectionCompDom a o.K ν,
    ‖(selectionCompose o.toSelectionChain x.2 ν x.1).1 - x.1.1‖ ≤
      ∑ j ∈ Finset.range ν, selectionA a j := by
  induction ν with
  | zero =>
    intro x _
    simp [selectionCompose]
  | succ ν ih =>
    intro x hx
    have h1 := ih _ (selectionComp_map_mem cx o ν hx)
    have h2 := o.map_angle_bound ν x hx
    rw [Finset.sum_range_succ]
    simp only at h1
    calc _ ≤ ‖(selectionCompose o.toSelectionChain x.2 ν (o.X ν x.2 x.1)).1 -
          (o.X ν x.2 x.1).1‖ + ‖(o.X ν x.2 x.1).1 - x.1.1‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add h1 h2

theorem selectionComp_action (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    ∀ x ∈ selectionCompDom a o.K ν,
    ‖(selectionCompose o.toSelectionChain x.2 ν x.1).2 - x.1.2‖ ≤
      ∑ j ∈ Finset.range ν, selectionAlpha a j := by
  induction ν with
  | zero =>
    intro x _
    simp [selectionCompose]
  | succ ν ih =>
    intro x hx
    have h1 := ih _ (selectionComp_map_mem cx o ν hx)
    have h2 := o.map_action_bound ν x hx
    rw [Finset.sum_range_succ]
    simp only at h1
    calc _ ≤ ‖(selectionCompose o.toSelectionChain x.2 ν (o.X ν x.2 x.1)).2 -
          (o.X ν x.2 x.1).2‖ + ‖(o.X ν x.2 x.1).2 - x.1.2‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add h1 h2

theorem selectionComp_increment (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    ∀ x ∈ selectionCompDom a o.K (ν + 1),
    ‖selectionCompose o.toSelectionChain x.2 (ν + 1) x.1 -
      selectionCompose o.toSelectionChain x.2 ν x.1‖ ≤
      (1 + (2 : ℝ)⁻¹ ^ 11) * max (selectionA a ν) (selectionAlpha a ν) := by
  rintro ⟨z, b⟩ hx
  have hy := selectionComp_map_mem cx o ν hx
  have hx0 := selectionComp_dom_succ cx o ν hx
  simp only at hy hx0 ⊢
  set S : Set (SelectionPhaseC n) :=
    {w | w.1 ∈ complexStrip n (selectionr a ν) ∧ ‖w.2‖ < selections a ν} with hS
  have hmem : ∀ w ∈ S, (w, b) ∈ selectionCompDom a o.K ν := fun w hw =>
    ⟨hw.1, hw.2, hx0.2.2⟩
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := selectionCompose o.toSelectionChain b ν)
    (f' := fun w => fderiv ℂ (selectionCompose o.toSelectionChain b ν) w)
    (C := 1 + (2 : ℝ)⁻¹ ^ 11) (s := S)
    (fun w hw => (selectionComp_diffAt cx o ν (hmem w hw)).hasFDerivAt.hasFDerivWithinAt)
    (fun w hw => by
      have h := selectionComp_small cx o ν (w, b) (hmem w hw)
      have hid : ‖ContinuousLinearMap.id ℂ (SelectionPhaseC n)‖ ≤ 1 :=
        ContinuousLinearMap.norm_id_le
      have := norm_le_insert' (fderiv ℂ (selectionCompose o.toSelectionChain b ν) w)
        (ContinuousLinearMap.id ℂ (SelectionPhaseC n))
      simp only at h
      linarith)
    (convex_selectionFibre _ _) (x := z) (y := o.X ν b z) ⟨hx0.1, hx0.2.1⟩ ?_
  · have hd : ‖o.X ν b z - z‖ ≤ max (selectionA a ν) (selectionAlpha a ν) := by
      rw [Prod.norm_def]
      exact max_le_max (o.map_angle_bound ν (z, b) hx) (o.map_action_bound ν (z, b) hx)
    show ‖selectionCompose o.toSelectionChain b ν (o.X ν b z) -
      selectionCompose o.toSelectionChain b ν z‖ ≤ _
    exact hmv.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  · exact ⟨hy.1, hy.2.1⟩

end Bounds

end KAM.Planetary

end
