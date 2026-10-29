/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.SelectionRecord
public import KAM.Planetary.WeakKAM.Budgets

/-! # P11B composition: domains, holomorphy and the chain rule

The finite composition `X₀ ∘ ⋯ ∘ X_{ν-1}` with a shared parameter is computed on the domain
`selectionCompDom a K ν` of stage `ν`. Each stage domain is open, contained in the previous one,
and carried by the map `X_ν` into the previous domain; holomorphy of the composition and the chain
rule for its fibre derivative follow by induction (source steps `co-dom`, `co-deriv`).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The stage-`ν` domain of the composition. -/
abbrev selectionCompDom (a : SelectionSchedule n) (K : ℕ → Set (SelectionR n)) (ν : ℕ) :
    Set (SelectionPoint n) :=
  selectionDomain (selectionr a ν) (selections a ν) (actionNbhd (K ν) (selectiont a ν))

theorem isOpen_selectionDomain (r s : ℝ) {B : Set (SelectionC n)} (hB : IsOpen B) :
    IsOpen (selectionDomain r s B) := by
  have h1 : IsOpen {x : SelectionPoint n | x.1.1 ∈ complexStrip n r} :=
    (KAM.isOpen_complexStrip n r).preimage (continuous_fst.comp continuous_fst)
  have h2 : IsOpen {x : SelectionPoint n | ‖x.1.2‖ < s} :=
    isOpen_lt (continuous_snd.comp continuous_fst).norm continuous_const
  exact h1.inter (h2.inter (hB.preimage continuous_snd))

/-- The fibre of a domain over a fixed parameter is convex. -/
theorem convex_selectionFibre (r s : ℝ) :
    Convex ℝ {z : SelectionPhaseC n | z.1 ∈ complexStrip n r ∧ ‖z.2‖ < s} := by
  have : {z : SelectionPhaseC n | z.1 ∈ complexStrip n r ∧ ‖z.2‖ < s} =
      complexStrip n r ×ˢ Metric.ball (0 : SelectionC n) s := by
    ext z
    simp
  rw [this]
  exact (KAM.convex_complexStrip n r).prod (convex_ball _ _)

section Steps
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}

theorem selectionComp_r_step (cx : WeakBudgetCtx d a) (j : ℕ) :
    selectionr a (j + 1) + selectionσ a j ≤ selectionr a j := by
  have h1 := wbud_d_pos cx.hyp j
  have h2 := wbud_σ_pos cx.hyp j
  unfold selectionr
  rw [Finset.sum_range_succ]
  linarith

theorem selectionComp_s_step (cx : WeakBudgetCtx d a) (j : ℕ) :
    selections a (j + 1) ≤ selections a j := by
  obtain ⟨hq, hq1, -⟩ := wbud_ratios cx
  have hs := cx.hyp.hs
  unfold selections
  rw [pow_succ]
  have h := mul_pos hs (pow_pos hq j)
  nlinarith [mul_le_mul_of_nonneg_left (hq1.trans (by norm_num : (1 / 32 : ℝ) ≤ 1)) h.le]

theorem selectionComp_t_step (cx : WeakBudgetCtx d a) (j : ℕ) :
    selectiont a (j + 1) ≤ selectiont a j := by
  have h := cx.hyp
  unfold selectiont
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) h.ht.le
  push_cast
  nlinarith [h.hτ]

theorem selectionComp_nbhd_succ (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    actionNbhd (o.K (ν + 1)) (selectiont a (ν + 1)) ⊆ actionNbhd (o.K ν) (selectiont a ν) := by
  rintro I ⟨J, hJ, hlt⟩
  exact ⟨J, (o.chain (ν + 1)).nested ν (by omega) hJ,
    lt_of_lt_of_le hlt (selectionComp_t_step cx ν)⟩

theorem selectionComp_dom_succ (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    selectionCompDom a o.K (ν + 1) ⊆ selectionCompDom a o.K ν := by
  rintro x ⟨hθ, hη, hb⟩
  refine ⟨fun i => (hθ i).trans_le ?_, hη.trans_le (selectionComp_s_step cx ν),
    selectionComp_nbhd_succ cx o ν hb⟩
  have := selectionComp_r_step cx ν
  have := wbud_σ_pos cx.hyp ν
  linarith

/-- The map `X_ν` carries the stage-`ν+1` domain into the stage-`ν` domain. -/
theorem selectionComp_map_mem (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ)
    {x : SelectionPoint n} (hx : x ∈ selectionCompDom a o.K (ν + 1)) :
    (o.X ν x.2 x.1, x.2) ∈ selectionCompDom a o.K ν := by
  obtain ⟨hθ, hη, hb⟩ := o.map_domain ν x hx
  refine ⟨fun i => (hθ i).trans_le (selectionComp_r_step cx ν), hη,
    selectionComp_nbhd_succ cx o ν hb⟩

theorem isOpen_selectionCompDom (a : SelectionSchedule n) (K : ℕ → Set (SelectionR n)) (ν : ℕ) :
    IsOpen (selectionCompDom a K ν) :=
  isOpen_selectionDomain _ _ (KAM.Head.isOpen_actionNbhd _ _)

/-- Joint holomorphy of the finite composition (source step `co-dom`). -/
theorem selectionComp_holo (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ) :
    DifferentiableOn ℂ
      (fun x : SelectionPoint n => selectionCompose o.toSelectionChain x.2 ν x.1)
      (selectionCompDom a o.K ν) := by
  induction ν with
  | zero => exact differentiable_fst.differentiableOn
  | succ ν ih =>
    have hX : DifferentiableOn ℂ (fun x : SelectionPoint n => (o.X ν x.2 x.1, x.2))
        (selectionCompDom a o.K (ν + 1)) :=
      (o.map_holo ν).prodMk differentiable_snd.differentiableOn
    exact ih.comp hX fun x hx => selectionComp_map_mem cx o ν hx

theorem selectionComp_diffAt (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a) (ν : ℕ)
    {z : SelectionPhaseC n} {b : SelectionC n} (hx : (z, b) ∈ selectionCompDom a o.K ν) :
    DifferentiableAt ℂ (selectionCompose o.toSelectionChain b ν) z := by
  have h := (selectionComp_holo cx o ν).differentiableAt
    ((isOpen_selectionCompDom a o.K ν).mem_nhds hx)
  have hf : DifferentiableAt ℂ (fun v : SelectionPhaseC n => (v, b)) z :=
    differentiableAt_id.prodMk (differentiableAt_const b)
  have h2 := DifferentiableAt.comp z h hf
  exact h2

theorem selectionComp_X_diffAt (o : SelectionIteration d f a) (ν : ℕ)
    {z : SelectionPhaseC n} {b : SelectionC n} (hx : (z, b) ∈ selectionCompDom a o.K (ν + 1)) :
    DifferentiableAt ℂ (o.X ν b) z := by
  have h := (o.map_holo ν).differentiableAt
    ((isOpen_selectionCompDom a o.K (ν + 1)).mem_nhds hx)
  have hf : DifferentiableAt ℂ (fun v : SelectionPhaseC n => (v, b)) z :=
    differentiableAt_id.prodMk (differentiableAt_const b)
  have h2 := DifferentiableAt.comp z h hf
  exact h2

/-- Chain rule for the fibre derivative (source step `co-deriv`). -/
theorem selectionComp_fderiv_succ (cx : WeakBudgetCtx d a) (o : SelectionIteration d f a)
    (ν : ℕ) {z : SelectionPhaseC n} {b : SelectionC n}
    (hx : (z, b) ∈ selectionCompDom a o.K (ν + 1)) :
    fderiv ℂ (selectionCompose o.toSelectionChain b (ν + 1)) z =
      (fderiv ℂ (selectionCompose o.toSelectionChain b ν) (o.X ν b z)).comp
        (fderiv ℂ (o.X ν b) z) :=
  fderiv_comp z (selectionComp_diffAt cx o ν (selectionComp_map_mem cx o ν hx))
    (selectionComp_X_diffAt o ν hx)

end Steps

end KAM.Planetary

end
