/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationStage
public import KAM.Planetary.WeakKAM.IterationParam

/-! # P11B iteration: the step fields (`O2`–`O5`, the map)

Everything one inductive step contributes: the increments on the whole collar (`stage_delta`),
the scalar bridges between the schedule budgets and the canonical-step constants, and the fields
of `IterPost` for the extended chain (`iterPost_step`).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

section Bridge
variable {d : SelectionData n} {a : SelectionSchedule n} {ch : SelectionChain n} {ν : ℕ}
  (hf : StepFacts a d.C₁ ν)

theorem selectionA_eq_stage : selectionA a ν = p11StepA (stageS d a ch ν hf) := by
  unfold selectionA p11StepA
  simp only [selectionΛ_eq_p11Lambda, selectionCutoffError_eq_p11Error]
  rfl

theorem selectionKappa_eq_stage : selectionKappa a ν = p11StepKappa (stageS d a ch ν hf) := by
  unfold selectionKappa p11StepKappa
  rw [selectionA_eq_stage hf (ch := ch)]
  rfl

theorem selectionAlpha_eq_stage : selectionAlpha a ν =
    (n + 1) * (stageS d a ch ν hf).s * p11StepA (stageS d a ch ν hf) /
      (stageS d a ch ν hf).sigma := by
  unfold selectionAlpha
  rw [selectionA_eq_stage hf (ch := ch)]
  rfl

theorem selectionMapBudget_eq_stage : selectionMapBudget a ν =
    2 * p11StepKappa (stageS d a ch ν hf) + p11StepKappa (stageS d a ch ν hf) *
      (stageS d a ch ν hf).s / (stageS d a ch ν hf).sigma := by
  unfold selectionMapBudget
  rw [selectionKappa_eq_stage hf (ch := ch)]
  rfl

theorem selectionRealBudget_eq_stage : selectionRealBudget a ν =
    2 * (stageS d a ch ν hf).T * (1 + p11Error n (stageS d a ch ν hf).T (stageS d a ch ν hf).d) *
      (stageS d a ch ν hf).eps * p11Lambda n ((stageS d a ch ν hf).r - (stageS d a ch ν hf).d) /
        ((stageS d a ch ν hf).D * (stageS d a ch ν hf).s) := by
  unfold selectionRealBudget
  simp only [selectionΛ_eq_p11Lambda, selectionCutoffError_eq_p11Error]
  rfl

end Bridge

section Delta
variable {d : SelectionData n} {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n}
  (c : WeakBudgetCtx d a) {ch : SelectionChain n} {ν : ℕ}

/-- The increments of stage `ν` on the whole collar `B_ν` (`stepP:p11a:il-inc`). -/
theorem stage_delta (hpre : IterPre d f a ch ν) (hf : StepFacts a d.C₁ ν) :
    let B := actionNbhd (ch.K ν) (selectiont a ν)
    DifferentiableOn ℂ (p11DeltaH (selectionT a ν) (ch.R ν)) B ∧
    DifferentiableOn ℂ (p11DeltaW (selectionT a ν) (ch.R ν)) B ∧
    p11Bound B (p11DeltaH (selectionT a ν) (ch.R ν))
      ((1 + p11Error n (selectionT a ν) (selectiond a ν)) * selectionε a ν) ∧
    p11Bound B (p11DeltaW (selectionT a ν) (ch.R ν))
      ((1 + p11Error n (selectionT a ν) (selectiond a ν)) * selectionε a ν / selections a ν) ∧
    ∀ b : SelectionR n, selectionReal b ∈ B →
      (p11DeltaH (selectionT a ν) (ch.R ν) (selectionReal b)).im = 0 ∧
      ∀ i, (p11DeltaW (selectionT a ν) (ch.R ν) (selectionReal b) i).im = 0 := by
  intro B
  have hadm := iterPre_admissible hpre
  have hdr : selectiond a ν < selectionr a ν := by
    linarith [hf.radius, hf.σ_pos]
  have hB : IsOpen B := p11_isOpen_actionNbhd _ _
  obtain ⟨h1, h2, h3, h4⟩ := cutoff_delta hf.n_pos (iter_r_pos c ν) hf.s_pos hf.T_pos.le
    hf.d_pos hdr hf.eps_nonneg hB hadm.1 hadm.2.1
  refine ⟨h1, h2, h3, h4, fun b hb => ?_⟩
  rw [selectionReal_eq_realInclusion] at hb ⊢
  exact cutoff_delta_real hf.n_pos (iter_r_pos c ν) hf.s_pos hf.T_pos.le hf.d_pos hdr
    hf.eps_nonneg hB hadm.1 hadm.2.1 hadm.2.2 hb

end Delta

end KAM.Planetary

end
