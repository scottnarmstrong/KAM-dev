/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationRecord

/-! # P11B selection: the output record `SelectionOutput`

The finite all-mode tests, the limit sets and the frequency/energy limits of the parameter
selection, packaged as an output record over the iteration (signature record; never an assumption
of a source export).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The finite all-mode tests are outputs, defined using the same first j cutoff extensions. -/
structure SelectionOutput (d : SelectionData n) (f : SelectionPhaseC n → ℂ)
    (a : SelectionSchedule n) extends SelectionIteration d f a where
  cutoffs : ℕ → SelectionR n → ℝ
  cutoff_spec : ∀ j, ContDiff ℝ d.μ (cutoffs j) ∧
    (∀ y, 0 ≤ cutoffs j y ∧ cutoffs j y ≤ 1) ∧ (∀ y ∈ K j, cutoffs j y = 1) ∧
    tsupport (cutoffs j) ⊆ {y | Metric.infDist y (K j) ≤ selectiont a j / 2}
  extended : ℕ → SelectionR n → SelectionR n
  extended_formula : ∀ j, extended j = selectionExtendedFrequency d toSelectionChain cutoffs j
  extended_regular : ∀ j, ContDiffOn ℝ d.μ (extended j)
    {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)}
  extended_eq : ∀ j, ∀ b ∈ K j, extended j b =
    selectionRe (selectionFrequency d toSelectionChain j (selectionReal b))
  Kinf : Set (SelectionR n)
  Hinf : Set (SelectionR n)
  Kinf_eq : Kinf = ⋂ j, K j
  compact_K : IsCompact Kinf
  compact_H : IsCompact Hinf
  H_subset : Hinf ⊆ Kinf
  modeStage : (Fin n → ℤ) → ℕ
  modeStage_eq : modeStage = selectionModeStage a
  modeStage_spec : ∀ k ≠ 0, k ∈ selectionShell a (modeStage k)
  Hinf_eq : Hinf = {b ∈ d.K | ∀ k : Fin n → ℤ, k ≠ 0 →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * extended (modeStage k) b i|}
  finite_compact : ∀ ν, IsCompact {b ∈ d.K | ∀ k : Fin n → ℤ,
    0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * extended (modeStage k) b i|}
  finite_inclusion : ∀ ν, {b ∈ d.K | ∀ k : Fin n → ℤ,
    0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * extended (modeStage k) b i|} ⊆ K (ν + 1)
  finite_measure : ∀ ν, volume d.K - ENNReal.ofReal d.loss ≤
    volume {b ∈ d.K | ∀ k : Fin n → ℤ,
      0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
      2 * a.γ / selectionModeLength k ^ a.τ ≤
        |∑ i, (k i : ℝ) * extended (modeStage k) b i|}
  measure_H : volume d.K - ENNReal.ofReal d.loss ≤ volume Hinf
  ωstar : SelectionR n → SelectionR n
  hstar : SelectionR n → ℝ
  frequency_summable : ∀ b ∈ Kinf, Summable (fun j => selectionRe (Δω j (selectionReal b)))
  energy_summable : ∀ b ∈ Kinf, Summable (fun j => (Δh j (selectionReal b)).re)
  frequency_uniform : TendstoUniformlyOn
    (fun ν b => selectionRe (selectionFrequency d toSelectionChain ν (selectionReal b)))
    ωstar atTop Kinf
  energy_uniform : TendstoUniformlyOn
    (fun ν b => (selectionEnergy toSelectionChain ν (selectionReal b)).re) hstar atTop Kinf
  ωstar_sum : ∀ b ∈ Kinf, ωstar b = frequencyMap d.h b +
    ∑' j, selectionRe (Δω j (selectionReal b))
  hstar_sum : ∀ b ∈ Kinf, hstar b = ∑' j, (Δh j (selectionReal b)).re
  ωstar_cont : ContinuousOn ωstar Kinf
  hstar_cont : ContinuousOn hstar Kinf
  frequency_tail : ∀ m, ∀ b ∈ Kinf,
    ‖ωstar b - selectionRe (selectionFrequency d toSelectionChain m (selectionReal b))‖
      ≤ selectionTail a m
  energy_tail : ∀ m, ∀ b ∈ Kinf,
    |hstar b - (selectionEnergy toSelectionChain m (selectionReal b)).re| ≤ 4 * selectionε a m
  diophantine : ∀ b ∈ Hinf, IsDiophantine a.γ a.τ (ωstar b)

end KAM.Planetary

end
