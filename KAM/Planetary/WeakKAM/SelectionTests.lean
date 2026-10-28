/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.FiniteMeasure
public import KAM.Planetary.WeakKAM.FiniteMeasureExt
public import KAM.Planetary.WeakKAM.SelectionRecord

/-! # P11B selection: one cutoff family for every finite test

`finite_measure` chooses its cutoffs for one prefix length `ν`. The infinite selection needs a
single family `χ_j` serving every `ν` at once (`stepP:p11a:ps-H`). Cutoffs depend only on the
stage `j` (the set `K_j` and the scale `t_j`), so here they are chosen for all `j` from an
iteration whose every finite prefix is a retained chain, and the finite tests are then proved for
that fixed family: compactness, inclusion in the retained set, and the measure bound.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The cutoff specification of one stage, with the derivative bounds used by the estimates. -/
def SelectionCutoffSpec (d : SelectionData n) (a : SelectionSchedule n) (c : SelectionChain n)
    (χ : ℕ → SelectionR n → ℝ) : Prop :=
  ∀ j, ContDiff ℝ d.μ (χ j) ∧
    (∀ y, 0 ≤ χ j y ∧ χ j y ≤ 1) ∧ (∀ y ∈ c.K j, χ j y = 1) ∧
    tsupport (χ j) ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2} ∧
    ∀ k ≤ d.μ, ∀ y, ∀ a' : Fin k → SelectionR n, (∀ i, ‖a' i‖ ≤ 1) →
      |iteratedFDeriv ℝ k (χ j) y a'| ≤ selectionCutoffC n d.μ k * (4 / selectiont a j) ^ k

/-- Cutoffs for every stage of a chain whose prefixes are all extension chains. -/
theorem selection_all_cutoffs (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (hc : ∀ ν, SelectionExtensionChain d a c ν)
    (ht : 0 < a.t₀) (ht1 : a.t₀ ≤ 1) (hτ : 0 ≤ a.τ) :
    ∃ χ : ℕ → SelectionR n → ℝ, SelectionCutoffSpec d a c χ := by
  have hcut : ∀ j, ∃ χ : SelectionR n → ℝ, ContDiff ℝ d.μ χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y ∈ c.K j, χ y = 1) ∧
      tsupport χ ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2} ∧
      ∀ k ≤ d.μ, ∀ y, ∀ a' : Fin k → SelectionR n, (∀ i, ‖a' i‖ ≤ 1) →
        |iteratedFDeriv ℝ k χ y a'| ≤ selectionCutoffC n d.μ k * (4 / selectiont a j) ^ k :=
    fun j => smooth_cutoff (μ := d.μ) d.n_pos d.μ_pos (c.K j) ((hc j).compact j le_rfl)
      ((hc j).nonempty j le_rfl) (selectiont_pos ht j) (selectiont_le_one ht ht1 hτ j)
  choose χ hχ using hcut
  exact ⟨χ, hχ⟩

/-- The finite test set at stage `ν` for the extended family of `χ`. -/
def selectionFiniteTests (d : SelectionData n) (a : SelectionSchedule n) (c : SelectionChain n)
    (χ : ℕ → SelectionR n → ℝ) (ν : ℕ) : Set (SelectionR n) :=
  {b ∈ d.K | ∀ k : Fin n → ℤ, 0 < selectionModeLength k → selectionModeLength k ≤ selectionT a ν →
    2 * a.γ / selectionModeLength k ^ a.τ ≤
      |∑ i, (k i : ℝ) * selectionExtendedFrequency d c χ (selectionModeStage a k) b i|}

/-- Every stage of the fixed cutoff family is smooth near `K` and agrees with `Re ω_j` on `K_j`. -/
theorem selection_stage_all (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (c : SelectionChain n)
    (hc : ∀ ν, SelectionExtensionChain d (adm_params d ε) c ν) (χ : ℕ → SelectionR n → ℝ)
    (hχ : SelectionCutoffSpec d (adm_params d ε) c χ) (j : ℕ) :
    ContDiffOn ℝ d.μ (selectionExtendedFrequency d c χ j) (selectionV d) ∧
      (∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
        selectionRe (selectionFrequency d c j (selectionReal b))) ∧
      ∀ i ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
        selectionDGVector i (selectionExtendedFrequency d c χ j - frequencyMap d.h) y ≤
          selectionThetaMax d :=
  selection_stage_close d ε he hsmall c j (hc j) χ (fun i _ => hχ i) le_rfl

/-- The finite tests for the fixed cutoff family: compact, retained, and of large measure. -/
theorem selection_tests_of_cutoffs (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (c : SelectionChain n)
    (hc : ∀ ν, SelectionFiniteChain d (adm_params d ε) c ν) (χ : ℕ → SelectionR n → ℝ)
    (hχ : SelectionCutoffSpec d (adm_params d ε) c χ) (ν : ℕ) :
    IsCompact (selectionFiniteTests d (adm_params d ε) c χ ν) ∧
      selectionFiniteTests d (adm_params d ε) c χ ν ⊆ selectionRetained (adm_params d ε) d c ν ∧
      volume d.K - ENNReal.ofReal d.loss ≤
        volume (selectionFiniteTests d (adm_params d ε) c χ ν) := by
  obtain ⟨hA, ht1, hs, he0⟩ := selection_adm_facts d ε he hsmall
  set a := adm_params d ε with ha
  have hT : 1 ≤ a.T₀ := hA.cutoff_ge
  have hstage := fun j => selection_stage_all d ε he hsmall c
    (fun ν => (hc ν).toSelectionExtensionChain) χ hχ j
  have hext : ∀ j, ∀ b ∈ c.K j, selectionExtendedFrequency d c χ j b =
      selectionRe (selectionFrequency d c j (selectionReal b)) := fun j => (hstage j).2.1
  set wt : (Fin n → ℤ) → SelectionR n → SelectionR n :=
    fun k => selectionExtendedFrequency d c χ (min (selectionModeStage a k) ν) with hwt
  have hG := selection_family_measure d wt (fun k _ => (hstage _).1)
    (fun k _ j hj y hy => (hstage _).2.2 j hj y hy)
  set Hs := selectionFiniteTests d a c χ ν with hHs
  have hGH : {y ∈ d.K | ∀ k : Fin n → ℤ, k ≠ 0 →
      2 * selectionGamma d * KAM.Fourier.modeSize k ^ (-d.τ) ≤ |p11dotZ k (wt k y)|} ⊆ Hs := by
    rintro b ⟨hbK, hb⟩
    refine ⟨hbK, fun k hk hkT => ?_⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp [selectionModeLength] at hk
    have h1 := hb k hk0
    have hst : selectionModeStage a k ≤ ν := selectionModeStage_le a hT hk hkT
    simp only [wt, min_eq_left hst] at h1
    have e : 2 * selectionGamma d * KAM.Fourier.modeSize k ^ (-d.τ) =
        2 * a.γ / selectionModeLength k ^ a.τ := by
      rw [Real.rpow_neg (KAM.Fourier.modeSize_nonneg k), div_eq_mul_inv]
      rfl
    rw [← e]
    exact h1
  have hKV : d.K ⊆ selectionV d := fun x hx =>
    selectionThick_subset_V d (K_subset_selectionThick d.K d.theta_pos.le hx)
  have hHeq : Hs = {b ∈ d.K | ∀ k : Fin n → ℤ, 0 < selectionModeLength k →
      selectionModeLength k ≤ selectionT a ν → 2 * a.γ / selectionModeLength k ^ a.τ ≤
        |∑ i, (k i : ℝ) * wt k b i|} := by
    ext b
    refine and_congr_right fun _ => forall_congr' fun k => forall_congr' fun hk =>
      forall_congr' fun hkT => ?_
    simp only [wt, min_eq_left (selectionModeStage_le a hT hk hkT)]
  have hcomp : IsCompact Hs := by
    rw [hHeq]
    exact isCompact_selection_tests d.compact wt
      (fun k => (hstage _).1.continuousOn.mono hKV) _ _
  exact ⟨hcomp, fun b hb => selection_retained_of_tests d a c ν (hc ν) hT χ
    (fun j _ => hext j) hb.1 hb.2, hG.trans (measure_mono hGH)⟩

end KAM.Planetary

end
