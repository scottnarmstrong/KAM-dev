/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Extension
public import KAM.Planetary.WeakKAM.ExtensionNorm

/-! # P11B finite measure: coherent cutoffs for every prefix

`finite_extension` produces its cutoff sequence internally and reports properties of the full
prefix only. The finite measure lemma needs the same cutoffs at every shorter prefix
(`stepP:p11a:fm-close`: "for `j ≤ ν` the chain of length `j` is an initial segment"), so the
cutoff choice is split from its consumption: `selection_coherent_cutoffs` chooses one cutoff
sequence (the choice made in `finite_extension`), and `selection_stage_of_cutoffs` derives the
`finite_extension` conclusions for the prefix `j` from those cutoffs.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

theorem SelectionExtensionChain.mono {d : SelectionData n} {a : SelectionSchedule n}
    {c : SelectionChain n} {ν j : ℕ} (hc : SelectionExtensionChain d a c ν) (hj : j ≤ ν) :
    SelectionExtensionChain d a c j where
  initial := hc.initial
  compact i hi := hc.compact i (hi.trans hj)
  nonempty i hi := hc.nonempty i (hi.trans hj)
  nested i hi := hc.nested i (lt_of_lt_of_le hi hj)
  holomorphic i hi := hc.holomorphic i (lt_of_lt_of_le hi hj)
  real i hi := hc.real i (lt_of_lt_of_le hi hj)
  bound i hi := hc.bound i (lt_of_lt_of_le hi hj)

/-- One cutoff sequence for the whole prefix (the choice made inside `finite_extension`). -/
theorem selection_coherent_cutoffs (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) (hc : SelectionExtensionChain d a c ν)
    (ht : 0 < a.t₀) (ht1 : a.t₀ ≤ 1) (hτ : 0 ≤ a.τ) :
    ∃ χ : ℕ → SelectionR n → ℝ, ∀ j < ν, ContDiff ℝ d.μ (χ j) ∧
      (∀ y, 0 ≤ χ j y ∧ χ j y ≤ 1) ∧ (∀ y ∈ c.K j, χ j y = 1) ∧
      tsupport (χ j) ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2} ∧
      ∀ k ≤ d.μ, ∀ y, ∀ a' : Fin k → SelectionR n, (∀ i, ‖a' i‖ ≤ 1) →
        |iteratedFDeriv ℝ k (χ j) y a'| ≤ selectionCutoffC n d.μ k * (4 / selectiont a j) ^ k := by
  have hcut : ∀ j, ∃ χ : SelectionR n → ℝ, j < ν → (ContDiff ℝ d.μ χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y ∈ c.K j, χ y = 1) ∧
      tsupport χ ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2} ∧
      ∀ k ≤ d.μ, ∀ y, ∀ a' : Fin k → SelectionR n, (∀ i, ‖a' i‖ ≤ 1) →
        |iteratedFDeriv ℝ k χ y a'| ≤ selectionCutoffC n d.μ k * (4 / selectiont a j) ^ k) := by
    intro j
    by_cases hj : j < ν
    · obtain ⟨χ, h⟩ := smooth_cutoff (μ := d.μ) d.n_pos d.μ_pos (c.K j)
        (hc.compact j hj.le) (hc.nonempty j hj.le) (selectiont_pos ht j)
        (selectiont_le_one ht ht1 hτ j)
      exact ⟨χ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose χ hχ using hcut
  exact ⟨χ, hχ⟩

/-- The `finite_extension` conclusions for the prefix of length `ν`, for any fixed cutoffs. -/
theorem selection_stage_of_cutoffs (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) (hc : SelectionExtensionChain d a c ν)
    (ht : 0 < a.t₀) (ht1 : a.t₀ ≤ 1) (hτ : 0 ≤ a.τ) (χ : ℕ → SelectionR n → ℝ)
    (hχ : ∀ j < ν, ContDiff ℝ d.μ (χ j) ∧
      (∀ y, 0 ≤ χ j y ∧ χ j y ≤ 1) ∧ (∀ y ∈ c.K j, χ j y = 1) ∧
      tsupport (χ j) ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2} ∧
      ∀ k ≤ d.μ, ∀ y, ∀ a' : Fin k → SelectionR n, (∀ i, ‖a' i‖ ≤ 1) →
        |iteratedFDeriv ℝ k (χ j) y a'| ≤ selectionCutoffC n d.μ k * (4 / selectiont a j) ^ k) :
    ContDiffOn ℝ d.μ (selectionExtendedFrequency d c χ ν)
        {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} ∧
      (∀ b ∈ c.K ν, selectionExtendedFrequency d c χ ν b =
        selectionRe (selectionFrequency d c ν (selectionReal b))) ∧
      ∀ j ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
        selectionDGVector j (selectionExtendedFrequency d c χ ν - frequencyMap d.h) y ≤
          selectionExtensionC n d.μ *
            ∑ i ∈ Finset.range ν, selectionell a i / selectiont a i ^ d.μ := by
  have hφ : ∀ j < ν, ContDiff ℝ d.μ
      (fun y => χ j y • selectionIncrement (c.Δω j) y) := fun j hj =>
    selectionStage_contDiff (hc.compact j hj.le) (hc.nonempty j hj.le) (selectiont_pos ht j)
      (hc.holomorphic j hj) (hχ j hj).1 (hχ j hj).2.2.2.1
  have hsub : ∀ j < ν, c.K ν ⊆ c.K j := fun j hj => by
    have := selectionChain_antitone hc (j := j) (ν - j) (by omega)
    rwa [Nat.add_sub_cancel' hj.le] at this
  have hKd : c.K ν ⊆ d.K := by
    rcases Nat.eq_zero_or_pos ν with rfl | hν
    · exact hc.initial ▸ subset_rfl
    · exact hc.initial ▸ hsub 0 hν
  refine ⟨?_, ?_, ?_⟩
  · have h1 := selectionFrequencyMap_contDiffOn (p11_isOpen_actionNbhd d.K (2 * d.ϑ)) d.holo d.μ
    have h2 : ContDiff ℝ d.μ (fun y => ∑ j ∈ Finset.range ν,
        χ j y • selectionIncrement (c.Δω j) y) :=
      ContDiff.sum fun j hj => hφ j (Finset.mem_range.1 hj)
    exact h1.add h2.contDiffOn
  · intro b hb
    have hbA : selectionReal b ∈ actionNbhd d.K (2 * d.ϑ) :=
      ⟨b, hKd hb, by
        rw [show selectionReal b - (fun i => (b i : ℂ)) = 0 from sub_self _, norm_zero]
        linarith [d.theta_pos]⟩
    funext i
    simp only [selectionExtendedFrequency, selectionFrequency, selectionRe, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.re_sum]
    rw [selectionFrequencyMap_apply (p11_isOpen_actionNbhd d.K (2 * d.ϑ)) d.holo hbA i]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [(hχ j (Finset.mem_range.1 hj)).2.2.1 b (hsub j (Finset.mem_range.1 hj) hb), one_mul]
  · intro k hk y _
    have hkμ : (k : WithTop ℕ∞) ≤ d.μ := by exact_mod_cast hk
    have hfun : (selectionExtendedFrequency d c χ ν - frequencyMap d.h) =
        fun y => ∑ j ∈ Finset.range ν, χ j y • selectionIncrement (c.Δω j) y := by
      funext z
      simp [selectionExtendedFrequency, selectionIncrement]
    rw [hfun]
    have hterm : ∀ j ∈ Finset.range ν, Real.sqrt n *
        ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y‖ ≤
        selectionell a j / selectiont a j ^ d.μ * selectionExtensionC n d.μ := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      exact selectionStage_extension_bound (hc.compact j hj'.le) (hc.nonempty j hj'.le)
        (selectiont_pos ht j) (selectiont_le_one ht ht1 hτ j) (hc.holomorphic j hj')
        (fun b hb => hc.real j hj' b hb) (fun b hb => hc.bound j hj' b hb) (hχ j hj').1
        (hχ j hj').2.2.2.1 (hχ j hj').2.2.2.2 hk y
    have hne : {v | ∃ a' : SelectionR n, selectionLength a' = 1 ∧ v = selectionLength
        (iteratedFDeriv ℝ k (fun y => ∑ j ∈ Finset.range ν,
          χ j y • selectionIncrement (c.Δω j) y) y (fun _ => a'))}.Nonempty :=
      ⟨_, _, selectionLength_single_zero d.n_pos, rfl⟩
    unfold selectionDGVector
    refine csSup_le hne ?_
    rintro v ⟨a', ha', rfl⟩
    rw [iteratedFDeriv_fun_sum_apply fun j hj =>
      ((hφ j (Finset.mem_range.1 hj)).of_le hkμ).contDiffAt]
    simp only [sum_apply]
    have ha1 : ‖a'‖ ≤ 1 := norm_le_one_of_selectionLength_eq_one ha'
    have hv : ∀ j ∈ Finset.range ν,
        ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y
          (fun _ => a')‖ ≤
        ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y‖ := by
      intro j _
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have : ∏ _i : Fin k, ‖a'‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        fun _ _ => ha1
      exact mul_le_of_le_one_right (norm_nonneg _) this
    calc selectionLength (∑ j ∈ Finset.range ν,
          iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y (fun _ => a'))
        ≤ Real.sqrt n * ‖∑ j ∈ Finset.range ν,
          iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y (fun _ => a')‖ :=
          selectionLength_le_sqrt_mul_norm _
      _ ≤ Real.sqrt n * ∑ j ∈ Finset.range ν,
          ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y (fun _ => a')‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt n * ∑ j ∈ Finset.range ν,
          ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y‖ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hv) (Real.sqrt_nonneg _)
      _ = ∑ j ∈ Finset.range ν, Real.sqrt n *
          ‖iteratedFDeriv ℝ k (fun y => χ j y • selectionIncrement (c.Δω j) y) y‖ :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ j ∈ Finset.range ν, selectionell a j / selectiont a j ^ d.μ *
          selectionExtensionC n d.μ := Finset.sum_le_sum hterm
      _ = selectionExtensionC n d.μ * ∑ i ∈ Finset.range ν,
          selectionell a i / selectiont a i ^ d.μ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end KAM.Planetary
