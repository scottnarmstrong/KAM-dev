/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The six divisors and their weights (blueprint-W `bpW:w4:divisors`)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`HomDivisorBound` packages the two conclusions of Lemma `bpW:w4:divisors` for a divisor `δ(ξ)` with
weight `w`: `|δ(ξ)| ≥ α w / A_k` and the Lipschitz bound for `1/δ`. It is proved for
`δ⁰_k` (`homDelta0_bound`, `k ≠ 0`, `w = 1`), `δ^±_{k,j}` (`w = j`), `δ^P_{k,ij}`, `δ^{P'}_{k,ij}`
(`w = i + j`) and `δ^Q_{k,ij}` (`w = max(1,|i-j|)`, for `k ≠ 0 ∨ i ≠ j`).
-/

@[expose] public section

namespace KAM.Wave

/-- The conclusions of blueprint Lemma `bpW:w4:divisors` for the divisor `δ` with weight `w`. -/
def HomDivisorBound (τ α Mω MΩ : ℝ) (Par : Set (Fin 2 → ℝ)) (k : Fin 2 → ℤ) (w : ℝ)
    (δ : (Fin 2 → ℝ) → ℝ) : Prop :=
  (∀ ξ ∈ Par, α * w / waveA τ k ≤ |δ ξ|) ∧
    ∀ ξ ∈ Par, ∀ ζ ∈ Par, |1 / δ ξ - 1 / δ ζ| ≤
      2 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * (Mω + MΩ) / (α ^ 2 * w) * ‖ξ - ζ‖

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ τ α : ℝ}

theorem homDivisorBound_of_gen (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikov τ α Par ω Ω) {k : Fin 2 → ℤ} {l : ℕ+ →₀ ℤ} (hz : (k, l) ∈ homZ)
    {w : ℝ} (hw : (homJap l : ℝ) = w) {δ : (Fin 2 → ℝ) → ℝ}
    (hδ : ∀ ξ, δ ξ = homPairZ k (ω ξ) + homPairL l (Ω ξ)) :
    HomDivisorBound τ α Mω MΩ Par k w δ := by
  have := homDivGen_bounds h hα hH hz
  subst hw
  unfold HomDivisorBound
  simp only [hδ]
  exact this

theorem homZ_mem {k : Fin 2 → ℤ} {l : ℕ+ →₀ ℤ} (hne : k ≠ 0 ∨ l ≠ 0) (hl : homL1 l ≤ 2) :
    (k, l) ∈ homZ := by
  refine ⟨?_, hl⟩
  intro h0
  rcases hne with hk | hl0
  · exact hk (congrArg Prod.fst h0)
  · exact hl0 (congrArg Prod.snd h0)

theorem homNe_zero_of_mom {l : ℕ+ →₀ ℤ} (h : homMom l ≠ 0) : l ≠ 0 := by
  intro h0; rw [h0, homMom_zero] at h; exact h rfl

theorem homDelta0_bound (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikov τ α Par ω Ω) {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    HomDivisorBound τ α Mω MΩ Par k 1 fun ξ => homDelta0 (ω ξ) k := by
  refine homDivisorBound_of_gen h hα hH (l := 0) (homZ_mem (Or.inl hk) (by simp [homL1_zero])) ?_ ?_
  · simp [homJap_eq, homMom_zero]
  · intro ξ; simp [homDelta0, homPairL_zero]

theorem homJap_neg_single (j : ℕ+) : homJap (-Finsupp.single j (1 : ℤ)) = j := by
  have : (j : ℕ) ≥ 1 := j.pos
  simp [homJap_eq, homMom_neg, homMom_single]
  omega

theorem homJap_single (j : ℕ+) : homJap (Finsupp.single j (1 : ℤ)) = j := by
  have : (j : ℕ) ≥ 1 := j.pos
  simp [homJap_eq, homMom_single]
  omega

theorem homJap_pair (i j : ℕ+) :
    homJap (Finsupp.single i (1 : ℤ) + Finsupp.single j 1) = (i : ℕ) + j := by
  have : (i : ℕ) ≥ 1 := i.pos
  have : (j : ℕ) ≥ 1 := j.pos
  simp [homJap_eq, homMom_add, homMom_single]
  omega

theorem homJap_neg_pair (i j : ℕ+) :
    homJap (-(Finsupp.single i (1 : ℤ) + Finsupp.single j 1)) = (i : ℕ) + j := by
  rw [homJap_eq, homMom_neg, Int.natAbs_neg, ← homJap_eq, homJap_pair]

theorem homJap_diff (i j : ℕ+) :
    homJap (Finsupp.single i (1 : ℤ) + -Finsupp.single j 1) = homWeightQ i j := by
  simp [homJap_eq, homMom_add, homMom_neg, homMom_single, homWeightQ, sub_eq_add_neg]

theorem homL1_pair_le (i j : ℕ+) :
    homL1 (Finsupp.single i (1 : ℤ) + Finsupp.single j 1) ≤ 2 := by
  refine (homL1_add_le _ _).trans ?_
  simp [homL1_single]

theorem homDeltaPlus_bound (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikov τ α Par ω Ω) (k : Fin 2 → ℤ) (j : ℕ+) :
    HomDivisorBound τ α Mω MΩ Par k (j : ℝ) fun ξ => homDeltaPlus (ω ξ) (Ω ξ) k j := by
  have hm : homMom (-Finsupp.single j (1 : ℤ)) ≠ 0 := by
    have : (j : ℤ) ≥ 1 := by exact_mod_cast j.pos
    simp [homMom_neg, homMom_single]
  refine homDivisorBound_of_gen h hα hH
    (homZ_mem (Or.inr (homNe_zero_of_mom hm)) (by simp [homL1_neg, homL1_single])) ?_ ?_
  · rw [homJap_neg_single]
  · intro ξ; simp [homDeltaPlus, homPairL_neg, homPairL_single, sub_eq_add_neg]

theorem homDeltaMinus_bound (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikov τ α Par ω Ω) (k : Fin 2 → ℤ) (j : ℕ+) :
    HomDivisorBound τ α Mω MΩ Par k (j : ℝ) fun ξ => homDeltaMinus (ω ξ) (Ω ξ) k j := by
  have hm : homMom (Finsupp.single j (1 : ℤ)) ≠ 0 := by
    have : (j : ℤ) ≥ 1 := by exact_mod_cast j.pos
    simp [homMom_single]
  refine homDivisorBound_of_gen h hα hH
    (homZ_mem (Or.inr (homNe_zero_of_mom hm)) (by simp [homL1_single])) ?_ ?_
  · rw [homJap_single]
  · intro ξ; simp [homDeltaMinus, homPairL_single]

theorem homDeltaP_bound (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikov τ α Par ω Ω) (k : Fin 2 → ℤ) (i j : ℕ+) :
    HomDivisorBound τ α Mω MΩ Par k ((i : ℝ) + j) fun ξ => homDeltaP (ω ξ) (Ω ξ) k i j := by
  have hm : homMom (-(Finsupp.single i (1 : ℤ) + Finsupp.single j 1)) ≠ 0 := by
    have : (i : ℤ) ≥ 1 := by exact_mod_cast i.pos
    have : (j : ℤ) ≥ 1 := by exact_mod_cast j.pos
    simp [homMom_neg, homMom_add, homMom_single]; omega
  refine homDivisorBound_of_gen h hα hH
    (homZ_mem (Or.inr (homNe_zero_of_mom hm)) (by rw [homL1_neg]; exact homL1_pair_le i j)) ?_ ?_
  · rw [homJap_neg_pair]; push_cast; rfl
  · intro ξ; simp [homDeltaP, homPairL_neg, homPairL_add, homPairL_single]; ring

theorem homDeltaP'_bound (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikov τ α Par ω Ω) (k : Fin 2 → ℤ) (i j : ℕ+) :
    HomDivisorBound τ α Mω MΩ Par k ((i : ℝ) + j) fun ξ => homDeltaP' (ω ξ) (Ω ξ) k i j := by
  have hm : homMom (Finsupp.single i (1 : ℤ) + Finsupp.single j 1) ≠ 0 := by
    have : (i : ℤ) ≥ 1 := by exact_mod_cast i.pos
    have : (j : ℤ) ≥ 1 := by exact_mod_cast j.pos
    simp [homMom_add, homMom_single]; omega
  refine homDivisorBound_of_gen h hα hH
    (homZ_mem (Or.inr (homNe_zero_of_mom hm)) (homL1_pair_le i j)) ?_ ?_
  · rw [homJap_pair]; push_cast; rfl
  · intro ξ; simp [homDeltaP', homPairL_add, homPairL_single]; ring

theorem homDeltaQ_bound (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikov τ α Par ω Ω) {k : Fin 2 → ℤ} {i j : ℕ+} (hkij : k ≠ 0 ∨ i ≠ j) :
    HomDivisorBound τ α Mω MΩ Par k (homWeightQ i j : ℝ)
      fun ξ => homDeltaQ (ω ξ) (Ω ξ) k i j := by
  have hne : k ≠ 0 ∨ (Finsupp.single i (1 : ℤ) + -Finsupp.single j 1) ≠ 0 := by
    rcases hkij with hk | hij
    · exact Or.inl hk
    · refine Or.inr (homNe_zero_of_mom ?_)
      have : (i : ℤ) ≠ j := by exact_mod_cast hij
      simp [homMom_add, homMom_neg, homMom_single]; omega
  have hl : homL1 (Finsupp.single i (1 : ℤ) + -Finsupp.single j 1) ≤ 2 := by
    refine (homL1_add_le _ _).trans ?_
    simp [homL1_neg, homL1_single]
  refine homDivisorBound_of_gen h hα hH (homZ_mem hne hl) ?_ ?_
  · rw [homJap_diff]
  · intro ξ; simp [homDeltaQ, homPairL_neg, homPairL_add, homPairL_single, sub_eq_add_neg]; ring

theorem one_le_homWeightQ (i j : ℕ+) : 1 ≤ homWeightQ i j := le_max_left _ _

theorem homWeightQ_ge_abs (i j : ℕ+) : ((i : ℤ) - j).natAbs ≤ homWeightQ i j := le_max_right _ _

theorem homWeightP_ge_abs (i j : ℕ+) : ((i : ℤ) - j).natAbs ≤ (i : ℕ) + j := by
  have := i.pos; have := j.pos; omega

end KAM.Wave
