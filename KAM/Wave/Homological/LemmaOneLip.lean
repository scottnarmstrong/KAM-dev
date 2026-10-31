/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LemmaOneF
public import KAM.Wave.Homological.TaylorSub
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Lipschitz dependence of the division operators on `ξ` (`bpW:w4:lemma1`, step *Lipschitz*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`HomMultLip τ α M d w₁ W₁ w₂ W₂`: the differences of the division operators at the parameters `ξ`
and `ζ` are bounded as in the hypotheses of `bpW:w4:solve` (ii) (`homLipC`), `d = |ξ-ζ|`;
`homMultLip_of` derives it from `(H_α)` and the Lipschitz bounds (`bpW:w4:divisors`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The Lipschitz constant `2(1+|k|₁)A_k² M d/α²` of the multipliers. -/
def homLipC (τ α M d : ℝ) (k : Fin 2 → ℤ) : ℝ :=
  2 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d

theorem homLipC_nonneg {τ α M d : ℝ} (hM : 0 ≤ M) (hd : 0 ≤ d) (k : Fin 2 → ℤ) :
    0 ≤ homLipC τ α M d k := by
  unfold homLipC
  have := Fourier.modeSize_nonneg k
  positivity

/-- The conclusions of the Lipschitz bounds for the seven division operators. -/
structure HomMultLip (τ α M d : ℝ) (w₁ : Fin 2 → ℝ) (W₁ : ℕ+ → ℝ) (w₂ : Fin 2 → ℝ)
    (W₂ : ℕ+ → ℝ) : Prop where
  a0 : ∀ k, ‖homMultA0 w₁ k - homMultA0 w₂ k‖ ≤ homLipC τ α M d k
  dp : ∀ k j, ‖homMultDp w₁ W₁ k j - homMultDp w₂ W₂ k j‖ ≤ homLipC τ α M d k
  dm : ∀ k j, ‖homMultDm w₁ W₁ k j - homMultDm w₂ W₂ k j‖ ≤ homLipC τ α M d k
  P : ∀ k, HomHadamardBound (fun i j => homDP w₁ W₁ k i j - homDP w₂ W₂ k i j)
    (homLipC τ α M d k)
  P' : ∀ k, HomHadamardBound (fun i j => homDP' w₁ W₁ k i j - homDP' w₂ W₂ k i j)
    (homLipC τ α M d k)
  Q : ∀ k, HomHadamardBound (fun i j => homDQ w₁ W₁ k i j - homDQ w₂ W₂ k i j)
    (homLipC τ α M d k)
  Qt : ∀ k, HomHadamardBound (fun i j => homDQt w₁ W₁ k i j - homDQt w₂ W₂ k i j)
    (homLipC τ α M d k)

theorem homInv_eq {δ : ℝ} (hδ : δ ≠ 0) : homInv δ = -Complex.I * ((1 / δ : ℝ) : ℂ) := by
  unfold homInv
  have : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ
  push_cast
  field_simp
  simp [Complex.I_sq]

theorem norm_homInv_sub {δ δ' : ℝ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0) :
    ‖homInv δ - homInv δ'‖ = |1 / δ - 1 / δ'| := by
  rw [homInv_eq hδ, homInv_eq hδ', ← mul_sub, norm_mul, norm_neg, Complex.norm_I, one_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ τ α : ℝ}

/-- Lipschitz bound for `1/(iδ)` from a divisor bound with weight `wt`. -/
theorem norm_homInv_sub_le {k : Fin 2 → ℤ} {wt : ℝ} {δ : (Fin 2 → ℝ) → ℝ} (hα : 0 < α)
    (hw : 0 < wt) (hb : HomDivisorBound τ α Mω MΩ Par k wt δ) {ξ ζ : Fin 2 → ℝ}
    (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) :
    ‖homInv (δ ξ) - homInv (δ ζ)‖ ≤ homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k / wt := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have hn1 := ne_zero_of_divisorBound hα hw hb hξ
  have hn2 := ne_zero_of_divisorBound hα hw hb hζ
  rw [norm_homInv_sub hn1 hn2]
  refine (hb.2 ξ hξ ζ hζ).trans (le_of_eq ?_)
  unfold homLipC
  field_simp

theorem homMultLip_of (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α)
    (hH : HomMelnikov τ α Par ω Ω) {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) :
    HomMultLip τ α (Mω + MΩ) ‖ξ - ζ‖ (ω ξ) (Ω ξ) (ω ζ) (Ω ζ) := by
  have hM : 0 ≤ Mω + MΩ := by linarith [h.nonneg.2.1, h.nonneg.2.2]
  have hc := fun k => homLipC_nonneg (τ := τ) (α := α) hM (norm_nonneg (ξ - ζ)) k
  have hw1 : ∀ j : ℕ+, (1 : ℝ) ≤ j := fun j => by exact_mod_cast j.pos
  refine ⟨fun k => ?_, fun k j => ?_, fun k j => ?_, fun k => ?_, fun k => ?_, fun k => ?_,
    fun k => ?_⟩
  · by_cases hk : k = 0
    · rw [homMultA0, homMultA0, if_pos hk, if_pos hk, sub_self, norm_zero]; exact hc k
    · rw [homMultA0, homMultA0, if_neg hk, if_neg hk]
      have := norm_homInv_sub_le hα one_pos (homDelta0_bound h hα hH hk) hξ hζ
      simpa [homDelta0] using this
  · have := norm_homInv_sub_le hα (by have := hw1 j; positivity) (homDeltaPlus_bound h hα hH k j) hξ hζ
    refine this.trans ?_
    exact div_le_self (hc k) (hw1 j)
  · have := norm_homInv_sub_le hα (by have := hw1 j; positivity) (homDeltaMinus_bound h hα hH k j) hξ hζ
    refine this.trans ?_
    exact div_le_self (hc k) (hw1 j)
  · refine homHadamardBound_of_weight (hc k) (fun i j => (i : ℝ) + j) ?_ ?_ ?_
    · intro i j _
      have := hw1 i; have := hw1 j
      rw [abs_le]; constructor <;> linarith
    · intro i j; have := hw1 i; have := hw1 j; linarith
    · intro i j
      have := hw1 i; have := hw1 j
      exact norm_homInv_sub_le hα (by positivity) (homDeltaP_bound h hα hH k i j) hξ hζ
  · refine homHadamardBound_of_weight (hc k) (fun i j => (i : ℝ) + j) ?_ ?_ ?_
    · intro i j _
      have := hw1 i; have := hw1 j
      rw [abs_le]; constructor <;> linarith
    · intro i j; have := hw1 i; have := hw1 j; linarith
    · intro i j
      have := hw1 i; have := hw1 j
      exact norm_homInv_sub_le hα (by positivity) (homDeltaP'_bound h hα hH k i j) hξ hζ
  · have key : ∀ i j : ℕ+, ‖homDQ (ω ξ) (Ω ξ) k i j - homDQ (ω ζ) (Ω ζ) k i j‖ ≤
        homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k / (homWeightQ i j : ℝ) := by
      intro i j
      have hw : (0 : ℝ) < homWeightQ i j := by exact_mod_cast one_le_homWeightQ i j
      by_cases hkij : k = 0 ∧ i = j
      · rw [homDQ, homDQ, if_pos hkij, if_pos hkij, sub_self, norm_zero]
        exact div_nonneg (hc k) hw.le
      · rw [homDQ, homDQ, if_neg hkij, if_neg hkij]
        have hne : k ≠ 0 ∨ i ≠ j := by
          by_contra hcon; push Not at hcon; exact hkij hcon
        exact norm_homInv_sub_le hα hw (homDeltaQ_bound h hα hH hne) hξ hζ
    refine homHadamardBound_of_weight (hc k) (fun i j => (homWeightQ i j : ℝ))
      (fun i j hij => homWeightQ_abs i j hij) (fun i j => by exact_mod_cast one_le_homWeightQ i j) key
  · have key : ∀ i j : ℕ+, ‖homDQt (ω ξ) (Ω ξ) k i j - homDQt (ω ζ) (Ω ζ) k i j‖ ≤
        homLipC τ α (Mω + MΩ) ‖ξ - ζ‖ k / (homWeightQ j i : ℝ) := by
      intro i j
      have hw : (0 : ℝ) < homWeightQ j i := by exact_mod_cast one_le_homWeightQ j i
      by_cases hkij : k = 0 ∧ j = i
      · rw [homDQt, homDQt, homDQ, homDQ, if_pos hkij, if_pos hkij, sub_self, norm_zero]
        exact div_nonneg (hc k) hw.le
      · rw [homDQt, homDQt, homDQ, homDQ, if_neg hkij, if_neg hkij]
        have hne : k ≠ 0 ∨ j ≠ i := by
          by_contra hcon; push Not at hcon; exact hkij hcon
        exact norm_homInv_sub_le hα hw (homDeltaQ_bound h hα hH hne) hξ hζ
    refine homHadamardBound_of_weight (hc k) (fun i j => (homWeightQ j i : ℝ))
      (fun i j hij => ?_) (fun i j => by exact_mod_cast one_le_homWeightQ j i) key
    have := homWeightQ_abs j i (Ne.symm hij)
    rwa [abs_sub_comm] at this

end KAM.Wave
