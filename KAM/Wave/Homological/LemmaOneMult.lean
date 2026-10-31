/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.DivisorsConcrete
public import KAM.Wave.Homological.NormalOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The division operators of Theorem `bpW:w4:lemma1` (step *Division operators*)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

At a fixed parameter value (frequencies `w ∈ ℝ²`, `W : ℕ+ → ℝ`) the multipliers of the seven
components are: scalar `homMultA0 w k = 1/(iδ⁰_k)` (zero for `k = 0`) for `a` and `b`; diagonal
`homMultDp`, `homMultDm` (`1/(iδ^±_{k,j})`) for `c^±`; and the Hadamard matrices `homDP`, `homDP'`,
`homDQ` (`1/(iδ^P_{k,ij})`, `1/(iδ^{P'}_{k,ij})`, `1/(iδ^Q_{k,ij})`, zero at `(k,i)=(0,j)`),
`homDQt k i j = homDQ k j i`. Under `(H_α)` they satisfy the hypotheses of `bpW:w4:solve` and
`bpW:w4:schur`: `homDP_bound` etc.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- `1/(iδ)`. -/
def homInv (δ : ℝ) : ℂ := (Complex.I * (δ : ℂ))⁻¹

theorem norm_homInv_le {δ L : ℝ} (hL : 0 < L) (h : L ≤ |δ|) : ‖homInv δ‖ ≤ 1 / L := by
  unfold homInv
  rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [one_div]
  exact inv_anti₀ hL h

/-- `1/(i δ⁰_k)`, zero for `k = 0`. -/
def homMultA0 (w : Fin 2 → ℝ) (k : Fin 2 → ℤ) : ℂ :=
  if k = 0 then 0 else homInv (homDelta0 w k)

/-- `1/(i δ^+_{k,j})`. -/
def homMultDp (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (j : ℕ+) : ℂ :=
  homInv (homDeltaPlus w W k j)

/-- `1/(i δ^-_{k,j})`. -/
def homMultDm (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (j : ℕ+) : ℂ :=
  homInv (homDeltaMinus w W k j)

/-- `1/(i δ^P_{k,ij})`. -/
def homDP (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℂ :=
  homInv (homDeltaP w W k i j)

/-- `1/(i δ^{P'}_{k,ij})`. -/
def homDP' (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℂ :=
  homInv (homDeltaP' w W k i j)

/-- `1/(i δ^Q_{k,ij})`, zero at `(k,i) = (0,j)`. -/
def homDQ (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℂ :=
  if k = 0 ∧ i = j then 0 else homInv (homDeltaQ w W k i j)

/-- The multiplier of `Q^T`: `1/(iδ^Q_{k,ji})`. -/
def homDQt (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) : ℂ := homDQ w W k j i

theorem homDP_symm (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) :
    homDP w W k i j = homDP w W k j i := by
  have : homDeltaP w W k i j = homDeltaP w W k j i := by unfold homDeltaP; ring
  unfold homDP; rw [this]

theorem homDP'_symm (w : Fin 2 → ℝ) (W : ℕ+ → ℝ) (k : Fin 2 → ℤ) (i j : ℕ+) :
    homDP' w W k i j = homDP' w W k j i := by
  have : homDeltaP' w W k i j = homDeltaP' w W k j i := by unfold homDeltaP'; ring
  unfold homDP'; rw [this]

variable {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {M0 Mω MΩ τ α : ℝ}

theorem norm_mult_le_of_bound {k : Fin 2 → ℤ} {wt : ℝ} {δ : (Fin 2 → ℝ) → ℝ} (hα : 0 < α)
    (hw : 0 < wt) (hb : HomDivisorBound τ α Mω MΩ Par k wt δ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    ‖homInv (δ ξ)‖ ≤ waveA τ k / (α * wt) := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have h := norm_homInv_le (by positivity : 0 < α * wt / waveA τ k) (hb.1 ξ hξ)
  refine h.trans (le_of_eq ?_)
  field_simp

theorem homHadamardBound_of_weight {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (hc : 0 ≤ c) (wt : ℕ+ → ℕ+ → ℝ)
    (hwabs : ∀ i j : ℕ+, i ≠ j → |(i : ℝ) - (j : ℝ)| ≤ wt i j) (hw1 : ∀ i j, 1 ≤ wt i j)
    (hd : ∀ i j, ‖d i j‖ ≤ c / wt i j) : HomHadamardBound d c := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hpos : 0 < |(i : ℝ) - (j : ℝ)| := by
      rw [abs_pos, sub_ne_zero]; exact_mod_cast hij
    exact (hd i j).trans (div_le_div_of_nonneg_left hc hpos (hwabs i j hij))
  · refine (hd i i).trans ?_
    have := hw1 i i
    exact div_le_self hc this


theorem homWeightQ_abs (i j : ℕ+) (hij : i ≠ j) :
    |(i : ℝ) - (j : ℝ)| ≤ (homWeightQ i j : ℝ) := by
  have := homWeightQ_ge_abs i j
  have h2 : (((i : ℤ) - j).natAbs : ℝ) ≤ (homWeightQ i j : ℝ) := by exact_mod_cast this
  have h3 : |(i : ℝ) - (j : ℝ)| = (((i : ℤ) - j).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]; push_cast; rfl
  rw [h3]; exact h2

section bounds

variable (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hα : 0 < α) (hH : HomMelnikov τ α Par ω Ω)
  {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
include h hα hH hξ

theorem norm_homMultA0_le (k : Fin 2 → ℤ) :
    ‖homMultA0 (ω ξ) k‖ ≤ 1 * waveA τ k / α := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  by_cases hk : k = 0
  · rw [homMultA0, if_pos hk, norm_zero]; positivity
  · rw [homMultA0, if_neg hk]
    have := norm_mult_le_of_bound hα one_pos (homDelta0_bound h hα hH hk) hξ
    simpa using this

theorem norm_homMultDp_le (k : Fin 2 → ℤ) (j : ℕ+) :
    ‖homMultDp (ω ξ) (Ω ξ) k j‖ ≤ 1 * waveA τ k / α := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have := norm_mult_le_of_bound hα (by positivity : (0 : ℝ) < j) (homDeltaPlus_bound h hα hH k j) hξ
  refine this.trans ?_
  rw [one_mul, div_le_div_iff₀ (by positivity) hα]
  nlinarith [mul_pos hα hA]

theorem norm_homMultDm_le (k : Fin 2 → ℤ) (j : ℕ+) :
    ‖homMultDm (ω ξ) (Ω ξ) k j‖ ≤ 1 * waveA τ k / α := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have := norm_mult_le_of_bound hα (by positivity : (0 : ℝ) < j) (homDeltaMinus_bound h hα hH k j) hξ
  refine this.trans ?_
  rw [one_mul, div_le_div_iff₀ (by positivity) hα]
  nlinarith [mul_pos hα hA]

theorem homDP_bound (k : Fin 2 → ℤ) :
    HomHadamardBound (homDP (ω ξ) (Ω ξ) k) (waveA τ k / α) := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  refine homHadamardBound_of_weight (by positivity) (fun i j => (i : ℝ) + j) ?_ ?_ ?_
  · intro i j _
    have hi : (1 : ℝ) ≤ i := by exact_mod_cast i.pos
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    rw [abs_le]; constructor <;> linarith
  · intro i j
    have hi : (1 : ℝ) ≤ i := by exact_mod_cast i.pos
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    linarith
  · intro i j
    have hi : (1 : ℝ) ≤ i := by exact_mod_cast i.pos
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    have := norm_mult_le_of_bound hα (by positivity : (0 : ℝ) < (i : ℝ) + j)
      (homDeltaP_bound h hα hH k i j) hξ
    refine this.trans (le_of_eq ?_)
    field_simp

theorem homDP'_bound (k : Fin 2 → ℤ) :
    HomHadamardBound (homDP' (ω ξ) (Ω ξ) k) (waveA τ k / α) := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  refine homHadamardBound_of_weight (by positivity) (fun i j => (i : ℝ) + j) ?_ ?_ ?_
  · intro i j _
    have hi : (1 : ℝ) ≤ i := by exact_mod_cast i.pos
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    rw [abs_le]; constructor <;> linarith
  · intro i j
    have hi : (1 : ℝ) ≤ i := by exact_mod_cast i.pos
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    linarith
  · intro i j
    have hi : (1 : ℝ) ≤ i := by exact_mod_cast i.pos
    have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    have := norm_mult_le_of_bound hα (by positivity : (0 : ℝ) < (i : ℝ) + j)
      (homDeltaP'_bound h hα hH k i j) hξ
    refine this.trans (le_of_eq ?_)
    field_simp

theorem homDQ_norm_le (k : Fin 2 → ℤ) (i j : ℕ+) :
    ‖homDQ (ω ξ) (Ω ξ) k i j‖ ≤ waveA τ k / α / (homWeightQ i j : ℝ) := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  have hw : (0 : ℝ) < homWeightQ i j := by exact_mod_cast one_le_homWeightQ i j
  by_cases hkij : k = 0 ∧ i = j
  · rw [homDQ, if_pos hkij, norm_zero]; positivity
  · rw [homDQ, if_neg hkij]
    have hne : k ≠ 0 ∨ i ≠ j := by
      by_contra hc; push Not at hc; exact hkij hc
    have := norm_mult_le_of_bound hα hw (homDeltaQ_bound h hα hH hne) hξ
    refine this.trans (le_of_eq ?_)
    field_simp

theorem homDQ_bound (k : Fin 2 → ℤ) :
    HomHadamardBound (homDQ (ω ξ) (Ω ξ) k) (waveA τ k / α) := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  refine homHadamardBound_of_weight (by positivity) (fun i j => (homWeightQ i j : ℝ))
    (fun i j hij => homWeightQ_abs i j hij) (fun i j => by exact_mod_cast one_le_homWeightQ i j)
    (fun i j => homDQ_norm_le h hα hH hξ k i j)

theorem homDQt_bound (k : Fin 2 → ℤ) :
    HomHadamardBound (homDQt (ω ξ) (Ω ξ) k) (waveA τ k / α) := by
  have hA : 0 < waveA τ k := lt_of_lt_of_le one_pos (waveA_ge_one k)
  refine homHadamardBound_of_weight (by positivity) (fun i j => (homWeightQ j i : ℝ))
    (fun i j hij => ?_) (fun i j => by exact_mod_cast one_le_homWeightQ j i)
    (fun i j => homDQ_norm_le h hα hH hξ k j i)
  have := homWeightQ_abs j i (Ne.symm hij)
  rwa [abs_sub_comm] at this

end bounds

end KAM.Wave
