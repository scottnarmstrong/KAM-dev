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
# Reindexing the Melnikov conditions from the P96-K index to the wave index
(blueprint-W `bpW:w4:wave` (ii), `bpW:w4:melnikov-check` (a))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`homJapW l = max(1, |∑_j (j+2) l_j|)` is the wave-index bracket. For `1 ≤ |l| ≤ 2`:
`homJap l ≤ homJapW l ≤ 3 homJap l` unless `∑ l_j = 0`, in which case they agree
(`homJapW_reindex`). Consequently `(H_α)` with `homJapW` implies `(H_α)`, and `(H_α)` implies the
conditions with `homJapW` and `α/3` (`homMelnikov_of_melnikovW`, `homMelnikovW_of_melnikov`).
-/

@[expose] public section

namespace KAM.Wave

/-- `⟨l⟩^w = max(1, |∑_j (j+2) l_j|)`, the bracket of the wave index. -/
def homJapW (l : ℕ+ →₀ ℤ) : ℕ := max 1 (l.sum fun j n => ((j : ℤ) + 2) * n).natAbs

/-- The conditions `(H_α)` stated with the wave-index bracket. -/
def HomMelnikovW (τ α : ℝ) (Par : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) : Prop :=
  ∀ ξ ∈ Par, ∀ p ∈ homZ, α * (homJapW p.2 : ℝ) / waveA τ p.1 ≤
    |homPairZ p.1 (ω ξ) + homPairL p.2 (Ω ξ)|

theorem homSumW_eq (l : ℕ+ →₀ ℤ) :
    (l.sum fun j n => ((j : ℤ) + 2) * n) =
      (l.sum fun j n => (j : ℤ) * n) + 2 * l.sum fun _ n => n := by
  unfold Finsupp.sum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- For a nonnegative `l` with `∑ l_j ≥ 1`: `⟨l⟩ ≤ ⟨l⟩^w ≤ 3 ⟨l⟩`. -/
theorem homJapW_reindex_nonneg (l : ℕ+ →₀ ℤ) (h0 : ∀ j, 0 ≤ l j)
    (hc : 1 ≤ l.sum fun _ n => n) :
    homJap l ≤ homJapW l ∧ homJapW l ≤ 3 * homJap l := by
  set S : ℤ := l.sum fun j n => (j : ℤ) * n with hS
  set c : ℤ := l.sum fun _ n => n with hc'
  have hSc : c ≤ S := by
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : (1 : ℤ) ≤ j := by exact_mod_cast j.pos
    nlinarith [h0 j]
  have hS1 : 1 ≤ S := hc.trans hSc
  have hW : (l.sum fun j n => ((j : ℤ) + 2) * n) = S + 2 * c := homSumW_eq l
  have e1 : homJap l = S.toNat := by
    unfold homJap
    rw [← hS]
    omega
  have e2 : homJapW l = (S + 2 * c).toNat := by
    unfold homJapW
    rw [hW]
    omega
  rw [e1, e2]
  omega

theorem homSum_neg (l : ℕ+ →₀ ℤ) (f : ℕ+ → ℤ) :
    ((-l).sum fun j n => f j * n) = -(l.sum fun j n => f j * n) := by
  unfold Finsupp.sum
  rw [Finsupp.support_neg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by simp

theorem homJap_neg (l : ℕ+ →₀ ℤ) : homJap (-l) = homJap l := by
  unfold homJap
  rw [homSum_neg l (fun j => (j : ℤ)), Int.natAbs_neg]

theorem homJapW_neg (l : ℕ+ →₀ ℤ) : homJapW (-l) = homJapW l := by
  unfold homJapW
  rw [homSum_neg l (fun j => (j : ℤ) + 2), Int.natAbs_neg]

/-- **Reindexing** (blueprint `bpW:w4:wave` (ii)). For `1 ≤ |l| ≤ 2`: if `∑ l_j = 0` the two
brackets agree; otherwise `⟨l⟩ ≤ ⟨l⟩^w ≤ 3⟨l⟩`. -/
theorem homJapW_reindex (l : ℕ+ →₀ ℤ) (h1 : 1 ≤ homL1 l) (h2 : homL1 l ≤ 2) :
    ((l.sum fun _ n => n) = 0 → homJapW l = homJap l) ∧
      ((l.sum fun _ n => n) ≠ 0 → homJap l ≤ homJapW l ∧ homJapW l ≤ 3 * homJap l) := by
  have hdec : ∀ j, (l j).natAbs = (l j).toNat + (-l j).toNat := fun j => by omega
  set P : ℤ := ∑ j ∈ l.support, ((l j).toNat : ℤ) with hP
  set N : ℤ := ∑ j ∈ l.support, ((-l j).toNat : ℤ) with hN
  have hn : (homL1 l : ℤ) = P + N := by
    unfold homL1 Finsupp.sum
    rw [Nat.cast_sum, hP, hN, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      show (((l j).natAbs : ℕ) : ℤ) = ((l j).toNat : ℤ) + ((-l j).toNat : ℤ)
      omega
  have hc : (l.sum fun _ n => n) = P - N := by
    unfold Finsupp.sum
    rw [hP, hN, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by dsimp only; omega
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun _ _ => by positivity
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · have hPN : P = N := by linarith
    -- both brackets agree since `∑ l_j = 0`
    have := homSumW_eq l
    unfold homJapW homJap
    rw [this, h0, mul_zero, add_zero]
  · have h1' : (1 : ℤ) ≤ P + N := by rw [← hn]; exact_mod_cast h1
    have h2' : P + N ≤ 2 := by rw [← hn]; exact_mod_cast h2
    have hPN : P ≠ N := fun h => hne (by rw [hc, h]; ring)
    have hcase : N = 0 ∨ P = 0 := by
      by_contra hcon
      push Not at hcon
      have : 1 ≤ N := by omega
      have : 1 ≤ P := by omega
      omega
    rcases hcase with hN' | hP'
    · have hnn : ∀ j, 0 ≤ l j := by
        intro j
        by_contra hneg
        push Not at hneg
        by_cases hj : j ∈ l.support
        · have hpos : (0 : ℤ) < ((-l j).toNat : ℤ) := by omega
          have : ((-l j).toNat : ℤ) ≤ N :=
            Finset.single_le_sum (f := fun j => ((-l j).toNat : ℤ))
              (fun _ _ => by positivity) hj
          omega
        · exact absurd (by simpa using hj) (by omega)
      refine homJapW_reindex_nonneg l hnn ?_
      rw [hc]; omega
    · have hnn : ∀ j, 0 ≤ (-l) j := by
        intro j
        by_contra hneg
        push Not at hneg
        have hneg' : 0 < l j := by simpa using hneg
        by_cases hj : j ∈ l.support
        · have hpos : (0 : ℤ) < ((l j).toNat : ℤ) := by omega
          have : ((l j).toNat : ℤ) ≤ P :=
            Finset.single_le_sum (f := fun j => ((l j).toNat : ℤ))
              (fun _ _ => by positivity) hj
          omega
        · exact absurd (by simpa using hj) (by omega)
      have := homJapW_reindex_nonneg (-l) hnn (by
        have : ((-l).sum fun _ n => n) = -(l.sum fun _ n => n) := by
          simpa using homSum_neg l (fun _ => 1)
        rw [this]; have := hc; omega)
      rwa [homJap_neg, homJapW_neg] at this

theorem homL1_eq_zero_iff (l : ℕ+ →₀ ℤ) : homL1 l = 0 ↔ l = 0 := by
  unfold homL1 Finsupp.sum
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    ext j
    by_cases hj : j ∈ l.support
    · simpa using h j hj
    · simpa using hj
  · intro h j _
    simp [h]

/-- The two brackets compare for every `l` with `|l| ≤ 2`: `⟨l⟩ ≤ ⟨l⟩^w ≤ 3⟨l⟩`. -/
theorem homJap_le_japW_le (l : ℕ+ →₀ ℤ) (h2 : homL1 l ≤ 2) :
    homJap l ≤ homJapW l ∧ homJapW l ≤ 3 * homJap l := by
  by_cases h0 : l = 0
  · subst h0
    simp [homJap, homJapW]
  · have h1 : 1 ≤ homL1 l := Nat.one_le_iff_ne_zero.mpr fun h => h0 ((homL1_eq_zero_iff l).1 h)
    obtain ⟨ha, hb⟩ := homJapW_reindex l h1 h2
    by_cases hc : (l.sum fun _ n => n) = 0
    · have := ha hc
      omega
    · exact hb hc

/-- `(H_α)` stated with the wave bracket implies `(H_α)` (blueprint `bpW:w4:wave` (ii)). -/
theorem homMelnikov_of_melnikovW {τ α : ℝ} (hα : 0 < α) {Par : Set (Fin 2 → ℝ)}
    {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
    (hW : HomMelnikovW τ α Par ω Ω) : HomMelnikov τ α Par ω Ω := by
  intro ξ hξ p hp
  refine le_trans ?_ (hW ξ hξ p hp)
  have hle : (homJap p.2 : ℝ) ≤ homJapW p.2 := by exact_mod_cast (homJap_le_japW_le p.2 hp.2).1
  have hA : 0 < waveA τ p.1 := by linarith [waveA_ge_one (τ := τ) p.1]
  gcongr

/-- `(H_α)` implies the conditions with the wave bracket and `α/3` (blueprint `bpW:w4:wave`
(ii)). -/
theorem homMelnikovW_of_melnikov {τ α : ℝ} (hα : 0 < α) {Par : Set (Fin 2 → ℝ)}
    {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
    (h : HomMelnikov τ α Par ω Ω) : HomMelnikovW τ (α / 3) Par ω Ω := by
  intro ξ hξ p hp
  refine le_trans ?_ (h ξ hξ p hp)
  have hle : (homJapW p.2 : ℝ) ≤ 3 * homJap p.2 := by
    exact_mod_cast (homJap_le_japW_le p.2 hp.2).2
  have hA : 0 < waveA τ p.1 := by linarith [waveA_ge_one (τ := τ) p.1]
  rw [div_le_div_iff_of_pos_right hA]
  nlinarith [mul_le_mul_of_nonneg_left hle hα.le]

end KAM.Wave
