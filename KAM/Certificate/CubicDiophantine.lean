/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Certificate.Freq
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation

/-!
# A nonresonant cubic frequency in dimension three

With `x = ∛2` the vector `(x/2, x²/2, 1/2)` is `(1/12, 2)`-Diophantine.  For an integer vector
`k ≠ 0` put `β = k₂ + k₀ x + k₁ x²`; the adjugate `Q` satisfies `β Q = N` with the integer norm
`N = a³ + 2b³ + 4c³ - 6abc ≠ 0` (infinite descent mod 2), and `|Q| < 6 |k|₁²`.
-/

@[expose] public section

noncomputable section

namespace KAM.Certificate

/-- `∛2`. -/
def cbrtTwo : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)

/-- The reference vector `(∛2/2, ∛4/2, 1/2)`: rationally independent (`x³ - 2` irreducible). -/
def cubicFreq : Fin 3 → ℝ := ![cbrtTwo / 2, cbrtTwo ^ 2 / 2, 1 / 2]

theorem cubicFreq_eq_algFreq :
    cubicFreq = algFreq 3 [[0, 1 / 2], [0, 0, 1 / 2], [1 / 2]] cbrtTwo := by
  funext i
  fin_cases i <;>
    simp [cubicFreq, algFreq, Finset.sum_range_succ, List.getD] <;> ring

private lemma cbrtTwo_cube : cbrtTwo ^ 3 = 2 := by
  unfold cbrtTwo
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

private lemma cbrtTwo_bounds : 5 / 4 < cbrtTwo ∧ cbrtTwo < 63 / 50 := by
  have h := cbrtTwo_cube
  have hpos : 0 < cbrtTwo := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · by_contra hc
    push Not at hc
    nlinarith [pow_le_pow_left₀ hpos.le hc 3]
  · by_contra hc
    push Not at hc
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 63 / 50) hc 3]

private lemma norm_form_zero : ∀ n : ℕ, ∀ a b c : ℤ, a.natAbs + b.natAbs + c.natAbs = n →
    a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hn h
    have ha : Even a := by
      have : Even (a ^ 3) := ⟨3 * a * b * c - b ^ 3 - 2 * c ^ 3, by linarith⟩
      exact (Int.even_pow.mp this).1
    obtain ⟨a', rfl⟩ := ha
    have hb : Even b := by
      have : Even (b ^ 3) := ⟨3 * a' * b * c - 2 * a' ^ 3 - c ^ 3, by linarith⟩
      exact (Int.even_pow.mp this).1
    obtain ⟨b', rfl⟩ := hb
    have hc : Even c := by
      have : Even (c ^ 3) := ⟨3 * a' * b' * c - a' ^ 3 - 2 * b' ^ 3, by linarith⟩
      exact (Int.even_pow.mp this).1
    obtain ⟨c', rfl⟩ := hc
    have h' : a' ^ 3 + 2 * b' ^ 3 + 4 * c' ^ 3 - 6 * a' * b' * c' = 0 := by nlinarith
    by_cases hz : a'.natAbs + b'.natAbs + c'.natAbs = 0
    · omega
    · have := ih (a'.natAbs + b'.natAbs + c'.natAbs) (by omega) a' b' c' rfl h'
      omega

private lemma norm_ne_zero (a b c : ℤ) (hk : (a, b, c) ≠ (0, 0, 0)) :
    a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c ≠ 0 := by
  intro h
  obtain ⟨h1, h2, h3⟩ := norm_form_zero _ a b c rfl h
  exact hk (by simp [h1, h2, h3])

/-- The norm-form lower bound `|a + b x + c x²| ≥ 1 / (6 (|a| + |b| + |c|)²)`. -/
private lemma cubic_lower (a b c : ℤ) (hk : (a, b, c) ≠ (0, 0, 0)) :
    1 / (6 * (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) ^ 2) ≤
      |(a : ℝ) + b * cbrtTwo + c * cbrtTwo ^ 2| := by
  obtain ⟨hx1, hx2⟩ := cbrtTwo_bounds
  have h3 := cbrtTwo_cube
  set x := cbrtTwo
  have hN := norm_ne_zero a b c hk
  have hN1 : (1 : ℝ) ≤ |((a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hN
  set Q : ℝ := ((a : ℝ) ^ 2 - 2 * b * c) + (2 * c ^ 2 - a * b) * x + (b ^ 2 - a * c) * x ^ 2
  have hid : ((a ^ 3 + 2 * b ^ 3 + 4 * c ^ 3 - 6 * a * b * c : ℤ) : ℝ) =
      ((a : ℝ) + b * x + c * x ^ 2) * Q := by
    push_cast
    linear_combination (-(-2 * a * b * c + b ^ 3 + 2 * c ^ 3 +
      x * (-(a : ℝ) * c ^ 2 + b ^ 2 * c))) * h3
  have hS : (1 : ℝ) ≤ |(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| := by
    have : (1 : ℤ) ≤ |a| + |b| + |c| := by
      by_contra hc
      have h1 := abs_nonneg a
      have h2 := abs_nonneg b
      have h3 := abs_nonneg c
      apply hk
      have : |a| = 0 := by omega
      have : |b| = 0 := by omega
      have : |c| = 0 := by omega
      simp_all
    exact_mod_cast this
  have hQ : |Q| ≤ 6 * (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) ^ 2 := by
    have ha := abs_nonneg (a : ℝ)
    have hb := abs_nonneg (b : ℝ)
    have hc := abs_nonneg (c : ℝ)
    have hx0 : 0 ≤ x := by linarith
    have hxx : x ^ 2 ≤ 8 / 5 := by nlinarith
    have e1 : |(a : ℝ) ^ 2 - 2 * b * c| ≤ |(a : ℝ)| ^ 2 + 2 * (|(b : ℝ)| * |(c : ℝ)|) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_pow, abs_mul, abs_mul, abs_two]; linarith
    have e2 : |2 * (c : ℝ) ^ 2 - a * b| ≤ 2 * |(c : ℝ)| ^ 2 + |(a : ℝ)| * |(b : ℝ)| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_pow, abs_mul, abs_two]
    have e3 : |(b : ℝ) ^ 2 - a * c| ≤ |(b : ℝ)| ^ 2 + |(a : ℝ)| * |(c : ℝ)| := by
      refine (abs_sub _ _).trans ?_
      rw [abs_pow, abs_mul]
    have t1 : |(2 * (c : ℝ) ^ 2 - a * b) * x| ≤
        (2 * |(c : ℝ)| ^ 2 + |(a : ℝ)| * |(b : ℝ)|) * (63 / 50) := by
      rw [abs_mul, abs_of_nonneg hx0]
      exact mul_le_mul e2 hx2.le hx0 (by positivity)
    have t2 : |((b : ℝ) ^ 2 - a * c) * x ^ 2| ≤
        (|(b : ℝ)| ^ 2 + |(a : ℝ)| * |(c : ℝ)|) * (8 / 5) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
      exact mul_le_mul e3 hxx (by positivity) (by positivity)
    have : |Q| ≤ |(a : ℝ) ^ 2 - 2 * b * c| + |(2 * (c : ℝ) ^ 2 - a * b) * x| +
        |((b : ℝ) ^ 2 - a * c) * x ^ 2| := abs_add_three _ _ _
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, sq_nonneg |(a : ℝ)|,
      sq_nonneg |(b : ℝ)|, sq_nonneg |(c : ℝ)|]
  rw [hid, abs_mul] at hN1
  have hspos : 0 < 6 * (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)|) ^ 2 := by positivity
  rw [div_le_iff₀ hspos]
  have hb0 := abs_nonneg ((a : ℝ) + b * x + c * x ^ 2)
  nlinarith [mul_le_mul_of_nonneg_left hQ hb0]

theorem cubicFreq_isDiophantine : KAM.IsDiophantine (1 / 12) 2 cubicFreq := by
  intro k hk
  have key : (k 2, k 0, k 1) ≠ (0, 0, 0) := by
    intro h
    apply hk
    simp only [Prod.mk.injEq] at h
    ext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  have := cubic_lower _ _ _ key
  simp only [Fin.sum_univ_three, cubicFreq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.rpow_two]
  have e : (k 0 : ℝ) * (cbrtTwo / 2) + k 1 * (cbrtTwo ^ 2 / 2) + k 2 * (1 / 2) =
      ((k 2 : ℝ) + k 0 * cbrtTwo + k 1 * cbrtTwo ^ 2) / 2 := by ring
  rw [e, abs_div, abs_two, le_div_iff₀ (by norm_num)]
  have hs : (|(k 2 : ℝ)| + |(k 0 : ℝ)| + |(k 1 : ℝ)|) =
      |(k 0 : ℝ)| + |(k 1 : ℝ)| + |(k 2 : ℝ)| := by ring
  rw [hs] at this
  calc 1 / 12 / (|(k 0 : ℝ)| + |(k 1 : ℝ)| + |(k 2 : ℝ)|) ^ 2 * 2
      = 1 / (6 * (|(k 0 : ℝ)| + |(k 1 : ℝ)| + |(k 2 : ℝ)|) ^ 2) := by
        have : (|(k 0 : ℝ)| + |(k 1 : ℝ)| + |(k 2 : ℝ)|) ≠ 0 := by
          intro h0
          have h1 := abs_nonneg (k 0 : ℝ)
          have h2 := abs_nonneg (k 1 : ℝ)
          have h3 := abs_nonneg (k 2 : ℝ)
          apply key
          have : (k 0 : ℝ) = 0 := abs_eq_zero.mp (by linarith)
          have : (k 1 : ℝ) = 0 := abs_eq_zero.mp (by linarith)
          have : (k 2 : ℝ) = 0 := abs_eq_zero.mp (by linarith)
          simp_all
        field_simp; ring
    _ ≤ _ := this

end KAM.Certificate

end
