/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.IsDiophantine
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.Real.Sqrt

/-!
# Diophantine bounds for the lunar frequencies

With `g = (√5 - 1)/2` the frequencies `ν± = 1 ± 1/(40 + g)` satisfy
`1559 x² - 3039 x + 1481 = 0` (`ν-`) and `1559 x² - 3197 x + 1639 = 0` (`ν+`), both of
discriminant `5`. The algebraic-norm argument gives `|a ν± + b| ≥ 1 / (21 (|a| + |b|))` for all
integers `(a, b) ≠ (0, 0)`, hence `IsDiophantine (1/21) 1 ![ν±, 1]` and
`IsDiophantine (1/42) 1 ![ν± / 2, 1 / 2]`.
-/

@[expose] public section

noncomputable section

namespace KAM.Certificate

/-- The golden-ratio conjugate `g = (√5 - 1)/2`. -/
def lunarG : ℝ := (Real.sqrt 5 - 1) / 2

/-- The lunar frequency `ν₋ = 1 - 1/(40 + g)`. -/
def lunarNuMinus : ℝ := 1 - 1 / (40 + lunarG)

/-- The lunar frequency `ν₊ = 1 + 1/(40 + g)`. -/
def lunarNuPlus : ℝ := 1 + 1 / (40 + lunarG)

private lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma sqrt5_bounds : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 9 / 4 := by
  have h0 := Real.sqrt_nonneg 5
  have h := sqrt5_sq
  constructor <;> nlinarith

private lemma sqrt5_irrational : Irrational (Real.sqrt 5) := by
  have := Nat.Prime.irrational_sqrt Nat.prime_five
  simpa using this

private lemma forty_g : 40 + lunarG = (79 + Real.sqrt 5) / 2 := by
  unfold lunarG; ring

private lemma inv_forty_g : 1 / (40 + lunarG) = (79 - Real.sqrt 5) / 3118 := by
  have h := sqrt5_bounds
  rw [forty_g]
  have : 79 + Real.sqrt 5 ≠ 0 := by linarith
  field_simp
  nlinarith [sqrt5_sq]

theorem lunarNuMinus_eq : lunarNuMinus = (3039 + Real.sqrt 5) / 3118 := by
  unfold lunarNuMinus; rw [inv_forty_g]; ring

theorem lunarNuPlus_eq : lunarNuPlus = (3197 - Real.sqrt 5) / 3118 := by
  unfold lunarNuPlus; rw [inv_forty_g]; ring

theorem lunarNuMinus_quadratic : 1559 * lunarNuMinus ^ 2 - 3039 * lunarNuMinus + 1481 = 0 := by
  rw [lunarNuMinus_eq]; nlinarith [sqrt5_sq]

theorem lunarNuPlus_quadratic : 1559 * lunarNuPlus ^ 2 - 3197 * lunarNuPlus + 1639 = 0 := by
  rw [lunarNuPlus_eq]; nlinarith [sqrt5_sq]

/-- The norm argument for a quadratic irrational with leading coefficient `1559` and conjugate
`y`. -/
private lemma norm_bound (x y : ℝ) (B C : ℤ) (hsum : x + y = B / 1559)
    (hprod : x * y = C / 1559) (hxy : |x - y| ≤ 9 / (4 * 1559)) (hx : 1 / 2 ≤ x)
    (hxi : Irrational x) (hyi : Irrational y) (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    1 / (21 * (|(a : ℝ)| + |(b : ℝ)|)) ≤ |a * x + b| := by
  have hs1 : (1 : ℝ) ≤ |(a : ℝ)| + |(b : ℝ)| := by
    have : (1 : ℤ) ≤ |a| + |b| := by
      by_contra h
      have ha : |a| = 0 := by have := abs_nonneg a; have := abs_nonneg b; omega
      have hb : |b| = 0 := by have := abs_nonneg a; have := abs_nonneg b; omega
      exact hab (by simp_all)
    exact_mod_cast this
  set s : ℝ := |(a : ℝ)| + |(b : ℝ)| with hs
  have hspos : 0 < s := by linarith
  have hle : 1 / (21 * s) ≤ 1 / 21 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  by_cases hs2 : s < 2
  · by_cases ha : a = 0
    · have hb : b ≠ 0 := by rintro rfl; exact hab (by simp [ha])
      have : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
      refine hle.trans ?_
      subst ha
      simp only [Int.cast_zero, zero_mul, zero_add]
      linarith
    · have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
      have hb : b = 0 := by
        by_contra hb
        have : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
        linarith
      refine hle.trans ?_
      subst hb
      simp only [Int.cast_zero, add_zero, abs_mul]
      have : |x| = x := abs_of_pos (by linarith)
      rw [this]
      nlinarith
  · push Not at hs2
    by_contra hlt
    push Not at hlt
    set d := |a * x + b| with hd
    have hd0 : 0 ≤ d := abs_nonneg _
    have hN : (a : ℝ) ^ 2 * C + a * b * B + 1559 * b ^ 2 = 1559 * ((a * x + b) * (a * y + b)) := by
      have h1 : (a : ℝ) ^ 2 * C = 1559 * (a ^ 2 * (x * y)) := by rw [hprod]; field_simp
      have h2 : (a : ℝ) * b * B = 1559 * (a * b * (x + y)) := by rw [hsum]; field_simp
      linear_combination h1 + h2
    set N : ℤ := a ^ 2 * C + a * b * B + 1559 * b ^ 2 with hNdef
    have hNcast : (N : ℝ) = 1559 * ((a * x + b) * (a * y + b)) := by
      rw [← hN]; simp [hNdef]
    have hN0 : N ≠ 0 := by
      intro h0
      rw [h0] at hNcast
      simp only [Int.cast_zero] at hNcast
      have : (a * x + b) * (a * y + b) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · by_cases ha : a = 0
        · subst ha; simp at h; subst h; exact hab rfl
        · apply hxi
          refine ⟨(-b / a : ℚ), ?_⟩
          have : (a : ℝ) ≠ 0 := by exact_mod_cast ha
          push_cast; field_simp; linarith
      · by_cases ha : a = 0
        · subst ha; simp at h; subst h; exact hab rfl
        · apply hyi
          refine ⟨(-b / a : ℚ), ?_⟩
          have : (a : ℝ) ≠ 0 := by exact_mod_cast ha
          push_cast; field_simp; linarith
    have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN0
    have hprod' : 1 / 1559 ≤ d * |a * y + b| := by
      rw [hd, ← abs_mul]
      have : |(N : ℝ)| = 1559 * |(a * x + b) * (a * y + b)| := by
        rw [hNcast, abs_mul]; norm_num
      rw [div_le_iff₀ (by norm_num)]; linarith
    have hy : |a * y + b| ≤ d + s * (9 / (4 * 1559)) := by
      have e : a * y + b = (a * x + b) - a * (x - y) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      have : (|(a : ℝ)|) * |x - y| ≤ s * (9 / (4 * 1559)) :=
        mul_le_mul (by simp [hs]) hxy
          (abs_nonneg _) hspos.le
      linarith
    have ht : d * s * 21 < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hlt; linarith
    have hs2' : (4 : ℝ) ≤ s ^ 2 := by nlinarith
    have key : d * (d + s * (9 / (4 * 1559))) < 1 / 1559 := by
      have h1 : d * d * (s ^ 2) * 441 < 1 := by nlinarith
      have h2 : d * s * (9 / (4 * 1559)) * s * 21 < 9 / (4 * 1559) * s * 1 := by nlinarith
      nlinarith
    have := mul_le_mul_of_nonneg_left hy hd0
    linarith

private lemma irr_comb (m : ℤ) (e : ℤ) (he : e = 1 ∨ e = -1) :
    Irrational ((m + e * Real.sqrt 5) / 3118) := by
  rintro ⟨q, hq⟩
  apply sqrt5_irrational
  have he0 : (e : ℝ) ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  refine ⟨(3118 * q - m) / e, ?_⟩
  push_cast
  rw [hq]
  field_simp
  ring

/-- The lower bound `|a ν₋ + b| ≥ 1 / (21 (|a| + |b|))`. -/
theorem lunarNuMinus_lower (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    1 / (21 * (|(a : ℝ)| + |(b : ℝ)|)) ≤ |a * lunarNuMinus + b| := by
  have h := sqrt5_bounds
  have hx := irr_comb 3039 1 (Or.inl rfl)
  have hy := irr_comb 3039 (-1) (Or.inr rfl)
  push_cast at hx hy
  rw [lunarNuMinus_eq]
  refine norm_bound _ ((3039 + -1 * Real.sqrt 5) / 3118) 3039 1481 ?_ ?_ ?_ ?_ ?_ ?_ a b hab
  · push_cast; ring
  · push_cast; nlinarith [sqrt5_sq]
  · rw [show (3039 + Real.sqrt 5) / 3118 - (3039 + -1 * Real.sqrt 5) / 3118
      = Real.sqrt 5 / 1559 by ring, abs_of_pos (by linarith)]
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  · linarith
  · simpa using hx
  · simpa using hy

/-- The lower bound `|a ν₊ + b| ≥ 1 / (21 (|a| + |b|))`. -/
theorem lunarNuPlus_lower (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    1 / (21 * (|(a : ℝ)| + |(b : ℝ)|)) ≤ |a * lunarNuPlus + b| := by
  have h := sqrt5_bounds
  have hx := irr_comb 3197 (-1) (Or.inr rfl)
  have hy := irr_comb 3197 1 (Or.inl rfl)
  push_cast at hx hy
  rw [lunarNuPlus_eq]
  refine norm_bound _ ((3197 + 1 * Real.sqrt 5) / 3118) 3197 1639 ?_ ?_ ?_ ?_ ?_ ?_ a b hab
  · push_cast; ring
  · push_cast; nlinarith [sqrt5_sq]
  · rw [show (3197 - Real.sqrt 5) / 3118 - (3197 + 1 * Real.sqrt 5) / 3118
      = -(Real.sqrt 5 / 1559) by ring, abs_neg, abs_of_pos (by linarith)]
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  · linarith
  · simpa [sub_eq_add_neg] using hx
  · simpa using hy

private lemma isDiophantine_of_lower (x : ℝ)
    (h : ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      1 / (21 * (|(a : ℝ)| + |(b : ℝ)|)) ≤ |a * x + b|) :
    IsDiophantine (1 / 21) 1 ![x, 1] ∧ IsDiophantine (1 / 42) 1 ![x / 2, 1 / 2] := by
  have key : ∀ k : Fin 2 → ℤ, k ≠ 0 → (k 0, k 1) ≠ (0, 0) := by
    intro k hk hk'
    apply hk
    ext i
    fin_cases i
    · simpa using congrArg Prod.fst hk'
    · simpa using congrArg Prod.snd hk'
  constructor
  · intro k hk
    have := h _ _ (key k hk)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_one,
      mul_one]
    rwa [div_div]
  · intro k hk
    have := h _ _ (key k hk)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_one]
    have e : (k 0 : ℝ) * (x / 2) + k 1 * (1 / 2) = (k 0 * x + k 1) / 2 := by ring
    rw [e, abs_div, abs_two, le_div_iff₀ (by norm_num)]
    calc 1 / 42 / (|(k 0 : ℝ)| + |(k 1 : ℝ)|) * 2
        = 1 / (21 * (|(k 0 : ℝ)| + |(k 1 : ℝ)|)) := by
          have : (|(k 0 : ℝ)| + |(k 1 : ℝ)|) ≠ 0 := by
            intro h0
            exact key k hk (by
              have h1 := abs_nonneg (k 0 : ℝ)
              have h2 := abs_nonneg (k 1 : ℝ)
              have : (k 0 : ℝ) = 0 := abs_eq_zero.mp (by linarith)
              have : (k 1 : ℝ) = 0 := abs_eq_zero.mp (by linarith)
              simp_all)
          field_simp; ring
      _ ≤ _ := this

/-- `ν₋` is `(1/21, 1)`-Diophantine in the convention of `IsDiophantine`. -/
theorem lunarNuMinus_isDiophantine : IsDiophantine (1 / 21) 1 ![lunarNuMinus, 1] :=
  (isDiophantine_of_lower _ lunarNuMinus_lower).1

/-- `ν₊` is `(1/21, 1)`-Diophantine in the convention of `IsDiophantine`. -/
theorem lunarNuPlus_isDiophantine : IsDiophantine (1 / 21) 1 ![lunarNuPlus, 1] :=
  (isDiophantine_of_lower _ lunarNuPlus_lower).1

/-- The isoenergetic reference vector `(ν₋/2, 1/2)` is `(1/42, 1)`-Diophantine. -/
theorem lunarNuMinus_half_isDiophantine :
    IsDiophantine (1 / 42) 1 ![lunarNuMinus / 2, 1 / 2] :=
  (isDiophantine_of_lower _ lunarNuMinus_lower).2

/-- The isoenergetic reference vector `(ν₊/2, 1/2)` is `(1/42, 1)`-Diophantine. -/
theorem lunarNuPlus_half_isDiophantine :
    IsDiophantine (1 / 42) 1 ![lunarNuPlus / 2, 1 / 2] :=
  (isDiophantine_of_lower _ lunarNuPlus_lower).2

end KAM.Certificate

end
