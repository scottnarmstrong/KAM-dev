/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.DiophantineTransfer

/-!
# Diophantine bounds for the lunar frequencies at a general barrier index `N`

With `g = (√5 - 1)/2`, `m = 2N - 1` and `L = N² - N - 1` (so `D = (m² - 5)/2 = 2L`), the
frequencies `ν± = 1 ± 1/(N + g)` equal `1 ± (m - √5)/D` and satisfy
`L x² - (2N² - 4N - 1) x + (N² - 3N + 1) = 0` (`ν₋`) and
`L x² - (2N² - 3) x + (N² + N - 1) = 0` (`ν₊`). For `N ≥ 8` the algebraic-norm argument gives
`|a ν± + b| ≥ γ(N) / (|a| + |b|)` with `γ(N) = 2/(N + 2)`, hence `IsDiophantine (γ(N)) 1 ![ν±, 1]`
and, in the rotated frame, `IsDiophantine (1/(N + 2)) 1 ![ν± - 1, 1]`. At `N = 40` this recovers
the landed constant `1/21`.
-/

@[expose] public section

noncomputable section

namespace KAM.Certificate

/-- The lunar frequency `ν₋ = 1 - 1/(N + g)`. -/
def lunarNuMinusN (N : ℕ) : ℝ := 1 - 1 / (N + lunarG)

/-- The lunar frequency `ν₊ = 1 + 1/(N + g)`. -/
def lunarNuPlusN (N : ℕ) : ℝ := 1 + 1 / (N + lunarG)

/-- The Diophantine constant `γ(N) = 2/(N + 2)` of `![ν±, 1]`. -/
def lunarGammaN (N : ℕ) : ℝ := 2 / (N + 2)

private lemma sqrt5_sq' : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma sqrt5_bounds' : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 9 / 4 := by
  have h0 := Real.sqrt_nonneg 5
  have h := sqrt5_sq'
  constructor <;> nlinarith

/-- `L = N² - N - 1`, kept as an atom for `field_simp`. -/
private def lunarLR (N : ℕ) : ℝ := (N : ℝ) ^ 2 - N - 1

private lemma lunarLR_def (N : ℕ) : (N : ℝ) ^ 2 - N - 1 = lunarLR N := rfl

private lemma lunarLR_ne (N : ℕ) : lunarLR N ≠ 0 := by
  unfold lunarLR
  rcases Nat.lt_or_ge N 2 with h | h
  · interval_cases N <;> norm_num
  · have : (2 : ℝ) ≤ N := by exact_mod_cast h
    nlinarith

private lemma inv_N_g (N : ℕ) :
    1 / (N + lunarG) = (2 * N - 1 - Real.sqrt 5) / (2 * lunarLR N) := by
  have h := sqrt5_bounds'
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hL := lunarLR_ne N
  have e : (N : ℝ) + lunarG = (2 * N - 1 + Real.sqrt 5) / 2 := by unfold lunarG; ring
  have : 2 * (N : ℝ) - 1 + Real.sqrt 5 ≠ 0 := by linarith
  rw [e, div_div_eq_mul_div, div_eq_div_iff this (by simpa using hL)]
  have e2 : lunarLR N = (N : ℝ) ^ 2 - N - 1 := rfl
  linear_combination sqrt5_sq' + 4 * e2

private lemma lunarD_eq (N : ℕ) :
    ((2 * (N : ℝ) - 1) ^ 2 - 5) / 2 = 2 * lunarLR N := by unfold lunarLR; ring

/-- Closed form `ν₋ = 1 - (2N - 1 - √5)/D`, `D = ((2N - 1)² - 5)/2`. -/
theorem lunarNuMinusN_eq (N : ℕ) :
    lunarNuMinusN N = 1 - (2 * N - 1 - Real.sqrt 5) / (((2 * (N : ℝ) - 1) ^ 2 - 5) / 2) := by
  rw [lunarNuMinusN, inv_N_g, lunarD_eq]

/-- Closed form `ν₊ = 1 + (2N - 1 - √5)/D`, `D = ((2N - 1)² - 5)/2`. -/
theorem lunarNuPlusN_eq (N : ℕ) :
    lunarNuPlusN N = 1 + (2 * N - 1 - Real.sqrt 5) / (((2 * (N : ℝ) - 1) ^ 2 - 5) / 2) := by
  rw [lunarNuPlusN, inv_N_g, lunarD_eq]

private lemma nuMinus_frac (N : ℕ) : lunarNuMinusN N =
    (2 * lunarLR N - (2 * N - 1) + Real.sqrt 5) / (2 * lunarLR N) := by
  have hL := lunarLR_ne N
  rw [lunarNuMinusN, inv_N_g]; field_simp; ring

private lemma nuPlus_frac (N : ℕ) : lunarNuPlusN N =
    (2 * lunarLR N + (2 * N - 1) - Real.sqrt 5) / (2 * lunarLR N) := by
  have hL := lunarLR_ne N
  rw [lunarNuPlusN, inv_N_g]; field_simp; ring

private lemma quad_aux (N : ℕ) (x : ℝ) (P : ℝ) (r : ℝ) (hr : r ^ 2 = 5)
    (hx : 2 * lunarLR N * x = P + r) :
    4 * lunarLR N * (lunarLR N * x ^ 2 - P * x + (P ^ 2 - 5) / (4 * lunarLR N)) = 0 := by
  have hL := lunarLR_ne N
  rw [mul_add, mul_div_cancel₀ _ (by simpa using hL)]
  linear_combination (2 * lunarLR N * x + P + r - 2 * P) * hx + hr

private lemma frac_mul (N : ℕ) (u : ℝ) : 2 * lunarLR N * (u / (2 * lunarLR N)) = u := by
  have hL := lunarLR_ne N
  field_simp

theorem lunarNuMinusN_quadratic (N : ℕ) :
    ((N : ℝ) ^ 2 - N - 1) * lunarNuMinusN N ^ 2 - (2 * N ^ 2 - 4 * N - 1) * lunarNuMinusN N
      + (N ^ 2 - 3 * N + 1) = 0 := by
  have hL := lunarLR_ne N
  have h := quad_aux N (lunarNuMinusN N) (2 * lunarLR N - (2 * N - 1)) _ sqrt5_sq'
    (by rw [nuMinus_frac, frac_mul])
  have hL4 : (4 : ℝ) * lunarLR N ≠ 0 := by simpa using hL
  have e : (((2 * lunarLR N - (2 * N - 1)) ^ 2 - 5) / (4 * lunarLR N))
      = (N : ℝ) ^ 2 - 3 * N + 1 := by
    rw [div_eq_iff hL4]; unfold lunarLR; ring
  rw [e, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h hL4
  · rw [lunarLR_def]; unfold lunarLR at h ⊢; linear_combination h

theorem lunarNuPlusN_quadratic (N : ℕ) :
    ((N : ℝ) ^ 2 - N - 1) * lunarNuPlusN N ^ 2 - (2 * N ^ 2 - 3) * lunarNuPlusN N
      + (N ^ 2 + N - 1) = 0 := by
  have hL := lunarLR_ne N
  have h := quad_aux N (lunarNuPlusN N) (2 * lunarLR N + (2 * N - 1)) (-Real.sqrt 5)
    (by rw [neg_sq]; exact sqrt5_sq') (by rw [nuPlus_frac, frac_mul]; ring)
  have hL4 : (4 : ℝ) * lunarLR N ≠ 0 := by simpa using hL
  have e : (((2 * lunarLR N + (2 * N - 1)) ^ 2 - 5) / (4 * lunarLR N))
      = (N : ℝ) ^ 2 + N - 1 := by
    rw [div_eq_iff hL4]; unfold lunarLR; ring
  rw [e, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h hL4
  · rw [lunarLR_def]; unfold lunarLR at h ⊢; linear_combination h

/-- The norm argument for a quadratic irrational with leading coefficient `L`, conjugate `y`
and `|x - y| ≤ δ`, giving the constant `c` whenever `c²/4 + c δ ≤ 1/L`. -/
private lemma norm_boundN (x y δ c : ℝ) (L B C : ℤ) (hL : 0 < L) (hsum : x + y = B / L)
    (hprod : x * y = C / L) (hxy : |x - y| ≤ δ) (hc0 : 0 < c) (hc : c ≤ 1 / 2)
    (hkey : c ^ 2 / 4 + c * δ ≤ 1 / L) (hx : 1 / 2 ≤ x)
    (hxi : Irrational x) (hyi : Irrational y) (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    c / (|(a : ℝ)| + |(b : ℝ)|) ≤ |a * x + b| := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hs1 : (1 : ℝ) ≤ |(a : ℝ)| + |(b : ℝ)| := by
    have : (1 : ℤ) ≤ |a| + |b| := by
      by_contra h
      have ha : |a| = 0 := by have := abs_nonneg a; have := abs_nonneg b; omega
      have hb : |b| = 0 := by have := abs_nonneg a; have := abs_nonneg b; omega
      exact hab (by simp_all)
    exact_mod_cast this
  set s : ℝ := |(a : ℝ)| + |(b : ℝ)| with hs
  have hspos : 0 < s := by linarith
  have hle : c / s ≤ 1 / 2 := by
    rw [div_le_iff₀ hspos]; nlinarith
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
    have hN : (a : ℝ) ^ 2 * C + a * b * B + L * b ^ 2 = L * ((a * x + b) * (a * y + b)) := by
      have h1 : (a : ℝ) ^ 2 * C = L * (a ^ 2 * (x * y)) := by rw [hprod]; field_simp
      have h2 : (a : ℝ) * b * B = L * (a * b * (x + y)) := by rw [hsum]; field_simp
      linear_combination h1 + h2
    set M : ℤ := a ^ 2 * C + a * b * B + L * b ^ 2 with hMdef
    have hMcast : (M : ℝ) = L * ((a * x + b) * (a * y + b)) := by
      rw [← hN]; simp [hMdef]
    have hM0 : M ≠ 0 := by
      intro h0
      rw [h0] at hMcast
      simp only [Int.cast_zero] at hMcast
      have : (a * x + b) * (a * y + b) = 0 := by
        rcases mul_eq_zero.mp hMcast.symm with h | h
        · linarith
        · exact h
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
    have hM1 : (1 : ℝ) ≤ |(M : ℝ)| := by exact_mod_cast Int.one_le_abs hM0
    have hprod' : 1 / (L : ℝ) ≤ d * |a * y + b| := by
      rw [hd, ← abs_mul]
      have : |(M : ℝ)| = L * |(a * x + b) * (a * y + b)| := by
        rw [hMcast, abs_mul, abs_of_pos hLr]
      rw [div_le_iff₀ hLr]; linarith
    have hδ : 0 ≤ δ := (abs_nonneg _).trans hxy
    have hy : |a * y + b| ≤ d + s * δ := by
      have e : a * y + b = (a * x + b) - a * (x - y) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      have : (|(a : ℝ)|) * |x - y| ≤ s * δ :=
        mul_le_mul (by simp [hs]) hxy (abs_nonneg _) hspos.le
      linarith
    have ht : d * s < c := by
      have := (lt_div_iff₀ hspos).mp hlt; linarith
    have hd2 : d < c / 2 := by
      rw [lt_div_iff₀ (by norm_num)]; nlinarith
    have key : d * (d + s * δ) < 1 / L := by
      have h1 : d * d < c ^ 2 / 4 := by nlinarith
      have h2 : d * s * δ ≤ c * δ := mul_le_mul_of_nonneg_right ht.le hδ
      nlinarith
    have := mul_le_mul_of_nonneg_left hy hd0
    linarith

private lemma irr_combN (p q e : ℤ) (hq : q ≠ 0) (he : e = 1 ∨ e = -1) :
    Irrational ((p + e * Real.sqrt 5) / q) := by
  rintro ⟨r, hr⟩
  have hs : Irrational (Real.sqrt 5) := by
    simpa using Nat.Prime.irrational_sqrt Nat.prime_five
  apply hs
  have he0 : (e : ℝ) ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  refine ⟨(q * r - p) / e, ?_⟩
  push_cast
  rw [hr]
  field_simp
  ring

/-- The key numeric inequality `γ²/4 + γ √5/L ≤ 1/L` for `γ = 2/(N + 2)`, `N ≥ 8`. -/
private lemma gamma_key (N : ℕ) (hN : 8 ≤ N) :
    lunarGammaN N ^ 2 / 4 + lunarGammaN N * (Real.sqrt 5 / lunarLR N) ≤ 1 / lunarLR N := by
  have h := sqrt5_bounds'
  have hN' : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have e2 : lunarLR N = (N : ℝ) ^ 2 - N - 1 := rfl
  have hL : (0 : ℝ) < lunarLR N := by rw [e2]; nlinarith
  have hP : (0 : ℝ) < N + 2 := by linarith
  unfold lunarGammaN
  have hL0 := hL.ne'
  have e : (2 / ((N : ℝ) + 2)) ^ 2 / 4 + 2 / ((N : ℝ) + 2) * (Real.sqrt 5 / lunarLR N)
      = (lunarLR N + 2 * Real.sqrt 5 * (N + 2)) / ((N + 2) ^ 2 * lunarLR N) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) hL, one_mul]
  have hq : lunarLR N + 2 * Real.sqrt 5 * (N + 2) ≤ (N + 2) ^ 2 := by rw [e2]; nlinarith
  exact mul_le_mul_of_nonneg_right hq hL.le

private lemma gamma_pos (N : ℕ) : 0 < lunarGammaN N := by unfold lunarGammaN; positivity

private lemma gamma_le_half (N : ℕ) (hN : 8 ≤ N) : lunarGammaN N ≤ 1 / 2 := by
  have hN' : (8 : ℝ) ≤ N := by exact_mod_cast hN
  unfold lunarGammaN
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith

/-- The common lower bound for `x = (2L + σ m - σ √5)/(2L)`, `m = 2N - 1`, `σ = ±1`. -/
private lemma lower_aux (N : ℕ) (hN : 8 ≤ N) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (a b : ℤ)
    (hab : (a, b) ≠ (0, 0)) :
    lunarGammaN N / (|(a : ℝ)| + |(b : ℝ)|) ≤
      |a * ((2 * lunarLR N + σ * (2 * N - 1) - σ * Real.sqrt 5) / (2 * lunarLR N)) + b| := by
  have h := sqrt5_bounds'
  have hN' : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have e2 : lunarLR N = (N : ℝ) ^ 2 - N - 1 := rfl
  have hL : (0 : ℝ) < lunarLR N := by rw [e2]; nlinarith
  have hL0 := hL.ne'
  have hσ2 : (σ : ℝ) ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσa : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set Lz : ℤ := (N : ℤ) ^ 2 - N - 1 with hLz
  have hLc : (Lz : ℝ) = lunarLR N := by rw [hLz, e2]; push_cast; ring
  have hLz0 : 0 < Lz := by exact_mod_cast (hLc ▸ hL)
  set P : ℤ := 2 * Lz + σ * (2 * N - 1) with hP
  have hPc : (P : ℝ) = 2 * lunarLR N + σ * (2 * N - 1) := by rw [hP]; push_cast; rw [hLc]
  set Q : ℤ := 2 * Lz with hQ
  have hQc : (Q : ℝ) = 2 * lunarLR N := by rw [hQ]; push_cast; rw [hLc]
  have hQ0 : Q ≠ 0 := by omega
  have hσ' : -σ = 1 ∨ -σ = -1 := by omega
  have hx := irr_combN P Q (-σ) hQ0 hσ'
  have hy := irr_combN P Q σ hQ0 hσ
  rw [hPc, hQc] at hx hy
  push_cast at hx
  set C : ℤ := Lz + σ * (2 * N - 1) + 1 with hC
  have hCc : (C : ℝ) = lunarLR N + σ * (2 * N - 1) + 1 := by rw [hC]; push_cast; rw [hLc]
  refine norm_boundN _ ((2 * lunarLR N + σ * (2 * N - 1) + σ * Real.sqrt 5) / (2 * lunarLR N))
    (Real.sqrt 5 / lunarLR N) _ Lz P C hLz0 ?_ ?_ (le_of_eq ?_) (gamma_pos N)
    (gamma_le_half N hN) (by rw [hLc]; exact gamma_key N hN) ?_ ?_ hy a b hab
  · rw [hPc, hLc]; field_simp; ring
  · rw [hCc, hLc, div_mul_div_comm, div_eq_div_iff (by positivity) hL0]
    linear_combination (-lunarLR N * σ ^ 2) * sqrt5_sq' + (-4 * lunarLR N) * e2
      + (lunarLR N * (2 * N - 1) ^ 2 - 5 * lunarLR N) * hσ2
  · rw [show (2 * lunarLR N + σ * (2 * N - 1) - σ * Real.sqrt 5) / (2 * lunarLR N)
      - (2 * lunarLR N + σ * (2 * N - 1) + σ * Real.sqrt 5) / (2 * lunarLR N)
      = -σ * (Real.sqrt 5 / lunarLR N) by field_simp; ring, abs_mul, abs_neg, hσa, one_mul]
    exact abs_of_pos (by positivity)
  · rw [le_div_iff₀ (by positivity)]
    have hq : 2 * N ≤ lunarLR N := by rw [e2]; nlinarith
    rcases hσ with rfl | rfl <;> push_cast <;> nlinarith
  · simpa [sub_eq_add_neg] using hx

/-- The lower bound `|a ν₋ + b| ≥ γ(N) / (|a| + |b|)` for `N ≥ 8`. -/
theorem lunarNuMinusN_lower (N : ℕ) (hN : 8 ≤ N) (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    lunarGammaN N / (|(a : ℝ)| + |(b : ℝ)|) ≤ |a * lunarNuMinusN N + b| := by
  have := lower_aux N hN (-1) (Or.inr rfl) a b hab
  rw [nuMinus_frac]
  convert this using 5
  push_cast; ring

/-- The lower bound `|a ν₊ + b| ≥ γ(N) / (|a| + |b|)` for `N ≥ 8`. -/
theorem lunarNuPlusN_lower (N : ℕ) (hN : 8 ≤ N) (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    lunarGammaN N / (|(a : ℝ)| + |(b : ℝ)|) ≤ |a * lunarNuPlusN N + b| := by
  have := lower_aux N hN 1 (Or.inl rfl) a b hab
  rw [nuPlus_frac]
  convert this using 5
  push_cast; ring

private lemma isDiophantine_of_lowerN (x γ : ℝ)
    (h : ∀ a b : ℤ, (a, b) ≠ (0, 0) → γ / (|(a : ℝ)| + |(b : ℝ)|) ≤ |a * x + b|) :
    IsDiophantine γ 1 ![x, 1] := by
  intro k hk
  have hk' : (k 0, k 1) ≠ (0, 0) := by
    intro hk'
    apply hk
    ext i
    fin_cases i
    · simpa using congrArg Prod.fst hk'
    · simpa using congrArg Prod.snd hk'
  have := h _ _ hk'
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.rpow_one,
    mul_one] using this

/-- The index map `k ↦ (k₀, k₁ - k₀)` of the rotation `Q₁ = q - φ`, `Q₂ = φ`. -/
private def rotIdxN (k : Fin 2 → ℤ) : Fin 2 → ℤ := ![k 0, k 1 - k 0]

private lemma rot_transferN {x γ : ℝ} (hγ : 0 ≤ γ) (h : IsDiophantine γ 1 ![x, 1]) :
    IsDiophantine (γ / 2) 1 ![x - 1, 1] := by
  have := isDiophantine_of_index_map (τ := 1) (C := 2) (ω' := ![x - 1, 1]) h hγ zero_le_one two_pos
    rotIdxN
    (fun k hk => by
      intro h0
      apply hk
      have a := congrFun h0 0
      have b := congrFun h0 1
      simp only [rotIdxN, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at a b
      ext i
      fin_cases i <;> simp <;> omega)
    (fun k => by
      simp only [rotIdxN, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      ring)
    (fun k => by
      simp only [rotIdxN, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      have h1 := abs_sub (k 1 : ℝ) (k 0 : ℝ)
      have := abs_nonneg (k 0 : ℝ)
      have := abs_nonneg (k 1 : ℝ)
      linarith)
  simpa using this

/-- `ν₋` is `(2/(N + 2), 1)`-Diophantine for `N ≥ 8`. -/
theorem lunarNuMinusN_isDiophantine (N : ℕ) (hN : 8 ≤ N) :
    IsDiophantine (lunarGammaN N) 1 ![lunarNuMinusN N, 1] :=
  isDiophantine_of_lowerN _ _ (lunarNuMinusN_lower N hN)

/-- `ν₊` is `(2/(N + 2), 1)`-Diophantine for `N ≥ 8`. -/
theorem lunarNuPlusN_isDiophantine (N : ℕ) (hN : 8 ≤ N) :
    IsDiophantine (lunarGammaN N) 1 ![lunarNuPlusN N, 1] :=
  isDiophantine_of_lowerN _ _ (lunarNuPlusN_lower N hN)

private lemma gamma_half (N : ℕ) : lunarGammaN N / 2 = 1 / (N + 2) := by
  unfold lunarGammaN; ring

/-- The rotated frequency `(ν₋ - 1, 1)` is `(1/(N + 2), 1)`-Diophantine for `N ≥ 8`. -/
theorem lunarNuMinusN_rot_isDiophantine (N : ℕ) (hN : 8 ≤ N) :
    IsDiophantine (1 / (N + 2)) 1 ![lunarNuMinusN N - 1, 1] := by
  rw [← gamma_half]
  exact rot_transferN (gamma_pos N).le (lunarNuMinusN_isDiophantine N hN)

/-- The rotated frequency `(ν₊ - 1, 1)` is `(1/(N + 2), 1)`-Diophantine for `N ≥ 8`. -/
theorem lunarNuPlusN_rot_isDiophantine (N : ℕ) (hN : 8 ≤ N) :
    IsDiophantine (1 / (N + 2)) 1 ![lunarNuPlusN N - 1, 1] := by
  rw [← gamma_half]
  exact rot_transferN (gamma_pos N).le (lunarNuPlusN_isDiophantine N hN)

/-! ### Sanity check against the landed `N = 40` declarations -/

theorem lunarNuMinusN_forty : lunarNuMinusN 40 = lunarNuMinus := by
  unfold lunarNuMinusN lunarNuMinus; norm_num

theorem lunarNuPlusN_forty : lunarNuPlusN 40 = lunarNuPlus := by
  unfold lunarNuPlusN lunarNuPlus; norm_num

theorem lunarGammaN_forty : lunarGammaN 40 = 1 / 21 := by
  unfold lunarGammaN; norm_num

/-- At `N = 40` the general statement is exactly `lunarNuMinus_isDiophantine`. -/
theorem lunarNuMinusN_isDiophantine_forty : IsDiophantine (1 / 21) 1 ![lunarNuMinus, 1] := by
  simpa [lunarNuMinusN_forty, lunarGammaN_forty] using lunarNuMinusN_isDiophantine 40 (by norm_num)

/-- At `N = 40` the rotated statement is exactly `lunarNuPlus_rot_isDiophantine`. -/
theorem lunarNuPlusN_rot_isDiophantine_forty :
    IsDiophantine (1 / 42) 1 ![lunarNuPlus - 1, 1] := by
  have := lunarNuPlusN_rot_isDiophantine 40 (by norm_num)
  rw [lunarNuPlusN_forty] at this
  norm_num at this ⊢
  exact this

/-! ### The instances `N = 65, 60, 55` (D38 and its fallbacks) -/

theorem lunarNuMinusN_rot_isDiophantine_65 :
    IsDiophantine (1 / 67) 1 ![lunarNuMinusN 65 - 1, 1] := by
  have := lunarNuMinusN_rot_isDiophantine 65 (by norm_num)
  norm_num at this ⊢
  exact this

theorem lunarNuPlusN_rot_isDiophantine_65 :
    IsDiophantine (1 / 67) 1 ![lunarNuPlusN 65 - 1, 1] := by
  have := lunarNuPlusN_rot_isDiophantine 65 (by norm_num)
  norm_num at this ⊢
  exact this

theorem lunarNuMinusN_rot_isDiophantine_60 :
    IsDiophantine (1 / 62) 1 ![lunarNuMinusN 60 - 1, 1] := by
  have := lunarNuMinusN_rot_isDiophantine 60 (by norm_num)
  norm_num at this ⊢
  exact this

theorem lunarNuPlusN_rot_isDiophantine_60 :
    IsDiophantine (1 / 62) 1 ![lunarNuPlusN 60 - 1, 1] := by
  have := lunarNuPlusN_rot_isDiophantine 60 (by norm_num)
  norm_num at this ⊢
  exact this

theorem lunarNuMinusN_rot_isDiophantine_55 :
    IsDiophantine (1 / 57) 1 ![lunarNuMinusN 55 - 1, 1] := by
  have := lunarNuMinusN_rot_isDiophantine 55 (by norm_num)
  norm_num at this ⊢
  exact this

theorem lunarNuPlusN_rot_isDiophantine_55 :
    IsDiophantine (1 / 57) 1 ![lunarNuPlusN 55 - 1, 1] := by
  have := lunarNuPlusN_rot_isDiophantine 55 (by norm_num)
  norm_num at this ⊢
  exact this

end KAM.Certificate

end
