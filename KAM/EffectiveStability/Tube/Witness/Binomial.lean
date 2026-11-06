/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Binomial remainders in one variable (T2-CONF, N4)

In modal polar actions the Hamiltonian has half-integer powers `(B + u)^s` of the actions, with
`B = B₀(φ) ≥ b_min > 0` and `|u| ≤ r < b_min`. The tube checker expands them in `u`:

  `(B + u)^s = Σ_{m < M} binom(s, m) B^{s-m} u^m + binomRem s M B u`.

This file proves the Lagrange-type remainder bound

  `|binomRem s M B u| ≤ |binom(s, M)| · max((B - r)^{s-M}, (B + r)^{s-M}) · |u|^M`

(`abs_binomRem_le`), and its box form with `B ∈ [b_min, b_max]` (`abs_binomRem_le_box`). The
derivatives are again remainders:

  `∂_u binomRem s (M+1) B u = s · binomRem (s-1) M B u`,
  `∂_B binomRem s M B u = s · binomRem (s-1) M B u`

(`hasDerivAt_binomRem_u`, `hasDerivAt_binomRem_B`), so their bounds are the same bound at `s - 1`.

* `gbinom s m = (s)_m / m!`, the generalized binomial coefficient (falling factorial over `m!`);
* `binomTaylor s M B u`, the Taylor polynomial with the terms `m < M`;
* `binomRem s M B u = (B + u)^s - binomTaylor s M B u`.

The proof of the bound is by induction on `M`: `binomRem s (M+1) B 0 = 0` and its `u`-derivative is
`s · binomRem (s-1) M B u`, bounded by the induction hypothesis by `c |u|^M`, so a fencing argument
(`image_norm_le_of_norm_deriv_right_le_deriv_boundary`) gives `c |u|^{M+1} / (M+1)`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset Polynomial

/-! ### Generalized binomial coefficients -/

/-- The generalized binomial coefficient `binom(s, m) = s (s-1) ⋯ (s-m+1) / m!`. -/
noncomputable def gbinom (s : ℝ) (m : ℕ) : ℝ := (descPochhammer ℝ m).eval s / m.factorial

@[simp] theorem gbinom_zero (s : ℝ) : gbinom s 0 = 1 := by simp [gbinom]

/-- `binom(s, m+1) (m+1) = s binom(s-1, m)`. -/
theorem gbinom_succ_mul (s : ℝ) (m : ℕ) : gbinom s (m + 1) * (m + 1) = s * gbinom (s - 1) m := by
  simp only [gbinom, descPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_sub, eval_one,
    Nat.factorial_succ]
  push_cast
  field_simp

/-- `binom(s, m+1) = s binom(s-1, m) / (m+1)`. -/
theorem gbinom_succ (s : ℝ) (m : ℕ) : gbinom s (m + 1) = s * gbinom (s - 1) m / (m + 1) := by
  rw [← gbinom_succ_mul, mul_div_cancel_right₀ _ (by positivity)]

/-- `binom(s, m) (s - m) = s binom(s-1, m)`. -/
theorem gbinom_mul_sub (s : ℝ) (m : ℕ) : gbinom s m * (s - m) = s * gbinom (s - 1) m := by
  rw [← gbinom_succ_mul]
  simp only [gbinom, descPochhammer_succ_eval, Nat.factorial_succ]
  push_cast
  field_simp

/-! ### Taylor polynomial and remainder -/

/-- The Taylor polynomial of `(B + u)^s` in `u` with the terms `m < M`. -/
noncomputable def binomTaylor (s : ℝ) (M : ℕ) (B u : ℝ) : ℝ :=
  ∑ m ∈ range M, gbinom s m * B ^ (s - m) * u ^ m

/-- The Taylor remainder `(B + u)^s - binomTaylor s M B u`. -/
noncomputable def binomRem (s : ℝ) (M : ℕ) (B u : ℝ) : ℝ := (B + u) ^ s - binomTaylor s M B u

@[simp] theorem binomTaylor_zero (s B u : ℝ) : binomTaylor s 0 B u = 0 := by simp [binomTaylor]

theorem binomRem_zero (s B u : ℝ) : binomRem s 0 B u = (B + u) ^ s := by simp [binomRem]

theorem binomRem_succ_at_zero (s : ℝ) (M : ℕ) (B : ℝ) : binomRem s (M + 1) B 0 = 0 := by
  simp [binomRem, binomTaylor, sum_range_succ', zero_pow]

/-- The `u`-derivative of the Taylor polynomial:
`∂_u binomTaylor s (M+1) = s binomTaylor (s-1) M`. -/
theorem hasDerivAt_binomTaylor_u (s : ℝ) (M : ℕ) (B u : ℝ) :
    HasDerivAt (fun u => binomTaylor s (M + 1) B u) (s * binomTaylor (s - 1) M B u) u := by
  simp only [binomTaylor]
  refine (HasDerivAt.fun_sum (u := range (M + 1)) (x := u)
    (A := fun m u => gbinom s m * B ^ (s - m) * u ^ m)
    (A' := fun m => gbinom s m * B ^ (s - m) * ((m : ℝ) * u ^ (m - 1)))
    fun m _ => (hasDerivAt_pow m u).const_mul _).congr_deriv ?_
  rw [sum_range_succ', mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  refine sum_congr rfl fun m _ => ?_
  have he : s - ((m + 1 : ℕ) : ℝ) = s - 1 - m := by push_cast; ring
  rw [he]
  have := gbinom_succ_mul s m
  push_cast
  linear_combination (u ^ m * B ^ (s - 1 - m)) * this

/-- The `u`-derivative of the remainder: `∂_u binomRem s (M+1) = s binomRem (s-1) M`. -/
theorem hasDerivAt_binomRem_u (s : ℝ) (M : ℕ) {B u : ℝ} (hBu : 0 < B + u) :
    HasDerivAt (fun u => binomRem s (M + 1) B u) (s * binomRem (s - 1) M B u) u := by
  have h1 : HasDerivAt (fun u => (B + u) ^ s) (1 * s * (B + u) ^ (s - 1)) u :=
    ((hasDerivAt_id u).const_add B).rpow_const (Or.inl hBu.ne')
  show HasDerivAt (fun u => (B + u) ^ s - binomTaylor s (M + 1) B u) _ u
  refine (h1.fun_sub (hasDerivAt_binomTaylor_u s M B u)).congr_deriv ?_
  simp only [binomRem]
  ring

/-- The `B`-derivative of the Taylor polynomial: `∂_B binomTaylor s M = s binomTaylor (s-1) M`. -/
theorem hasDerivAt_binomTaylor_B (s : ℝ) (M : ℕ) {B : ℝ} (u : ℝ) (hB : 0 < B) :
    HasDerivAt (fun B => binomTaylor s M B u) (s * binomTaylor (s - 1) M B u) B := by
  simp only [binomTaylor]
  refine (HasDerivAt.fun_sum (u := range M) (x := B)
    (A := fun m B => gbinom s m * B ^ (s - m) * u ^ m)
    (A' := fun m => gbinom s m * ((s - m) * B ^ (s - m - 1)) * u ^ m)
    fun m _ => ((Real.hasDerivAt_rpow_const (Or.inl hB.ne')).const_mul _).mul_const _).congr_deriv
      ?_
  rw [mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have he : s - (m : ℝ) - 1 = s - 1 - m := by ring
  rw [he, ← mul_assoc (gbinom s m), gbinom_mul_sub]
  ring

/-- The `B`-derivative of the remainder: `∂_B binomRem s M = s binomRem (s-1) M`. -/
theorem hasDerivAt_binomRem_B (s : ℝ) (M : ℕ) {B u : ℝ} (hB : 0 < B) (hBu : 0 < B + u) :
    HasDerivAt (fun B => binomRem s M B u) (s * binomRem (s - 1) M B u) B := by
  have h1 : HasDerivAt (fun B => (B + u) ^ s) (1 * s * (B + u) ^ (s - 1)) B :=
    ((hasDerivAt_id B).add_const u).rpow_const (Or.inl hBu.ne')
  show HasDerivAt (fun B => (B + u) ^ s - binomTaylor s M B u) _ B
  refine (h1.fun_sub (hasDerivAt_binomTaylor_B s M u hB)).congr_deriv ?_
  simp only [binomRem]
  ring

/-! ### A fencing lemma -/

/-- If `g 0 = 0` and `|g'| ≤ c τ^M` on `[0, t]`, then `|g t| ≤ c t^{M+1} / (M+1)`. -/
theorem abs_le_of_hasDerivAt_pow_nonneg {g g' : ℝ → ℝ} {c t : ℝ} {M : ℕ} (ht : 0 ≤ t)
    (hg0 : g 0 = 0) (hd : ∀ τ ∈ Set.Icc 0 t, HasDerivAt g (g' τ) τ)
    (hb : ∀ τ ∈ Set.Icc 0 t, |g' τ| ≤ c * τ ^ M) : |g t| ≤ c * t ^ (M + 1) / (M + 1) := by
  have hB : ∀ x, HasDerivAt (fun τ : ℝ => c * τ ^ (M + 1) / (M + 1)) (c * x ^ M) x := by
    intro x
    convert ((hasDerivAt_pow (M + 1) x).const_mul c).div_const ((M : ℝ) + 1) using 1
    push_cast
    field_simp
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t) (f := g) (f' := g')
    (fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hd τ (Set.Ico_subset_Icc_self hτ)).hasDerivWithinAt)
    (B := fun τ : ℝ => c * τ ^ (M + 1) / (M + 1)) (by simp [hg0]) hB
    (fun τ hτ => by
      rw [Real.norm_eq_abs]
      exact hb τ (Set.Ico_subset_Icc_self hτ))
    (x := t) ⟨ht, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

/-- If `g 0 = 0` and `|g' τ| ≤ c |τ|^M` for `|τ| ≤ r`, then `|g t| ≤ c |t|^{M+1} / (M+1)` for
`|t| ≤ r`. -/
theorem abs_le_of_hasDerivAt_pow {g g' : ℝ → ℝ} {c r : ℝ} {M : ℕ} (hg0 : g 0 = 0)
    (hd : ∀ τ, |τ| ≤ r → HasDerivAt g (g' τ) τ) (hb : ∀ τ, |τ| ≤ r → |g' τ| ≤ c * |τ| ^ M)
    {t : ℝ} (ht : |t| ≤ r) : |g t| ≤ c * |t| ^ (M + 1) / (M + 1) := by
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0]
    have hIcc : ∀ τ ∈ Set.Icc 0 t, |τ| ≤ r := fun τ hτ => by
      rw [abs_of_nonneg hτ.1]; exact hτ.2.trans ((le_abs_self t).trans ht)
    exact abs_le_of_hasDerivAt_pow_nonneg h0 hg0 (fun τ hτ => hd τ (hIcc τ hτ))
      (fun τ hτ => by simpa [abs_of_nonneg hτ.1] using hb τ (hIcc τ hτ))
  · rw [abs_of_nonpos h0]
    have hIcc : ∀ τ ∈ Set.Icc 0 (-t), |-τ| ≤ r := fun τ hτ => by
      rw [abs_neg, abs_of_nonneg hτ.1]; exact hτ.2.trans ((neg_le_abs t).trans ht)
    have := abs_le_of_hasDerivAt_pow_nonneg (g := fun τ => g (-τ)) (g' := fun τ => -g' (-τ))
      (c := c) (M := M) (neg_nonneg.2 h0) (by simpa using hg0)
      (fun τ hτ => by
        convert (hd (-τ) (hIcc τ hτ)).comp τ (hasDerivAt_neg τ) using 1
        · rfl
        · ring)
      (fun τ hτ => by
        have := hb (-τ) (hIcc τ hτ)
        rw [abs_neg, abs_of_nonneg hτ.1] at this
        simpa using this)
    simpa using this

/-! ### The remainder bound -/

/-- On a positive interval, `x^e` is at most its value at one of the endpoints. -/
theorem rpow_le_max_endpoints {lo x hi : ℝ} (e : ℝ) (hlo : 0 < lo) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    x ^ e ≤ max (lo ^ e) (hi ^ e) := by
  rcases le_total 0 e with he | he
  · exact (Real.rpow_le_rpow (hlo.le.trans h1) h2 he).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hlo h1 he).trans (le_max_left _ _)

/-- **One-variable binomial remainder (Lagrange form).** For `0 ≤ r < B` and `|u| ≤ r`:
`|binomRem s M B u| ≤ |binom(s, M)| · max((B - r)^{s-M}, (B + r)^{s-M}) · |u|^M`. -/
theorem abs_binomRem_le (M : ℕ) (s : ℝ) {B r u : ℝ} (hBr : r < B) (hu : |u| ≤ r) :
    |binomRem s M B u| ≤ |gbinom s M| * max ((B - r) ^ (s - M)) ((B + r) ^ (s - M)) * |u| ^ M := by
  induction M generalizing s u with
  | zero =>
    have hBu : 0 < B + u := by linarith [neg_abs_le u]
    rw [binomRem_zero, abs_of_nonneg (Real.rpow_nonneg hBu.le _)]
    simp only [gbinom_zero, abs_one, one_mul, Nat.cast_zero, sub_zero, pow_zero, mul_one]
    exact rpow_le_max_endpoints s (by linarith) (by linarith [neg_abs_le u])
      (by linarith [le_abs_self u])
  | succ M ih =>
    obtain ⟨c, hc⟩ : ∃ c, c =
        |s| * (|gbinom (s - 1) M| * max ((B - r) ^ (s - 1 - M)) ((B + r) ^ (s - 1 - M))) :=
      ⟨_, rfl⟩
    have hd : ∀ τ, |τ| ≤ r → HasDerivAt (fun u => binomRem s (M + 1) B u)
        (s * binomRem (s - 1) M B τ) τ := fun τ hτ =>
      hasDerivAt_binomRem_u s M (by linarith [neg_abs_le τ])
    have hb : ∀ τ, |τ| ≤ r → |s * binomRem (s - 1) M B τ| ≤ c * |τ| ^ M := fun τ hτ => by
      rw [abs_mul, hc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih (s - 1) hτ) (abs_nonneg s)
    have key := abs_le_of_hasDerivAt_pow (binomRem_succ_at_zero s M B) hd hb hu
    refine key.trans (le_of_eq ?_)
    have he : s - 1 - (M : ℝ) = s - ((M + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hc, he, gbinom_succ, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < M + 1)]
    ring

/-- **Box form.** For `b_min ≤ B ≤ b_max`, `0 ≤ r < b_min` and `|u| ≤ r`:
`|binomRem s M B u| ≤ |binom(s, M)| · max((b_min - r)^{s-M}, (b_max + r)^{s-M}) · r^M`. -/
theorem abs_binomRem_le_box (M : ℕ) (s : ℝ) {bmin bmax B r u : ℝ} (h1 : bmin ≤ B) (h2 : B ≤ bmax)
    (hr : r < bmin) (hu : |u| ≤ r) :
    |binomRem s M B u| ≤
      |gbinom s M| * max ((bmin - r) ^ (s - M)) ((bmax + r) ^ (s - M)) * r ^ M := by
  have hr0 : 0 ≤ r := (abs_nonneg u).trans hu
  refine (abs_binomRem_le M s (hr.trans_le h1) hu).trans ?_
  refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    (pow_le_pow_left₀ (abs_nonneg u) hu M) (by positivity)
    (mul_nonneg (abs_nonneg _) ((Real.rpow_nonneg (by linarith) _).trans (le_max_left _ _)))
  exact max_le (rpow_le_max_endpoints _ (by linarith) (by linarith) (by linarith))
    (rpow_le_max_endpoints _ (by linarith) (by linarith) (by linarith))

/-- The box bound of one Taylor term:
`|binom(s, m) B^{s-m} u^m| ≤ |binom(s, m)| · max(b_min^{s-m}, b_max^{s-m}) · r^m`. -/
theorem abs_binomTerm_le_box (m : ℕ) (s : ℝ) {bmin bmax B r u : ℝ} (h0 : 0 < bmin)
    (h1 : bmin ≤ B) (h2 : B ≤ bmax) (hu : |u| ≤ r) :
    |gbinom s m * B ^ (s - m) * u ^ m| ≤
      |gbinom s m| * max (bmin ^ (s - m)) (bmax ^ (s - m)) * r ^ m := by
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (Real.rpow_nonneg (h0.le.trans h1) _)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (rpow_le_max_endpoints _ h0 h1 h2) (abs_nonneg _))
    (pow_le_pow_left₀ (abs_nonneg u) hu m) (by positivity)
    (mul_nonneg (abs_nonneg _) ((Real.rpow_nonneg h0.le _).trans (le_max_left _ _)))

end KAM.EffectiveStability.Tube

end
