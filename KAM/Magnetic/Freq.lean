/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Freq
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Magnetic.Defs.MagAlpha
public import KAM.Magnetic.Params
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The magnetic frequency `(α, 1)` and its Diophantine constant

Unfrozen helper code.

* `magAlgFreq_eq`: `algFreq 2 magCoeffs √5 = κ (α, 1)`, `α = magAlpha = (7913 - √5)/13618`.
* `magAlpha_isDiophantine`: `(α, 1)` is `(1/10, 1)`-Diophantine.
* `magFreq_isDiophantine`: `κ (α, 1)` is `(κ/10, 1)`-Diophantine.

The proof is the algebraic-norm argument of `KAM/Certificate/QuadraticDiophantine.lean` with one
refinement. `α` is a root of `6809 x² - 7913 x + 2299` (discriminant `5`) with conjugate
`α' = α + √5/6809`. For `(a, b) ≠ 0` the integer `N = 2299 a² + 7913 a b + 6809 b²` is nonzero and
`6809 (aα + b)(aα' + b) = N`. With `x = |aα + b|`, `|aα' + b| ≤ x + |a| √5/6809`, so
`x (x + |a| √5/6809) ≥ 1/6809`, which contradicts `x < 1/(10 (|a| + |b|))` once `|a| + |b| ≥ 10`.
The pairs with `|a| + |b| ≤ 9` are checked by a kernel `decide` on integer enclosures
(`√5 ∈ [2.236, 2.237]`).
-/

@[expose] public section

noncomputable section

namespace KAM.Magnetic

open KAM KAM.Certificate

private lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma sqrt5_bounds : 2236 / 1000 < Real.sqrt 5 ∧ Real.sqrt 5 < 2237 / 1000 := by
  have h0 := Real.sqrt_nonneg 5
  have h := sqrt5_sq
  constructor <;> nlinarith

private lemma sqrt5_irrational : Irrational (Real.sqrt 5) := by
  have := Nat.Prime.irrational_sqrt Nat.prime_five
  simpa using this

/-! ### The frequency vector -/

private lemma algFreq_two (a b c : ℚ) (x : ℝ) :
    algFreq 2 [[a, b], [c]] x = ![(a : ℝ) + b * x, c] := by
  ext i
  fin_cases i <;> simp [algFreq, Finset.sum_range_succ]

theorem magAlgFreq_eq : algFreq 2 magCoeffs (Real.sqrt 5) = (magKappa : ℝ) • ![magAlpha, 1] := by
  rw [magCoeffs, algFreq_two]
  ext i
  fin_cases i <;> simp [magAlpha]
  ring

/-! ### The finite check -/

/-- The integer check of `(|a| + |b|) |a α + b| ≥ 1/10` from `α ∈ [7910763, 7910764]/13618000`
(trivially true when `a = 0` or `|a| + |b| > 9`). -/
def magChkPair (a b : ℤ) : Bool :=
  a == 0 || decide (9 < |a| + |b|) ||
    (decide (0 < a * 7910763 + b * 13618000) && decide (0 < a * 7910764 + b * 13618000) &&
      decide (13618000 ≤ 10 * (|a| + |b|) * (a * 7910763 + b * 13618000)) &&
      decide (13618000 ≤ 10 * (|a| + |b|) * (a * 7910764 + b * 13618000))) ||
    (decide (a * 7910763 + b * 13618000 < 0) && decide (a * 7910764 + b * 13618000 < 0) &&
      decide (13618000 ≤ -(10 * (|a| + |b|) * (a * 7910763 + b * 13618000))) &&
      decide (13618000 ≤ -(10 * (|a| + |b|) * (a * 7910764 + b * 13618000))))

/-- The check over `|a|, |b| ≤ 9`. -/
def magChkAll : Bool :=
  (List.range 19).all fun i => (List.range 19).all fun j => magChkPair ((i : ℤ) - 9) ((j : ℤ) - 9)

theorem magChkAll_eq : magChkAll = true := by decide +kernel

theorem magChkPair_of_abs_le {a b : ℤ} (ha : |a| ≤ 9) (hb : |b| ≤ 9) : magChkPair a b = true := by
  have h := magChkAll_eq
  simp only [magChkAll, List.all_eq_true, List.mem_range] at h
  have ha' := abs_le.1 ha
  have hb' := abs_le.1 hb
  have := h (a + 9).toNat (by omega) (b + 9).toNat (by omega)
  rwa [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega), add_sub_cancel_right,
    add_sub_cancel_right] at this

private lemma magAlpha_lo : (7910763 : ℝ) / 13618000 ≤ magAlpha := by
  have := sqrt5_bounds
  unfold magAlpha
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  linarith

private lemma magAlpha_hi : magAlpha ≤ (7910764 : ℝ) / 13618000 := by
  have := sqrt5_bounds
  unfold magAlpha
  rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
  linarith

/-- The small pairs: `1/10 ≤ (|a| + |b|) |a α + b|` for `a ≠ 0`, `|a| + |b| ≤ 9`. -/
private lemma small_bound {a b : ℤ} (ha0 : a ≠ 0) (hs : |a| + |b| ≤ 9) :
    1 / 10 ≤ (|(a : ℝ)| + |(b : ℝ)|) * |a * magAlpha + b| := by
  have hchk := magChkPair_of_abs_le (a := a) (b := b) (by linarith [abs_nonneg b])
    (by linarith [abs_nonneg a])
  have hs' : ¬ 9 < |a| + |b| := not_lt.2 hs
  simp only [magChkPair, ha0, hs', beq_iff_eq, decide_false, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, false_or, and_assoc] at hchk
  have hlo := magAlpha_lo
  have hhi := magAlpha_hi
  set D : ℝ := 13618000
  set s : ℝ := |(a : ℝ)| + |(b : ℝ)| with hsdef
  have hsZ : ((|a| + |b| : ℤ) : ℝ) = s := by push_cast; rfl
  -- `D (aα + b)` lies between `u = a L + b D` and `v = a H + b D`
  have hDx : D * (a * magAlpha + b) = a * (D * magAlpha) + b * D := by ring
  have hL : (7910763 : ℝ) ≤ D * magAlpha := by
    have := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 13618000)
    simp only [D]; field_simp at this ⊢; linarith
  have hH : D * magAlpha ≤ 7910764 := by
    have := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 13618000)
    simp only [D]; field_simp at this ⊢; linarith
  have hbetween : (a * 7910763 + b * D ≤ D * (a * magAlpha + b) ∧
        D * (a * magAlpha + b) ≤ a * 7910764 + b * D) ∨
      (a * 7910764 + b * D ≤ D * (a * magAlpha + b) ∧
        D * (a * magAlpha + b) ≤ a * 7910763 + b * D) := by
    rw [hDx]
    rcases le_total 0 (a : ℝ) with h | h
    · left
      exact ⟨by nlinarith, by nlinarith⟩
    · right
      exact ⟨by nlinarith, by nlinarith⟩
  have hD : (0 : ℝ) < D := by norm_num [D]
  rcases hchk with ⟨hu, hv, hsu, hsv⟩ | ⟨hu, hv, hsu, hsv⟩
  · have hu' : (0 : ℝ) < a * 7910763 + b * D := by simp only [D]; exact_mod_cast hu
    have hv' : (0 : ℝ) < a * 7910764 + b * D := by simp only [D]; exact_mod_cast hv
    have hsu' : D ≤ 10 * s * (a * 7910763 + b * D) := by
      rw [← hsZ]; simp only [D]; exact_mod_cast hsu
    have hsv' : D ≤ 10 * s * (a * 7910764 + b * D) := by
      rw [← hsZ]; simp only [D]; exact_mod_cast hsv
    have hs0 : 0 ≤ s := by positivity
    have hge : D ≤ 10 * s * (D * (a * magAlpha + b)) := by
      rcases hbetween with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hsu'.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
      · exact hsv'.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    have hx : 0 < a * magAlpha + (b : ℝ) := by
      by_contra hn; push Not at hn; nlinarith
    rw [abs_of_pos hx]
    nlinarith
  · have hu' : a * 7910763 + b * D < (0 : ℝ) := by simp only [D]; exact_mod_cast hu
    have hv' : a * 7910764 + b * D < (0 : ℝ) := by simp only [D]; exact_mod_cast hv
    have hsu' : D ≤ -(10 * s * (a * 7910763 + b * D)) := by
      rw [← hsZ]; simp only [D]; exact_mod_cast hsu
    have hsv' : D ≤ -(10 * s * (a * 7910764 + b * D)) := by
      rw [← hsZ]; simp only [D]; exact_mod_cast hsv
    have hs0 : 0 ≤ s := by positivity
    have hge : D ≤ -(10 * s * (D * (a * magAlpha + b))) := by
      rcases hbetween with ⟨-, h1⟩ | ⟨-, h1⟩
      · have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 10 * s)
        linarith
      · have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 10 * s)
        linarith
    have hx : a * magAlpha + (b : ℝ) < 0 := by
      by_contra hn; push Not at hn; nlinarith
    rw [abs_of_neg hx]
    nlinarith

/-! ### The norm argument -/

/-- The conjugate `α' = (7913 + √5)/13618`. -/
private def magAlphaConj : ℝ := (7913 + Real.sqrt 5) / 13618

private lemma irr_comb (e : ℤ) (he : e = 1 ∨ e = -1) :
    Irrational ((7913 + e * Real.sqrt 5) / 13618) := by
  rintro ⟨q, hq⟩
  apply sqrt5_irrational
  have he0 : (e : ℝ) ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  refine ⟨(13618 * q - 7913) / e, ?_⟩
  push_cast
  rw [hq]
  field_simp
  ring

private lemma ne_zero_of_irrational {x : ℝ} (hx : Irrational x) {a b : ℤ} (ha : a ≠ 0) :
    (a : ℝ) * x + b ≠ 0 := by
  intro h
  apply hx
  refine ⟨(-b / a : ℚ), ?_⟩
  have : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  push_cast; field_simp; linarith

/-- The large pairs: `1/10 ≤ (|a| + |b|) |a α + b|` for `a ≠ 0`, `|a| + |b| ≥ 10`. -/
private lemma large_bound {a b : ℤ} (ha0 : a ≠ 0) (hs : 10 ≤ |(a : ℝ)| + |(b : ℝ)|) :
    1 / 10 ≤ (|(a : ℝ)| + |(b : ℝ)|) * |a * magAlpha + b| := by
  have h5 := sqrt5_bounds
  set s : ℝ := |(a : ℝ)| + |(b : ℝ)| with hsdef
  set x : ℝ := a * magAlpha + b with hxdef
  set y : ℝ := a * magAlphaConj + b with hydef
  have hNr : (2299 * a ^ 2 + 7913 * a * b + 6809 * b ^ 2 : ℝ) = 6809 * (x * y) := by
    simp only [hxdef, hydef, magAlpha, magAlphaConj]
    linear_combination ((a : ℝ) ^ 2 / 27236) * sqrt5_sq
  set N : ℤ := 2299 * a ^ 2 + 7913 * a * b + 6809 * b ^ 2 with hNdef
  have hNcast : (N : ℝ) = 6809 * (x * y) := by rw [← hNr]; simp [hNdef]
  have hx0 : x ≠ 0 := by
    have := irr_comb (-1) (Or.inr rfl)
    push_cast at this
    exact ne_zero_of_irrational (by simpa [magAlpha, sub_eq_add_neg] using this) ha0
  have hy0 : y ≠ 0 := by
    have := irr_comb 1 (Or.inl rfl)
    push_cast at this
    exact ne_zero_of_irrational (by simpa [magAlphaConj] using this) ha0
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hNcast
    rcases mul_eq_zero.1 (by linarith : x * y = 0) with h | h
    · exact hx0 h
    · exact hy0 h
  have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN0
  set d := |x| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hprod : 1 / 6809 ≤ d * |y| := by
    rw [hd, ← abs_mul]
    have : |(N : ℝ)| = 6809 * |x * y| := by rw [hNcast, abs_mul]; norm_num
    rw [div_le_iff₀ (by norm_num)]; linarith
  have hy : |y| ≤ d + s * (9 / 4 / 6809) := by
    have e : y = x + a * (Real.sqrt 5 / 6809) := by
      simp only [hxdef, hydef, magAlpha, magAlphaConj]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt 5 / 6809)]
    have h1 : |(a : ℝ)| ≤ s := by simp only [hsdef]; linarith [abs_nonneg (b : ℝ)]
    have h2 : Real.sqrt 5 / 6809 ≤ 9 / 4 / 6809 := by
      rw [div_le_div_iff_of_pos_right (by norm_num)]; linarith
    have := mul_le_mul h1 h2 (by positivity) (by positivity)
    linarith
  by_contra hlt
  push Not at hlt
  have hds : d * s < 1 / 10 := by linarith [mul_comm s d]
  have hd1 : d < 1 / 100 := by
    by_contra h; push Not at h; nlinarith
  have key : d * (d + s * (9 / 4 / 6809)) < 1 / 6809 := by nlinarith
  have := mul_le_mul_of_nonneg_left hy hd0
  linarith

/-- `(a, b) ≠ 0 → 1/(10 (|a| + |b|)) ≤ |a α + b|`. -/
theorem magAlpha_lower (a b : ℤ) (hab : (a, b) ≠ (0, 0)) :
    1 / 10 / (|(a : ℝ)| + |(b : ℝ)|) ≤ |a * magAlpha + b| := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by rintro rfl; exact hab (by simp [ha])
    have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
    subst ha
    simp only [Int.cast_zero, abs_zero, zero_add, zero_mul]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · have ha1 : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
    have hspos : 0 < |(a : ℝ)| + |(b : ℝ)| := by linarith [abs_nonneg (b : ℝ)]
    rw [div_le_iff₀ hspos, mul_comm]
    rcases le_or_gt (|a| + |b|) 9 with h | h
    · exact small_bound ha h
    · apply large_bound ha
      have : (10 : ℤ) ≤ |a| + |b| := h
      have : (10 : ℝ) ≤ ((|a| + |b| : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at this
      exact this

theorem magAlpha_isDiophantine : IsDiophantine (1 / 10) 1 ![magAlpha, 1] := by
  intro k hk
  have hk' : (k 0, k 1) ≠ (0, 0) := by
    intro h
    apply hk
    ext i
    fin_cases i
    · simpa using congrArg Prod.fst h
    · simpa using congrArg Prod.snd h
  simpa [Fin.sum_univ_two, Real.rpow_one] using magAlpha_lower (k 0) (k 1) hk'

private lemma isDiophantine_smul {γ τ s : ℝ} {ω : Fin 2 → ℝ} (hs : 0 < s)
    (h : IsDiophantine γ τ ω) : IsDiophantine (s * γ) τ (s • ω) := by
  intro k hk
  have hsum : ∑ i, (k i : ℝ) * (s • ω) i = s * ∑ i, (k i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum, abs_mul, abs_of_pos hs, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (h k hk) hs.le

theorem magKappa_pos : (0 : ℝ) < magKappa := by
  have : (0 : ℚ) < magKappa := by norm_num [magKappa, magScalar]
  exact_mod_cast this

theorem magFreq_isDiophantine :
    IsDiophantine ((magKappa : ℝ) / 10) 1 (algFreq 2 magCoeffs (Real.sqrt 5)) := by
  rw [magAlgFreq_eq, div_eq_mul_one_div]
  exact isDiophantine_smul magKappa_pos magAlpha_isDiophantine

end KAM.Magnetic

end
