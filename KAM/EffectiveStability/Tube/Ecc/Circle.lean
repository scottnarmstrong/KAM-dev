/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Rat.Floor

/-!
# Gaussian rationals and the rational circle chart (T2-CONF eccentricity enclosure)

Kernel-side arithmetic for the eccentricity enclosure of program T2-CONF (package N6,
`docs/explorations/sjsu-g2-handoffs/N6-Ecc.md`).

* `GQ`: Gaussian rationals `re + i·im` with multiplication, conjugation, powers, `Re (a · conj b)`
  (`GQ.reDot`) and the squared modulus (`GQ.nsq`), with their complex values (`GQ.toC`).
* `GZ`: Gaussian integers; `GZ.table`, `GZ.zpowT`: the table `G^j N^(M - j)` and integer powers
  read from it, `N^M (G/N)^m` for a unit `G/N` (`GZ.toC_zpowT`).
* `wt t = (1 + i t)/(1 - i t)`: the rational parametrization of the unit circle. Every point of the
  circle is `± wt t` with `|t| ≤ 1` (`exists_circ`); `circPt s t` is the exact rational point
  `± wt t` and `circDer s t` the exact derivative, with the quadratic remainder bound
  `norm_circ_remainder` and the chord bound `norm_circ_sub`.
-/

@[expose] public section

open Complex

namespace KAM.EffectiveStability.Tube

/-- A Gaussian rational `re + i·im`. -/
structure GQ where
  /-- The real part. -/
  re : ℚ
  /-- The imaginary part. -/
  im : ℚ

namespace GQ

/-- The unit `1`. -/
def one : GQ := ⟨1, 0⟩

/-- Multiplication of Gaussian rationals. -/
def mul (a b : GQ) : GQ := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- Complex conjugation. -/
def conj (a : GQ) : GQ := ⟨a.re, -a.im⟩

/-- Natural powers. -/
def npow (a : GQ) : ℕ → GQ
  | 0 => one
  | n + 1 => mul (npow a n) a

/-- `Re (a · conj b)`. -/
def reDot (a b : GQ) : ℚ := a.re * b.re + a.im * b.im

/-- The squared modulus. -/
def nsq (a : GQ) : ℚ := a.re * a.re + a.im * a.im

/-- The complex value. -/
noncomputable def toC (a : GQ) : ℂ := ⟨a.re, a.im⟩

@[simp] theorem toC_re (a : GQ) : (toC a).re = a.re := rfl
@[simp] theorem toC_im (a : GQ) : (toC a).im = a.im := rfl

theorem toC_one : toC one = 1 := by apply Complex.ext <;> simp [toC, one]

theorem toC_mul (a b : GQ) : toC (mul a b) = toC a * toC b := by
  apply Complex.ext <;> simp [toC, mul]

theorem toC_conj (a : GQ) : toC (conj a) = (starRingEnd ℂ) (toC a) := by
  apply Complex.ext <;> simp [toC, conj]

theorem toC_npow (a : GQ) (n : ℕ) : toC (npow a n) = toC a ^ n := by
  induction n with
  | zero => simp [npow, toC_one]
  | succ n ih => rw [npow, toC_mul, ih, pow_succ]

theorem reDot_eq (a b : GQ) : ((reDot a b : ℚ) : ℝ) = (toC a * (starRingEnd ℂ) (toC b)).re := by
  simp [reDot, toC]

theorem nsq_eq (a : GQ) : ((nsq a : ℚ) : ℝ) = Complex.normSq (toC a) := by
  simp [nsq, toC, Complex.normSq_apply]

end GQ

/-! ### Gaussian integers -/

/-- A Gaussian integer `re + i·im`. -/
structure GZ where
  /-- The real part. -/
  re : ℤ
  /-- The imaginary part. -/
  im : ℤ

namespace GZ

/-- Multiplication of Gaussian integers. -/
def mul (a b : GZ) : GZ := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- The real part of a product, `Re (a b)`. -/
def reMul (a b : GZ) : ℤ := a.re * b.re - a.im * b.im

/-- Complex conjugation. -/
def conj (a : GZ) : GZ := ⟨a.re, -a.im⟩

/-- Multiplication by an integer. -/
def smul (c : ℤ) (a : GZ) : GZ := ⟨c * a.re, c * a.im⟩

/-- Natural powers. -/
def npow (a : GZ) : ℕ → GZ
  | 0 => ⟨1, 0⟩
  | n + 1 => mul (npow a n) a

/-- The table `[G^j N^(M - j)]_{j ≤ M}`: the powers of `G/N` scaled by `N^M`. -/
def table (G : GZ) (N : ℤ) (M : ℕ) : List GZ :=
  (List.range (M + 1)).map fun j => smul (N ^ (M - j)) (npow G j)

/-- The integer power read from a table: for `|m| ≤ M` and a unit `G/N`, `N^M (G/N)^m`
(`toC_zpowT`). -/
def zpowT (T : List GZ) : ℤ → GZ
  | .ofNat n => T.getD n ⟨0, 0⟩
  | .negSucc n => conj (T.getD (n + 1) ⟨0, 0⟩)

/-- The complex value. -/
noncomputable def toC (a : GZ) : ℂ := ⟨a.re, a.im⟩

theorem toC_mul (a b : GZ) : toC (mul a b) = toC a * toC b := by
  apply Complex.ext <;> simp [toC, mul]

theorem reMul_eq (a b : GZ) : ((reMul a b : ℤ) : ℝ) = (toC a * toC b).re := by
  simp [reMul, toC]

theorem toC_conj (a : GZ) : toC (conj a) = (starRingEnd ℂ) (toC a) := by
  apply Complex.ext <;> simp [toC, conj]

theorem toC_smul (c : ℤ) (a : GZ) : toC (smul c a) = (c : ℂ) * toC a := by
  apply Complex.ext <;> simp [toC, smul]

theorem toC_npow (a : GZ) (n : ℕ) : toC (npow a n) = toC a ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [npow, toC]
  | succ n ih => rw [npow, toC_mul, ih, pow_succ]

theorem getD_table (G : GZ) (N : ℤ) (M n : ℕ) (hn : n ≤ M) :
    (table G N M).getD n ⟨0, 0⟩ = smul (N ^ (M - n)) (npow G n) := by
  unfold table
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- The table value: if `toC G = N · P` with `‖P‖ = 1`, `N ≠ 0` and `|m| ≤ M`, the entry is
`N^M P^m`. -/
theorem toC_zpowT {G : GZ} {N : ℤ} {P : ℂ} (hN : N ≠ 0) (hG : toC G = (N : ℂ) * P)
    (hP : Complex.normSq P = 1) (M : ℕ) (m : ℤ) (hm : m.natAbs ≤ M) :
    toC (zpowT (table G N M) m) = (N : ℂ) ^ M * P ^ m := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  cases m with
  | ofNat n =>
    have hn : n ≤ M := by simpa using hm
    rw [zpowT, getD_table G N M n hn, toC_smul, toC_npow, hG, mul_pow]
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    push_cast
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
  | negSucc n =>
    have hn : n + 1 ≤ M := by simpa [Int.natAbs_negSucc] using hm
    rw [zpowT, getD_table G N M (n + 1) hn, toC_conj, toC_smul, toC_npow, hG, mul_pow, zpow_negSucc]
    have h1 : Complex.normSq (P ^ (n + 1)) = 1 := by rw [map_pow, hP, one_pow]
    rw [Complex.inv_def, h1]
    simp only [map_mul, map_pow, map_intCast, Complex.ofReal_one,
      inv_one, mul_one]
    push_cast
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

end GZ

/-! ### The rational circle chart -/

/-- `wt t = (1 + i t)/(1 - i t)`, a point of the unit circle. -/
noncomputable def wt (t : ℝ) : ℂ := (1 + t * I) / (1 - t * I)

/-- The sign `±1` coded by a Boolean. -/
def sgnQ (b : Bool) : ℚ := if b then 1 else -1

/-- The exact rational point `± wt t = ±((1 - t²)/(1 + t²), 2t/(1 + t²))`. -/
def circPt (s : Bool) (t : ℚ) : GQ :=
  ⟨sgnQ s * ((1 - t * t) / (1 + t * t)), sgnQ s * (2 * t / (1 + t * t))⟩

/-- The exact derivative `± wt' t = ± 2i/(1 - i t)² = ±(-4t, 2(1 - t²))/(1 + t²)²`. -/
def circDer (s : Bool) (t : ℚ) : GQ :=
  ⟨sgnQ s * (-4 * t / ((1 + t * t) * (1 + t * t))),
    sgnQ s * (2 * (1 - t * t) / ((1 + t * t) * (1 + t * t)))⟩

/-- The sign `±1` as an integer. -/
def sgnZ (b : Bool) : ℤ := if b then 1 else -1

/-- The Gaussian integer `±((q² - p²) + 2pq i)` of the chart point at `t = p/q` (lowest terms):
`circG s t = circN t · circPt s t` (`toC_circG`). -/
def circG (s : Bool) (t : ℚ) : GZ :=
  ⟨sgnZ s * ((t.den : ℤ) ^ 2 - t.num ^ 2), sgnZ s * (2 * t.num * t.den)⟩

/-- The norm `q² + p²` of `circG s t`, `t = p/q`. -/
def circN (t : ℚ) : ℤ := (t.den : ℤ) ^ 2 + t.num ^ 2

theorem circN_pos (t : ℚ) : 0 < circN t := by
  unfold circN; have := t.den_pos; positivity

theorem sgnQ_sq (b : Bool) : sgnQ b * sgnQ b = 1 := by cases b <;> norm_num [sgnQ]

theorem abs_sgnQ (b : Bool) : |((sgnQ b : ℚ) : ℝ)| = 1 := by cases b <;> norm_num [sgnQ]

theorem one_sub_mul_I_ne_zero (t : ℝ) : (1 : ℂ) - t * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem normSq_one_sub_mul_I (t : ℝ) : Complex.normSq (1 - t * I) = 1 + t ^ 2 := by
  simp [Complex.normSq_apply]; ring

theorem norm_wt (t : ℝ) : ‖wt t‖ = 1 := by
  unfold wt
  rw [norm_div]
  have h1 : ‖(1 : ℂ) + t * I‖ = ‖(1 : ℂ) - t * I‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
  rw [h1, div_self]
  exact (norm_ne_zero_iff).mpr (one_sub_mul_I_ne_zero t)

/-- `wt t` in coordinates. -/
theorem wt_eq (t : ℝ) : wt t = ⟨(1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)⟩ := by
  have hne := one_sub_mul_I_ne_zero t
  have hd : (1 : ℝ) + t * t ≠ 0 := ne_of_gt (by nlinarith [mul_self_nonneg (t : ℝ)])
  unfold wt
  rw [div_eq_iff hne]
  apply Complex.ext <;> simp <;> field_simp <;> ring

theorem toC_circPt (s : Bool) (t : ℚ) :
    GQ.toC (circPt s t) = ((sgnQ s : ℚ) : ℂ) * wt (t : ℝ) := by
  rw [wt_eq]
  apply Complex.ext <;> simp [circPt, GQ.toC]

theorem nsq_circPt (s : Bool) (t : ℚ) : GQ.nsq (circPt s t) = 1 := by
  have hd : (1 : ℚ) + t * t ≠ 0 := ne_of_gt (by nlinarith [mul_self_nonneg t])
  have h2 := sgnQ_sq s
  simp only [GQ.nsq, circPt]
  field_simp
  linear_combination ((1 - t * t) ^ 2 + (2 * t) ^ 2) * h2

theorem toC_circDer (s : Bool) (t : ℚ) :
    GQ.toC (circDer s t) = ((sgnQ s : ℚ) : ℂ) * (2 * I / (1 - (t : ℝ) * I) ^ 2) := by
  have hne := one_sub_mul_I_ne_zero (t : ℝ)
  have hd : (1 : ℝ) + t * t ≠ 0 := ne_of_gt (by nlinarith [mul_self_nonneg (t : ℝ)])
  rw [mul_div_assoc', eq_div_iff (pow_ne_zero 2 hne)]
  apply Complex.ext <;> simp [circDer, GQ.toC, pow_two] <;> field_simp <;> ring

theorem norm_toC_circDer (s : Bool) (t : ℚ) :
    ‖GQ.toC (circDer s t)‖ = 2 / (1 + (t : ℝ) ^ 2) := by
  rw [toC_circDer, norm_mul, norm_div, norm_pow, norm_mul]
  have h1 : ‖((sgnQ s : ℚ) : ℂ)‖ = 1 := by
    rw [show (((sgnQ s : ℚ) : ℂ)) = (((sgnQ s : ℚ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_sgnQ]
  have h2 : ‖(1 : ℂ) - (t : ℝ) * I‖ ^ 2 = 1 + (t : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_one_sub_mul_I]
  rw [h1, h2]
  simp

theorem toC_circG (s : Bool) (t : ℚ) :
    GZ.toC (circG s t) = ((circN t : ℤ) : ℂ) * GQ.toC (circPt s t) := by
  have hq : (0 : ℝ) < t.den := by exact_mod_cast t.den_pos
  have ht : (t : ℝ) = (t.num : ℝ) / (t.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hd : (1 : ℝ) + (t : ℝ) * t ≠ 0 := ne_of_gt (by nlinarith [mul_self_nonneg (t : ℝ)])
  have hs : ((sgnZ s : ℤ) : ℝ) = ((sgnQ s : ℚ) : ℝ) := by cases s <;> simp [sgnZ, sgnQ]
  apply Complex.ext
  · simp only [GZ.toC, circG, circN, GQ.toC, circPt, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, zero_mul, sub_zero]
    push_cast
    rw [hs, ht]; field_simp
  · simp only [GZ.toC, circG, circN, GQ.toC, circPt, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, add_zero]
    push_cast
    rw [hs, ht]; field_simp

/-- The quadratic remainder of the chart: `‖± wt t - P - (t - t_c) D‖ ≤ 2 (t - t_c)²/(1 + t_c²)`
with `P = circPt s t_c` and `D = circDer s t_c`. -/
theorem norm_circ_remainder (s : Bool) (tc : ℚ) (t : ℝ) :
    ‖((sgnQ s : ℚ) : ℂ) * wt t - GQ.toC (circPt s tc) -
        ((t - tc : ℝ) : ℂ) * GQ.toC (circDer s tc)‖ ≤
      2 * (t - tc) ^ 2 / (1 + (tc : ℝ) ^ 2) := by
  set c : ℝ := (tc : ℝ) with hcdef
  set A : ℂ := 1 - (t : ℂ) * I with hAdef
  set B : ℂ := 1 - (c : ℂ) * I with hBdef
  have hA : A ≠ 0 := one_sub_mul_I_ne_zero t
  have hB : B ≠ 0 := one_sub_mul_I_ne_zero c
  have hwt : ∀ x : ℝ, wt x = 2 / (1 - (x : ℂ) * I) - 1 := fun x => by
    unfold wt; field_simp [one_sub_mul_I_ne_zero x]; ring
  have hBA : B - A = ((t - c : ℝ) : ℂ) * I := by rw [hAdef, hBdef]; push_cast; ring
  have hkey : 2 / A - 1 - (2 / B - 1) - 2 * (B - A) / B ^ 2 = 2 * (B - A) ^ 2 / (A * B ^ 2) := by
    field_simp; ring
  have hid : ((sgnQ s : ℚ) : ℂ) * wt t - GQ.toC (circPt s tc) -
      ((t - c : ℝ) : ℂ) * GQ.toC (circDer s tc) =
      ((sgnQ s : ℚ) : ℂ) * (2 * (B - A) ^ 2 / (A * B ^ 2)) := by
    rw [toC_circPt, toC_circDer, hwt, hwt, ← hkey, ← hcdef]
    have : ((t - c : ℝ) : ℂ) * (2 * I / B ^ 2) = 2 * (B - A) / B ^ 2 := by rw [hBA]; ring
    rw [← hAdef, ← hBdef, ← this]
    ring
  have hnBA : ‖B - A‖ = |t - c| := by
    rw [hBA, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hid, norm_mul, norm_div, norm_mul, norm_pow, norm_mul, norm_pow, hnBA]
  have h1 : ‖((sgnQ s : ℚ) : ℂ)‖ = 1 := by
    rw [show (((sgnQ s : ℚ) : ℂ)) = (((sgnQ s : ℚ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_sgnQ]
  have h2 : ‖B‖ ^ 2 = 1 + c ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, hBdef, normSq_one_sub_mul_I]
  have h3 : 1 ≤ ‖A‖ := by
    have : 1 ≤ ‖A‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hAdef, normSq_one_sub_mul_I]; nlinarith [sq_nonneg t]
    nlinarith [norm_nonneg A]
  rw [h1, h2, sq_abs]
  have hc : 0 < 1 + c ^ 2 := by positivity
  have h22 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h22, one_mul, div_le_div_iff₀ (by positivity) hc]
  have h0 : 0 ≤ 2 * (t - c) ^ 2 * (1 + c ^ 2) := by positivity
  nlinarith

/-- The chord bound on a chart cell: for `|t - t_c| ≤ h`, `‖± wt t - P‖ ≤ 2h(1 + h)/(1 + t_c²)`. -/
theorem norm_circ_sub (s : Bool) (tc : ℚ) (t h : ℝ) (ht : |t - tc| ≤ h) :
    ‖((sgnQ s : ℚ) : ℂ) * wt t - GQ.toC (circPt s tc)‖ ≤ 2 * h * (1 + h) / (1 + (tc : ℝ) ^ 2) := by
  have hr := norm_circ_remainder s tc t
  have hc : 0 < 1 + (tc : ℝ) ^ 2 := by positivity
  have hh : 0 ≤ h := le_trans (abs_nonneg _) ht
  have hsq : (t - tc) ^ 2 ≤ h ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  calc ‖((sgnQ s : ℚ) : ℂ) * wt t - GQ.toC (circPt s tc)‖
      ≤ ‖((t - tc : ℝ) : ℂ) * GQ.toC (circDer s tc)‖ + ‖((sgnQ s : ℚ) : ℂ) * wt t -
          GQ.toC (circPt s tc) - ((t - tc : ℝ) : ℂ) * GQ.toC (circDer s tc)‖ := by
        have := norm_add_le (((t - tc : ℝ) : ℂ) * GQ.toC (circDer s tc))
          (((sgnQ s : ℚ) : ℂ) * wt t - GQ.toC (circPt s tc) -
            ((t - tc : ℝ) : ℂ) * GQ.toC (circDer s tc))
        simpa using this
    _ ≤ |t - tc| * (2 / (1 + (tc : ℝ) ^ 2)) + 2 * (t - tc) ^ 2 / (1 + (tc : ℝ) ^ 2) := by
        rw [norm_mul, norm_toC_circDer, Complex.norm_real, Real.norm_eq_abs]
        exact add_le_add le_rfl hr
    _ ≤ h * (2 / (1 + (tc : ℝ) ^ 2)) + 2 * h ^ 2 / (1 + (tc : ℝ) ^ 2) := by
        gcongr
    _ = 2 * h * (1 + h) / (1 + (tc : ℝ) ^ 2) := by ring

/-- A chart point for nonnegative cosine: `c + i y = wt (y/(1 + c))` with `|y/(1 + c)| ≤ 1`. -/
theorem wt_of_cos_nonneg {c y : ℝ} (h : c ^ 2 + y ^ 2 = 1) (hc : 0 ≤ c) :
    wt (y / (1 + c)) = ⟨c, y⟩ ∧ -1 ≤ y / (1 + c) ∧ y / (1 + c) ≤ 1 := by
  have h1 : 0 < 1 + c := by linarith
  have hy : |y| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg c]
  refine ⟨?_, ?_, ?_⟩
  · rw [wt_eq]
    have hd : (1 + c) ^ 2 + y ^ 2 ≠ 0 := by positivity
    apply Complex.ext <;> simp <;> field_simp
    · linear_combination (-(1 + c)) * h
    · linear_combination (-y) * h
  · rw [le_div_iff₀ h1]; linarith [neg_abs_le y]
  · rw [div_le_iff₀ h1]; linarith [le_abs_self y]

/-- Every point of the unit circle is `± wt t` with `|t| ≤ 1`. -/
theorem exists_circ (φ : ℝ) :
    ∃ s : Bool, ∃ t : ℝ, -1 ≤ t ∧ t ≤ 1 ∧ Complex.exp (φ * I) = ((sgnQ s : ℚ) : ℂ) * wt t := by
  have hpy := Real.cos_sq_add_sin_sq φ
  by_cases hc : 0 ≤ Real.cos φ
  · obtain ⟨h1, h2, h3⟩ := wt_of_cos_nonneg hpy hc
    refine ⟨true, _, h2, h3, ?_⟩
    rw [h1, Complex.exp_mul_I]
    apply Complex.ext <;> simp [sgnQ, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  · have hpy' : (-Real.cos φ) ^ 2 + (-Real.sin φ) ^ 2 = 1 := by nlinarith
    obtain ⟨h1, h2, h3⟩ := wt_of_cos_nonneg hpy' (by linarith)
    refine ⟨false, _, h2, h3, ?_⟩
    rw [h1, Complex.exp_mul_I]
    apply Complex.ext <;> simp [sgnQ, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

end KAM.EffectiveStability.Tube

end
