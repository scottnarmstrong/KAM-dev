/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Trig.Poly
public import KAM.Certificate.Poly.Layout
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.List.GetD

/-!
# Exact products of trigonometric polynomials (T2-CONF, N3)

The exact product of two polynomials on dense square layouts of a common row stride `S` is the
one-dimensional convolution `listConv` (`KAM.Certificate.Poly.Packed`) of their slot lists, read on
the layout of half-width `C_a + C_b` (Kronecker substitution), provided:
* the padding columns of both factors are zero (`colsOk`);
* no row wraps: `2 (C_a + C_b) < S`;
* one factor is **symmetric** for its parity (`symOk`: the list reversed is the list, resp. its
  negation). On the square layout, reversal is the reflection `k ↦ -k` of the modes, so an even
  symmetric list is a cosine series `Σ a_k e^{ik·φ}`, `a_{-k} = a_k`, and an odd antisymmetric list
  is `Σ i b_k e^{ik·φ}`, `b_{-k} = -b_k`.

Main results:
* `evalK_eq_re`: `evalK κ p d φ = Re (ω_p Σ_i d_i e^{i κ i · φ})`, `ω_false = 1`, `ω_true = i`;
* `ek_mul`: the complex sums multiply by `listConv` (Kronecker);
* `evalK_mul`: **the product identity**
  `evalK (key C_a S) p a φ * evalK (key C_b S) q b φ =
    psgn (p && q) * evalK (key (C_a + C_b) S) (xor p q) (listConv a b) φ`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset Complex KAM.Certificate

/-! ### The complex form -/

/-- `ω_p`: `1` (even) or `i` (odd). -/
noncomputable def omega (p : Bool) : ℂ := if p then I else 1

/-- The complex exponential sum `Σ_i d_i e^{i κ i · φ}`. -/
noncomputable def ek (κ : ℕ → ℤ × ℤ) (d : List ℤ) (φ : Fin 2 → ℝ) : ℂ :=
  ∑ i ∈ range d.length, (d.getD i 0 : ℂ) * exp ((kdot (κ i) φ : ℂ) * I)

theorem trig_eq_re (p : Bool) (x : ℝ) : trig p x = (omega p * exp ((x : ℂ) * I)).re := by
  cases p
  · simp [trig, omega, exp_ofReal_mul_I_re]
  · simp [trig, omega, exp_ofReal_mul_I_im]

theorem evalK_eq_re (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ) :
    evalK κ p d φ = (omega p * ek κ d φ).re := by
  rw [evalK, ek, mul_sum, re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [trig_eq_re, mul_left_comm, show ((d.getD i 0 : ℤ) : ℂ) = (((d.getD i 0 : ℤ) : ℝ) : ℂ) by
    push_cast; rfl, re_ofReal_mul]

/-! ### Square layouts: reflection and addition of keys -/

theorem Layout.len_pos (C S : ℕ) : 0 < Layout.len C S := by unfold Layout.len; omega

/-- On the square layout, reversal of the slots is the reflection of the modes. -/
theorem Layout.key_reflect {C S i : ℕ} (hS : 2 * C < S) (hi : i < Layout.len C S)
    (hc : i % S ≤ 2 * C) : Layout.key C S (Layout.len C S - 1 - i) = -Layout.key C S i := by
  have hS0 : 0 < S := by omega
  set a := i % S with ha
  set b := i / S with hb
  have hab : a + S * b = i := Nat.mod_add_div i S
  have hb2 : b ≤ 2 * C := by
    by_contra hn
    have : S * (2 * C + 1) ≤ S * b := Nat.mul_le_mul_left S (by omega)
    have hl : Layout.len C S = 2 * C * S + 2 * C + 1 := rfl
    nlinarith
  have hY : S * (2 * C - b) = S * (2 * C) - S * b := Nat.mul_sub S (2 * C) b
  have hYle : S * b ≤ S * (2 * C) := Nat.mul_le_mul_left S hb2
  have hj : Layout.len C S - 1 - i = (2 * C - a) + S * (2 * C - b) := by
    have hl : Layout.len C S = S * (2 * C) + 2 * C + 1 := by unfold Layout.len; ring
    rw [hl, hY]
    omega
  have hm : (Layout.len C S - 1 - i) % S = 2 * C - a := by
    rw [hj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hd : (Layout.len C S - 1 - i) / S = 2 * C - b := by
    rw [hj, Nat.add_mul_div_left _ _ hS0, Nat.div_eq_of_lt (by omega), zero_add]
  refine Prod.ext ?_ ?_
  · simp only [Layout.key, hm, Prod.fst_neg]
    omega
  · simp only [Layout.key, hd, Prod.snd_neg]
    omega

/-- Keys add under the product layout when no row wraps. -/
theorem Layout.key_add {Ca Cb S i j : ℕ} (hS : 2 * (Ca + Cb) < S) (hi : i % S ≤ 2 * Ca)
    (hj : j % S ≤ 2 * Cb) :
    Layout.key (Ca + Cb) S (i + j) = Layout.key Ca S i + Layout.key Cb S j := by
  have hS0 : 0 < S := by omega
  have hij : i + j = (i % S + j % S) + S * (i / S + j / S) := by
    have h1 := Nat.mod_add_div i S
    have h2 := Nat.mod_add_div j S
    rw [mul_add]
    omega
  have hm : (i + j) % S = i % S + j % S := by
    rw [hij, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hd : (i + j) / S = i / S + j / S := by
    rw [hij, Nat.add_mul_div_left _ _ hS0, Nat.div_eq_of_lt (by omega), zero_add]
  refine Prod.ext ?_ ?_
  · simp only [Layout.key, hm, Prod.fst_add]
    push_cast
    ring
  · simp only [Layout.key, hd, Prod.snd_add]
    push_cast
    ring

theorem kdot_add (k l : ℤ × ℤ) (φ : Fin 2 → ℝ) : kdot (k + l) φ = kdot k φ + kdot l φ := by
  simp only [kdot, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem kdot_neg (k : ℤ × ℤ) (φ : Fin 2 → ℝ) : kdot (-k) φ = -kdot k φ := by
  simp only [kdot, Prod.fst_neg, Prod.snd_neg]
  push_cast
  ring

/-! ### Symmetry -/

/-- The symmetry check of parity `q`: the reversed list is the list (even) or its negation (odd). -/
def symOk (q : Bool) (d : List ℤ) : Bool :=
  d.reverse == (if q then d.map (fun c => -c) else d)

theorem symOk_spec {q : Bool} {d : List ℤ} (h : symOk q d = true) {i : ℕ} (hi : i < d.length) :
    d.getD (d.length - 1 - i) 0 = psgn q * d.getD i 0 := by
  have h' : d.reverse = (if q then d.map (fun c => -c) else d) := by simpa [symOk] using h
  have := congrArg (fun l => l.getD i 0) h'
  rw [List.getD_reverse i hi] at this
  rw [this]
  cases q
  · simp [psgn]
  · simp only [ite_true, psgn, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases d[i]? <;> simp

/-- A symmetric polynomial of parity `q` on a square layout has a real `ω_q`-sum. -/
theorem omega_ek_im {C S : ℕ} {q : Bool} {d : List ℤ} (hS : 2 * C < S)
    (hc : colsOk C S d = true) (hl : d.length = Layout.len C S) (hs : symOk q d = true)
    (φ : Fin 2 → ℝ) : (omega q * ek (Layout.key C S) d φ).im = 0 := by
  rw [← conj_eq_iff_im]
  -- conj of the sum, reflected
  have hconj : (starRingEnd ℂ) (ek (Layout.key C S) d φ) =
      (psgn q : ℂ) * ek (Layout.key C S) d φ := by
    rw [ek, map_sum, ← sum_range_reflect, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    have hi' : d.length - 1 - i < d.length := by omega
    rw [map_mul, ← exp_conj, map_mul, conj_ofReal, conj_I, map_intCast]
    by_cases h0 : d.getD i 0 = 0
    · have : d.getD (d.length - 1 - (d.length - 1 - i)) 0 = 0 := by
        rw [show d.length - 1 - (d.length - 1 - i) = i by omega, h0]
      rw [show d.getD (d.length - 1 - i) 0 = psgn q * d.getD i 0 from symOk_spec hs hi, h0]
      simp
    · have hcol := colsOk_spec hc i h0
      rw [symOk_spec hs hi, hl, Layout.key_reflect hS (hl ▸ hi) hcol, kdot_neg]
      push_cast
      ring_nf
  rw [map_mul, hconj]
  cases q <;> simp [omega, psgn]

/-- The real value of a symmetric polynomial is its `ω_q`-sum. -/
theorem evalK_eq_omega_ek {C S : ℕ} {q : Bool} {d : List ℤ} (hS : 2 * C < S)
    (hc : colsOk C S d = true) (hl : d.length = Layout.len C S) (hs : symOk q d = true)
    (φ : Fin 2 → ℝ) : (evalK (Layout.key C S) q d φ : ℂ) = omega q * ek (Layout.key C S) d φ := by
  rw [evalK_eq_re]
  exact Complex.ext (by simp) (by simp [omega_ek_im hS hc hl hs φ])

/-! ### Kronecker substitution -/

/-- The convolution of nonempty lists entrywise. -/
theorem listConv_getD {a b : List ℤ} (ha : a ≠ []) (hb : b ≠ []) {m : ℕ}
    (hm : m < a.length + b.length - 1) :
    (listConv a b).getD m 0 = ∑ p ∈ range (m + 1), a.getD p 0 * b.getD (m - p) 0 := by
  have hab : (a.isEmpty || b.isEmpty) = false := by
    simp [ha, hb]
  rw [listConv, hab]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hm, Option.map_some, Option.getD_some, sum_map_range_eq]

theorem length_listConv {a b : List ℤ} (ha : a ≠ []) (hb : b ≠ []) :
    (listConv a b).length = a.length + b.length - 1 := by
  have hab : (a.isEmpty || b.isEmpty) = false := by
    simp [ha, hb]
  rw [listConv, hab]
  simp only [Bool.false_eq_true, ↓reduceIte, List.length_map, List.length_range]

/-- **Kronecker**: on a common stride with zero padding and no row wrap, the complex sums of two
square-layout polynomials multiply by `listConv`. -/
theorem ek_mul {Ca Cb S : ℕ} {a b : List ℤ} (hS : 2 * (Ca + Cb) < S)
    (ha : colsOk Ca S a = true) (hb : colsOk Cb S b = true) (φ : Fin 2 → ℝ) :
    ek (Layout.key Ca S) a φ * ek (Layout.key Cb S) b φ =
      ek (Layout.key (Ca + Cb) S) (listConv a b) φ := by
  by_cases hae : a = []
  · subst hae; simp [ek, listConv]
  by_cases hbe : b = []
  · subst hbe; simp [ek, listConv]
  set H : ℕ → ℂ := fun m => exp ((kdot (Layout.key (Ca + Cb) S m) φ : ℂ) * I) with hH
  have hL : ek (Layout.key Ca S) a φ * ek (Layout.key Cb S) b φ =
      ∑ p ∈ range a.length, ∑ q ∈ range b.length,
        (a.getD p 0 : ℂ) * (b.getD q 0 : ℂ) * H (p + q) := by
    rw [ek, ek, sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    by_cases h0 : a.getD p 0 = 0
    · rw [h0]; simp
    by_cases h1 : b.getD q 0 = 0
    · rw [h1]; simp
    simp only [hH]
    rw [Layout.key_add hS (colsOk_spec ha p h0) (colsOk_spec hb q h1), kdot_add]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  rw [hL, ← sum_range_cauchy_weighted (fun p => (a.getD p 0 : ℂ)) (fun q => (b.getD q 0 : ℂ)) H
    a.length b.length
    (fun p hp => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hp])
    (fun q hq => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hq]),
    ek, length_listConv hae hbe]
  refine sum_congr rfl fun m hm => ?_
  rw [mem_range] at hm
  rw [listConv_getD hae hbe hm]
  push_cast
  rfl

/-- `ω_p ω_q = psgn (p ∧ q) · ω_{p ⊕ q}`. -/
theorem omega_mul (p q : Bool) : omega p * omega q = (psgn (p && q) : ℂ) * omega (xor p q) := by
  cases p <;> cases q <;> simp [omega, psgn]

/-- **The product identity.** If the second factor is symmetric for its parity (and both have zero
padding, no row wraps), the product of the values is `psgn (p ∧ q)` times the value of the
convolution, with parity `p ⊕ q`, on the layout of half-width `C_a + C_b`. -/
theorem evalK_mul {Ca Cb S : ℕ} {p q : Bool} {a b : List ℤ} (hS : 2 * (Ca + Cb) < S)
    (ha : colsOk Ca S a = true) (hb : colsOk Cb S b = true) (hbl : b.length = Layout.len Cb S)
    (hbs : symOk q b = true) (φ : Fin 2 → ℝ) :
    evalK (Layout.key Ca S) p a φ * evalK (Layout.key Cb S) q b φ =
      (psgn (p && q) : ℝ) * evalK (Layout.key (Ca + Cb) S) (xor p q) (listConv a b) φ := by
  have hS' : 2 * Cb < S := by omega
  have hB := evalK_eq_omega_ek hS' hb hbl hbs φ
  rw [evalK_eq_re (Layout.key Ca S) p a φ, ← re_mul_ofReal, hB,
    evalK_eq_re (Layout.key (Ca + Cb) S), ← ek_mul hS ha hb φ]
  rw [show omega p * ek (Layout.key Ca S) a φ * (omega q * ek (Layout.key Cb S) b φ) =
    (omega p * omega q) * (ek (Layout.key Ca S) a φ * ek (Layout.key Cb S) b φ) by ring,
    omega_mul, mul_assoc]
  rw [show ((psgn (p && q) : ℤ) : ℂ) = (((psgn (p && q) : ℤ) : ℝ) : ℂ) by push_cast; rfl,
    re_ofReal_mul]

/-- The product identity with the symmetric factor first. -/
theorem evalK_mul' {Ca Cb S : ℕ} {p q : Bool} {a b : List ℤ} (hS : 2 * (Ca + Cb) < S)
    (ha : colsOk Ca S a = true) (hb : colsOk Cb S b = true) (hal : a.length = Layout.len Ca S)
    (has : symOk p a = true) (φ : Fin 2 → ℝ) :
    evalK (Layout.key Ca S) p a φ * evalK (Layout.key Cb S) q b φ =
      (psgn (p && q) : ℝ) * evalK (Layout.key (Ca + Cb) S) (xor p q) (listConv b a) φ := by
  rw [mul_comm, evalK_mul (by omega) hb ha hal has φ, Bool.and_comm, Bool.xor_comm, add_comm Cb Ca]

end KAM.EffectiveStability.Tube

end
