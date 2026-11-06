/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.L1
public import KAM.EffectiveStability.Tube.Trig.Trunc

/-!
# Integer combinations of slot lists (T2-CONF, N7)

* `ladd`, `lcomb`: padded slotwise sums `Σ_t m_t l_t` of integer slot lists, with `getD_lcomb`,
  `packSum_lcomb` (the packing is linear: one big-integer combination in the kernel) and
  `evalK_lcomb` (the value is linear);
* `colsOk_listConv`: a product of zero-padded lists without row wrap is zero-padded on the sum
  layout; `colsOk_lcomb`;
* `wl1_le_mul_l1`: on a zero-padded list of the square layout `C`, `wl1 ≤ C · l1` (every mode has
  `|k_a| ≤ C`).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- Slotwise sum of two lists, padded by zeros to the longer length. -/
def ladd : List ℤ → List ℤ → List ℤ
  | [], m => m
  | l, [] => l
  | a :: l, b :: m => (a + b) :: ladd l m

theorem getD_ladd : ∀ (l m : List ℤ) (i : ℕ), (ladd l m).getD i 0 = l.getD i 0 + m.getD i 0
  | [], m, i => by simp [ladd]
  | a :: l, [], i => by simp [ladd]
  | a :: l, b :: m, 0 => by simp [ladd]
  | a :: l, b :: m, i + 1 => by
    simp only [ladd, List.getD_cons_succ]
    exact getD_ladd l m i

theorem length_ladd : ∀ (l m : List ℤ), (ladd l m).length = max l.length m.length
  | [], m => by simp [ladd]
  | a :: l, [] => by simp [ladd]
  | a :: l, b :: m => by simp [ladd, length_ladd l m, Nat.succ_max_succ]

/-- `Σ_t m_t l_t`, padded. -/
def lcomb : List (ℤ × List ℤ) → List ℤ
  | [] => []
  | t :: ts => ladd (t.2.map (t.1 * ·)) (lcomb ts)

theorem getD_lcomb : ∀ (ts : List (ℤ × List ℤ)) (i : ℕ),
    (lcomb ts).getD i 0 = (ts.map fun t => t.1 * t.2.getD i 0).sum
  | [], i => by simp [lcomb]
  | t :: ts, i => by
    rw [lcomb, getD_ladd, getD_lcomb ts i, getD_map_mul, List.map_cons, List.sum_cons]

theorem length_lcomb_le {n : ℕ} : ∀ (ts : List (ℤ × List ℤ)), (∀ t ∈ ts, t.2.length ≤ n) →
    (lcomb ts).length ≤ n
  | [], _ => by simp [lcomb]
  | t :: ts, h => by
    rw [lcomb, length_ladd, List.length_map]
    exact max_le (h t (by simp)) (length_lcomb_le ts fun x hx => h x (by simp [hx]))

theorem packSum_eq_sum_of_le (w : ℕ) (l : List ℤ) {n : ℕ} (hn : l.length ≤ n) :
    packSum w l = ∑ i ∈ range n, l.getD i 0 * (2 ^ w) ^ i := by
  rw [packSum_eq_sum]
  refine sum_subset (range_subset_range.mpr hn) fun i _ hi => ?_
  rw [mem_range, not_lt] at hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem packSum_ladd (w : ℕ) (l m : List ℤ) : packSum w (ladd l m) = packSum w l + packSum w m := by
  rw [packSum_eq_sum_of_le w _ (le_refl _), length_ladd,
    packSum_eq_sum_of_le w l (le_max_left l.length m.length),
    packSum_eq_sum_of_le w m (le_max_right l.length m.length), ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by rw [getD_ladd, add_mul]

theorem packSum_map_mul (w : ℕ) (m : ℤ) (l : List ℤ) :
    packSum w (l.map (m * ·)) = m * packSum w l := by
  rw [packSum_eq_sum, packSum_eq_sum, List.length_map, mul_sum]
  exact sum_congr rfl fun i _ => by rw [getD_map_mul, mul_assoc]

/-- **The packing is linear.** -/
theorem packSum_lcomb (w : ℕ) : ∀ ts : List (ℤ × List ℤ),
    packSum w (lcomb ts) = (ts.map fun t => t.1 * packSum w t.2).sum
  | [] => by simp [lcomb, packSum_nil]
  | t :: ts => by
    rw [lcomb, packSum_ladd, packSum_map_mul, packSum_lcomb w ts, List.map_cons, List.sum_cons]

theorem evalK_ladd (κ : ℕ → ℤ × ℤ) (p : Bool) (l m : List ℤ) (φ : Fin 2 → ℝ) :
    evalK κ p (ladd l m) φ = evalK κ p l φ + evalK κ p m φ := by
  rw [evalK, length_ladd, evalK_eq_sum_of_le κ p l φ (le_max_left l.length m.length),
    evalK_eq_sum_of_le κ p m φ (le_max_right l.length m.length), ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by rw [getD_ladd]; push_cast; ring

/-- **The value is linear.** -/
theorem evalK_lcomb (κ : ℕ → ℤ × ℤ) (p : Bool) : ∀ (ts : List (ℤ × List ℤ)) (φ : Fin 2 → ℝ),
    evalK κ p (lcomb ts) φ = (ts.map fun t => (t.1 : ℝ) * evalK κ p t.2 φ).sum
  | [], φ => by simp [lcomb, evalK]
  | t :: ts, φ => by
    rw [lcomb, evalK_ladd, evalK_map_mul, evalK_lcomb κ p ts φ, List.map_cons, List.sum_cons]

/-! ### Zero padding -/

theorem getD_eq_zero_of_colsOk {C S : ℕ} {d : List ℤ} (h : colsOk C S d = true) {i : ℕ}
    (hi : 2 * C < i % S) : d.getD i 0 = 0 := by
  by_contra hn
  have := colsOk_spec h i hn
  omega

/-- A product of zero-padded lists without row wrap is zero-padded on the sum layout. -/
theorem colsOk_listConv {Ca Cb S : ℕ} (hS : 2 * (Ca + Cb) < S) {a b : List ℤ}
    (ha : colsOk Ca S a = true) (hb : colsOk Cb S b = true) :
    colsOk (Ca + Cb) S (listConv a b) = true := by
  apply colsOk_of_getD
  intro m hm
  simp only [zero_add]
  by_contra hcol
  push Not at hcol
  apply hm
  by_cases hae : a = []
  · subst hae; simp [listConv]
  by_cases hbe : b = []
  · subst hbe; simp [listConv]
  by_cases hml : m < a.length + b.length - 1
  · rw [listConv_getD hae hbe hml]
    refine sum_eq_zero fun p hp => ?_
    have hp' : p ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hp)
    by_cases h1 : a.getD p 0 = 0
    · rw [h1, zero_mul]
    by_cases h2 : b.getD (m - p) 0 = 0
    · rw [h2, mul_zero]
    exfalso
    have c1 := colsOk_spec ha p h1
    have c2 := colsOk_spec hb (m - p) h2
    have hS0 : 0 < S := by omega
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp'
    rw [Nat.add_sub_cancel_left] at c2
    have hsplit : p + q = (p % S + q % S) + S * (p / S + q / S) := by
      have e1 := Nat.mod_add_div p S
      have e2 := Nat.mod_add_div q S
      rw [Nat.mul_add]; omega
    have : (p + q) % S = p % S + q % S := by
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_listConv hae hbe]; omega)]
    rfl

theorem colsOk_lcomb {C S : ℕ} : ∀ (ts : List (ℤ × List ℤ)), (∀ t ∈ ts, colsOk C S t.2 = true) →
    colsOk C S (lcomb ts) = true := by
  intro ts h
  apply colsOk_of_getD
  intro i hi
  simp only [zero_add]
  by_contra hcol
  push Not at hcol
  apply hi
  rw [getD_lcomb]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [getD_eq_zero_of_colsOk (h t ht) hcol, mul_zero]

/-! ### The weighted norm on the square layout -/

theorem abs_kc_key_le {C S i : ℕ} (hS : 2 * C < S) (hcol : i % S ≤ 2 * C)
    (hi : i < Layout.len C S) (a : Fin 2) : |kc (Layout.key C S i) a| ≤ C := by
  have hS0 : 0 < S := by omega
  have hrow : i / S ≤ 2 * C := by
    by_contra hn
    have h1 : S * (2 * C + 1) ≤ S * (i / S) := Nat.mul_le_mul_left S (by omega)
    have h2 : S * (i / S) ≤ i := Nat.mul_div_le i S
    unfold Layout.len at hi
    nlinarith
  have hcol' : ((i % S : ℕ) : ℤ) ≤ 2 * C := by exact_mod_cast hcol
  have hrow' : ((i / S : ℕ) : ℤ) ≤ 2 * C := by exact_mod_cast hrow
  have h0 : (0 : ℤ) ≤ ((i % S : ℕ) : ℤ) := Nat.cast_nonneg _
  have h0' : (0 : ℤ) ≤ ((i / S : ℕ) : ℤ) := Nat.cast_nonneg _
  unfold kc Layout.key
  split_ifs
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- `wl1 ≤ C · l1` on a zero-padded list of the square layout `C`. -/
theorem wl1_le_mul_l1 {C S : ℕ} (hS : 2 * C < S) {d : List ℤ} (hd : colsOk C S d = true)
    (hl : d.length ≤ Layout.len C S) (a : Fin 2) :
    wl1 (Layout.key C S) a d ≤ C * l1 d := by
  rw [wl1_eq, l1_eq, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.mp hi
  by_cases h0 : d.getD i 0 = 0
  · rw [h0]; simp
  · exact mul_le_mul_of_nonneg_right (abs_kc_key_le hS (colsOk_spec hd i h0) (by omega) a)
      (abs_nonneg _)

end KAM.EffectiveStability.Tube

end
