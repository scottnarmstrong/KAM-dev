/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Spread
public import KAM.EffectiveStability.Tube.Trig.Product

/-!
# Compact literal models (T2-CONF, N7)

A ledger model of half-width `C` is stored as `(2C+1)²` offset digits of `b` bits (row-major over the
square box `|k_i| ≤ C`, digit value `mantissa + 2^(b-1)`) in one natural number `X` (the unwhitened
literal). Its slot list on the square layout of stride `S` (`Layout.key C S`) is `litList C S b X`:
slot `c + S r` (`c, r ≤ 2C`) holds `dig b X (c + (2C+1) r) - 2^(b-1)`, the padding columns hold `0`.

* `litZ_eq`: the kernel's packed value `litZ` (two `spread`s, one closed-form offset) is
  `packSum w (litList C S b X)`;
* `colsOk_litList`, `length_litList`, `abs_litList_lt` (every slot in `[-2^(b-1), 2^(b-1))`);
* `symDigOk q C b X` (decode the compact digits once and compare with their reversal) implies
  `symOk q (litList C S b X)`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- Slot `i` of the literal model: a compact digit minus the offset on valid columns, else `0`. -/
def litSlot (C S b X i : ℕ) : ℤ :=
  if i % S < 2 * C + 1 then (dig b X (i % S + (2 * C + 1) * (i / S)) : ℤ) - 2 ^ (b - 1) else 0

/-- The slot list of a literal model on the square layout `(C, S)`. -/
def litList (C S b X : ℕ) : List ℤ := (List.range (Layout.len C S)).map (litSlot C S b X)

/-- The packed offset `Σ_{r,c ≤ 2C} 2^(b-1) 2^(w (c + S r))` in closed form. -/
def litOff (C S b w : ℕ) : ℕ := 2 ^ (b - 1) * (periodic w (2 * C + 1) 1 * periodic (S * w) (2 * C + 1) 1)

/-- The packed value of a literal model (kernel form). -/
def litZ (C S b w L₁ L₂ X : ℕ) : ℤ := (expand C S b w L₁ L₂ X : ℤ) - (litOff C S b w : ℤ)

theorem length_litList (C S b X : ℕ) : (litList C S b X).length = Layout.len C S := by
  simp [litList]

theorem getD_litList (C S b X i : ℕ) :
    (litList C S b X).getD i 0 = if i < Layout.len C S then litSlot C S b X i else 0 := by
  unfold litList
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]; rfl

theorem periodic_one_eq_sum {w : ℕ} (hw : 0 < w) (N : ℕ) :
    periodic w N 1 = ∑ i ∈ range N, 2 ^ (w * i) := by
  rw [periodic_eq_natPack hw, natPack_eq_sum, List.length_replicate]
  refine sum_congr rfl fun i hi => ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, mem_range.mp hi]

theorem colsOk_of_getD {C S : ℕ} : ∀ {i₀ : ℕ} {d : List ℤ},
    (∀ i, d.getD i 0 ≠ 0 → (i₀ + i) % S ≤ 2 * C) → colsOkAux C S i₀ d = true
  | _, [], _ => rfl
  | i₀, c :: l, h => by
    simp only [colsOkAux, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨?_, colsOk_of_getD fun i hi => ?_⟩
    · by_cases hc : c = 0
      · left; exact hc
      · right; simpa using h 0 (by simpa using hc)
    · have := h (i + 1) (by simpa using hi)
      rwa [show i₀ + (i + 1) = i₀ + 1 + i by omega] at this

theorem colsOk_litList (C S b X : ℕ) : colsOk C S (litList C S b X) = true := by
  apply colsOk_of_getD
  intro i hi
  rw [getD_litList] at hi
  simp only [zero_add]
  unfold litSlot at hi
  split_ifs at hi with h1 h2
  · omega
  · exact absurd rfl hi
  · exact absurd rfl hi

theorem abs_litList_lt {C S b X : ℕ} (hb : 1 ≤ b) :
    ∀ c ∈ litList C S b X, -2 ^ (b - 1) ≤ c ∧ c < 2 ^ (b - 1) := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
  unfold litSlot
  have h2 : (2 : ℤ) ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hb]
  have hp : (0 : ℤ) < 2 ^ (b - 1) := by positivity
  split_ifs
  · have h1 := dig_lt b X (i % S + (2 * C + 1) * (i / S))
    have h3 : (dig b X (i % S + (2 * C + 1) * (i / S)) : ℤ) < 2 ^ b := by exact_mod_cast h1
    have h4 : (0 : ℤ) ≤ dig b X (i % S + (2 * C + 1) * (i / S)) := Nat.cast_nonneg _
    constructor <;> linarith
  · constructor <;> linarith

/-! ### The packed value -/

/-- Index arithmetic of the square layout: `c + S r` has column `c` and row `r`. -/
theorem mod_div_of_lt {S c r : ℕ} (hc : c < S) : (c + S * r) % S = c ∧ (c + S * r) / S = r := by
  have hS : 0 < S := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · rw [Nat.add_mul_div_left _ _ hS, Nat.div_eq_of_lt hc, zero_add]

/-- **The packed value of a literal model** is the packing of its slot list. -/
theorem litZ_eq {C S b w L₁ L₂ X : ℕ} (hb : 0 < b) (hbw : b ≤ w) (hKS : 2 * C + 1 ≤ S)
    (hL₁ : (2 * C + 1) * (2 * C + 1) ≤ 2 ^ L₁) (hL₂ : 2 * C + 1 ≤ 2 ^ L₂) :
    litZ C S b w L₁ L₂ X = packSum w (litList C S b X) := by
  have hw : 0 < w := by omega
  set K := 2 * C + 1 with hK
  have hS : 0 < S := by omega
  have hlen : Layout.len C S ≤ S * K := by unfold Layout.len; rw [hK]; nlinarith
  rw [packSum_eq_sum, length_litList]
  -- extend to `S K` slots, regroup by rows, keep the valid columns
  have hext : ∑ i ∈ range (Layout.len C S), (litList C S b X).getD i 0 * (2 ^ w) ^ i =
      ∑ i ∈ range (S * K), (litList C S b X).getD i 0 * (2 ^ w) ^ i := by
    refine sum_subset (range_subset_range.mpr hlen) fun i _ hi => ?_
    rw [getD_litList, if_neg (by simpa using hi), zero_mul]
  rw [hext, sum_range_mul_regroup S _ K]
  have hrow : ∀ r ∈ range K, ∑ c ∈ range S, (litList C S b X).getD (c + S * r) 0 *
      (2 ^ w) ^ (c + S * r) = ∑ c ∈ range K, ((dig b X (c + K * r) : ℤ) - 2 ^ (b - 1)) *
        2 ^ (w * (c + S * r)) := by
    intro r hr
    have hr' := mem_range.mp hr
    symm
    refine sum_subset_zero_on_sdiff (range_subset_range.mpr hKS) (fun c hc => ?_)
      (fun c hc => ?_)
    · rw [mem_sdiff, mem_range, mem_range] at hc
      rw [getD_litList]
      split_ifs
      · unfold litSlot
        rw [(mod_div_of_lt hc.1).1, if_neg (by omega), zero_mul]
      · rw [zero_mul]
    · have hcK := mem_range.mp hc
      have hlt : c + S * r < Layout.len C S := by
        unfold Layout.len
        have : S * r ≤ S * (2 * C) := Nat.mul_le_mul_left S (by omega)
        nlinarith
      rw [getD_litList, if_pos hlt]
      unfold litSlot
      rw [(mod_div_of_lt (by omega)).1, (mod_div_of_lt (by omega)).2, if_pos hcK, ← pow_mul]
  have hoff : ((litOff C S b w : ℕ) : ℤ) =
      ∑ r ∈ range K, ∑ c ∈ range K, (2 : ℤ) ^ (b - 1) * 2 ^ (w * (c + S * r)) := by
    rw [litOff, periodic_one_eq_sum hw, periodic_one_eq_sum (Nat.mul_pos hS hw), sum_mul_sum,
      sum_comm]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [← pow_add]
    congr 2
    ring
  have hexp : ((expand C S b w L₁ L₂ X : ℕ) : ℤ) =
      ∑ r ∈ range K, ∑ c ∈ range K, (dig b X (c + K * r) : ℤ) * 2 ^ (w * (c + S * r)) := by
    rw [expand_eq hb hbw hKS hL₁ hL₂]
    push_cast
    rfl
  rw [sum_congr rfl hrow, litZ, hexp, hoff, ← sum_sub_distrib]
  refine sum_congr rfl fun r _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun c _ => ?_
  ring

/-! ### Symmetry from the compact digits -/

/-- The compact digits of a literal (kernel decode, balanced). -/
def compactDigits (C b X : ℕ) : List ℕ :=
  natDigitsSh b 64 ((2 * C + 1) * (2 * C + 1)) (X % 2 ^ (b * ((2 * C + 1) * (2 * C + 1))))

/-- The symmetry check of parity `q` on the compact digits: the reversed digits are the digits
(even) or their reflections `2^b - d` (odd). -/
def symDigOk (q : Bool) (C b X : ℕ) : Bool :=
  (compactDigits C b X).reverse ==
    (if q then (compactDigits C b X).map (fun d => 2 ^ b - d) else compactDigits C b X)

theorem compactDigits_eq (C b X : ℕ) :
    compactDigits C b X = (List.range ((2 * C + 1) * (2 * C + 1))).map (dig b X) := by
  unfold compactDigits
  have h := natDigitsSh_natPack b 64 ((List.range ((2 * C + 1) * (2 * C + 1))).map (dig b X))
    (fun e he => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp he; exact dig_lt b X i)
  rw [List.length_map, List.length_range, natPack_range, ← mod_pow_eq_sum] at h
  exact h

theorem symDigOk_spec {q : Bool} {C b X : ℕ} (h : symDigOk q C b X = true) {j : ℕ}
    (hj : j < (2 * C + 1) * (2 * C + 1)) :
    dig b X ((2 * C + 1) * (2 * C + 1) - 1 - j) = if q then 2 ^ b - dig b X j else dig b X j := by
  have h' := beq_iff_eq.mp h
  rw [compactDigits_eq] at h'
  have := congrArg (fun l => l.getD j 0) h'
  rw [List.getD_reverse j (by simpa using hj), List.length_map, List.length_range,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)] at this
  cases q
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj] using this
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj] using this

/-- **Symmetry of a literal model from its compact digits.** -/
theorem symOk_litList {q : Bool} {C S b X : ℕ} (hb : 1 ≤ b) (hKS : 2 * C + 1 ≤ S)
    (h : symDigOk q C b X = true) : symOk q (litList C S b X) = true := by
  set K := 2 * C + 1 with hK
  have hS : 0 < S := by omega
  have ho : (2 : ℤ) ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ', Nat.sub_add_cancel hb]
  -- the slotwise statement
  have key : ∀ i < Layout.len C S, litSlot C S b X (Layout.len C S - 1 - i) =
      psgn q * litSlot C S b X i := by
    intro i hi
    set c := i % S with hc
    set r := i / S with hr
    have hcr : c + S * r = i := Nat.mod_add_div i S
    have hcS : c < S := Nat.mod_lt _ hS
    have hlenE : Layout.len C S = 2 * C + S * (2 * C) + 1 := by unfold Layout.len; ring
    by_cases hcK : c < K
    · have hr2 : r ≤ 2 * C := by
        by_contra hn
        have : S * (2 * C + 1) ≤ S * r := Nat.mul_le_mul_left S (by omega)
        nlinarith
      have hY : S * (2 * C - r) = S * (2 * C) - S * r := Nat.mul_sub S (2 * C) r
      have hYle : S * r ≤ S * (2 * C) := Nat.mul_le_mul_left S hr2
      have hrefl : Layout.len C S - 1 - i = (2 * C - c) + S * (2 * C - r) := by
        rw [hlenE, hY]; omega
      have hjlt : c + K * r < K * K := by
        have : K * r ≤ K * (2 * C) := Nat.mul_le_mul_left K hr2
        nlinarith
      have hKr : K * (2 * C - r) = K * (2 * C) - K * r := Nat.mul_sub K (2 * C) r
      have hKrle : K * r ≤ K * (2 * C) := Nat.mul_le_mul_left K hr2
      have hjrefl : K * K - 1 - (c + K * r) = (2 * C - c) + K * (2 * C - r) := by
        have : K * K = 2 * C + K * (2 * C) + 1 := by rw [hK]; ring
        rw [this, hKr]; omega
      have hds := symDigOk_spec h hjlt
      rw [hjrefl] at hds
      unfold litSlot
      rw [hrefl, (mod_div_of_lt (by omega)).1, (mod_div_of_lt (by omega)).2, ← hc, ← hr,
        if_pos (by omega), if_pos hcK]
      cases q
      · simp only [Bool.false_eq_true, ↓reduceIte] at hds
        rw [hds]; simp [psgn, hK]
      · simp only [↓reduceIte] at hds
        have hd := dig_lt b X (c + K * r)
        rw [hds, Nat.cast_sub hd.le]
        simp only [psgn, ↓reduceIte]
        push_cast
        rw [ho]; ring
    · -- a padding column reflects to a padding column
      have hr2 : r < 2 * C := by
        by_contra hn
        have : S * (2 * C) ≤ S * r := Nat.mul_le_mul_left S (by omega)
        nlinarith
      have hY : S * (2 * C - r - 1) = S * (2 * C) - S * r - S := by
        rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_one]
      have hYle : S * r + S ≤ S * (2 * C) := by
        have : S * (r + 1) ≤ S * (2 * C) := Nat.mul_le_mul_left S (by omega)
        nlinarith
      have hrefl : Layout.len C S - 1 - i = (S + 2 * C - c) + S * (2 * C - r - 1) := by
        rw [hlenE, hY]; omega
      unfold litSlot
      rw [hrefl, (mod_div_of_lt (by omega)).1, if_neg (by omega), if_neg hcK, mul_zero]
  -- lift to the lists
  have hlen := length_litList C S b X
  unfold symOk
  apply beq_iff_eq.mpr
  apply List.ext_getElem
  · cases q <;> simp [hlen]
  · intro i h1 h2
    have hi : i < Layout.len C S := by simpa [hlen] using h1
    rw [List.getElem_reverse]
    simp only [litList, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    rw [key i hi]
    cases q <;> simp [psgn, litList]

end KAM.EffectiveStability.Tube

end
