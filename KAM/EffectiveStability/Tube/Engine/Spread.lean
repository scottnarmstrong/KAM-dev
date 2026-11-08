/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Norm

/-!
# Spreading packed digits (T2-CONF, N7)

Ledger literals are stored compactly: the `n` digits of a model, each `b` bits, in one natural
number. The packed product layout needs the same digits at a wider slot width `w ≥ b`.
`pspread b w L X` re-spaces the `2^L` digits in `L` parallel rounds (`spreadRound`: one periodic
mask, one `AND`, one subtraction, one shift, one addition each), so the kernel does a few
whole-number operations and no per-digit loop over big numbers.

* `dig b X i = (X >>> (b i)) % 2^b`: digit `i` of `X` in base `2^b`;
* `pspread_eq`: for `0 < b ≤ w` and `X < 2^(b 2^L)`,
  `pspread b w L X = Σ_{i<2^L} dig b X i · 2^(w i)`; `expand_eq`: the same on the square box;
* `dig_digitSum`: the digits of `Σ_{i<n} e_i 2^(m i)` (all `e_i < 2^m`) are the `e_i`;
* `sum_range_mul_regroup`: `Σ_{i < K R} f i = Σ_{r<R} Σ_{c<K} f (c + K r)`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.CertificateSharp.Packed

/-- Digit `i` of `X` in base `2^b`. -/
def dig (b X i : ℕ) : ℕ := (X >>> (b * i)) % 2 ^ b

theorem dig_lt (b X i : ℕ) : dig b X i < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)

theorem dig_mod (b X h i : ℕ) (hi : i < h) : dig b (X % 2 ^ (b * h)) i = dig b X i := by
  unfold dig
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hj : j < b
  · have : b * i + j < b * h := by
      have : b * (i + 1) ≤ b * h := Nat.mul_le_mul_left b hi
      rw [Nat.mul_succ] at this; omega
    simp [hj, this]
  · simp [hj]

theorem dig_shift (b X h i : ℕ) : dig b (X >>> (b * h)) i = dig b X (i + h) := by
  unfold dig
  rw [← Nat.shiftRight_add, Nat.mul_add, Nat.add_comm (b * h)]

theorem dig_of_lt {b X : ℕ} (hX : X < 2 ^ b) : dig b X 0 = X := by
  simp [dig, Nat.mod_eq_of_lt hX]

/-! ### Digit sums -/

theorem natPack_eq_sum (m : ℕ) : ∀ l : List ℕ,
    natPack m l = ∑ i ∈ range l.length, l.getD i 0 * 2 ^ (m * i)
  | [] => by simp [natPack_nil]
  | e :: l => by
    rw [natPack_cons, natPack_eq_sum m l, List.length_cons,
      sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [Nat.mul_succ, pow_add]
    ring

theorem natPack_range (m n : ℕ) (e : ℕ → ℕ) :
    natPack m ((List.range n).map e) =
      ∑ i ∈ range n, e i * 2 ^ (m * i) := by
  rw [natPack_eq_sum]
  simp only [List.length_map, List.length_range]
  refine sum_congr rfl fun i hi => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hi)]
  rfl

/-- A digit sum is below `2^(m n)`. -/
theorem digitSum_lt {m n : ℕ} {e : ℕ → ℕ} (he : ∀ i < n, e i < 2 ^ m) :
    ∑ i ∈ range n, e i * 2 ^ (m * i) < 2 ^ (m * n) := by
  rw [← natPack_range]
  have := natPack_lt (w := m) (es := (List.range n).map e)
    (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact he i (List.mem_range.mp hi))
  simpa using this

/-- The digits of a digit sum. -/
theorem dig_digitSum {m n : ℕ} {e : ℕ → ℕ} (he : ∀ i < n, e i < 2 ^ m) {j : ℕ} (hj : j < n) :
    dig m (∑ i ∈ range n, e i * 2 ^ (m * i)) j = e j := by
  rw [← natPack_range]
  have := natPack_digit ((List.range n).map e) j (fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact he i (List.mem_range.mp hi))
  rw [Nat.and_two_pow_sub_one_eq_mod] at this
  rw [dig, this, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- Regroup a range of length `K R` into `R` blocks of `K`. -/
theorem sum_range_mul_regroup {M : Type*} [AddCommMonoid M] (K : ℕ) (f : ℕ → M) :
    ∀ R : ℕ, ∑ i ∈ range (K * R), f i = ∑ r ∈ range R, ∑ c ∈ range K, f (c + K * r)
  | 0 => by simp
  | R + 1 => by
    rw [Nat.mul_succ, sum_range_add, sum_range_mul_regroup K f R, sum_range_succ]
    congr 1
    exact sum_congr rfl fun c _ => by rw [Nat.add_comm]

theorem mod_pow_eq_sum (b X : ℕ) : ∀ n : ℕ,
    X % 2 ^ (b * n) = ∑ i ∈ range n, dig b X i * 2 ^ (b * i)
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [Nat.mul_succ, pow_add, Nat.mod_mul, mod_pow_eq_sum b X n, sum_range_succ]
    unfold dig
    rw [Nat.shiftRight_eq_div_pow]
    ring

theorem dig_mod_of_ge (b X h i : ℕ) (hi : h ≤ i) : dig b (X % 2 ^ (b * h)) i = 0 := by
  unfold dig
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
  · rfl
  · exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left b hi))

/-! ### The parallel spread -/

/-- One round: in each of `nb` blocks of `2m` digits (block stride `2 m w` bits, digits of `b`
bits at the bottom), move the high `m` digits up by `m (w - b)` bits. Kernel: a closed-form
periodic mask, one `AND`, one subtraction, one shift, one addition. -/
def spreadRound (b w m nb X : ℕ) : ℕ :=
  (X &&& periodic (2 * m * w) nb (2 ^ (m * b) - 1)) +
    ((X - (X &&& periodic (2 * m * w) nb (2 ^ (m * b) - 1))) <<< (m * (w - b)))

/-- `k` rounds from `nb` blocks of `2^k` digits. -/
def pspreadAux (b w : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, X => X
  | k + 1, nb, X => pspreadAux b w k (2 * nb) (spreadRound b w (2 ^ k) nb X)

/-- **The parallel spread**: re-space the `2^L` base-`2^b` digits of `X` to base `2^w` in `L`
rounds of whole-number operations. -/
def pspread (b w L X : ℕ) : ℕ := pspreadAux b w L 1 X

/-- Block `t` of `2^k` digits of the digit function `e`, at base `2^b`. -/
def blk (b : ℕ) (e : ℕ → ℕ) (k t : ℕ) : ℕ := ∑ i ∈ range (2 ^ k), e (t * 2 ^ k + i) * 2 ^ (b * i)

theorem blk_lt {b : ℕ} {e : ℕ → ℕ} (he : ∀ i, e i < 2 ^ b) (k t : ℕ) :
    blk b e k t < 2 ^ (b * 2 ^ k) :=
  digitSum_lt fun _ _ => he _

theorem blk_succ {b : ℕ} (e : ℕ → ℕ) (k t : ℕ) :
    blk b e (k + 1) t = blk b e k (2 * t) + 2 ^ (b * 2 ^ k) * blk b e k (2 * t + 1) := by
  unfold blk
  rw [pow_succ, Nat.mul_two, sum_range_add, mul_sum]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    congr 2; ring
  · refine sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, mul_comm (2 ^ (b * 2 ^ k)), mul_assoc, ← pow_add]
    congr 2
    · ring
    · ring

theorem spreadRound_eq {b w : ℕ} (hb : 0 < b) (hbw : b ≤ w) {e : ℕ → ℕ} (he : ∀ i, e i < 2 ^ b)
    (k nb : ℕ) {X : ℕ} (hX : X = ∑ t ∈ range nb, blk b e (k + 1) t * 2 ^ (2 * 2 ^ k * w * t)) :
    spreadRound b w (2 ^ k) nb X = ∑ t ∈ range (2 * nb), blk b e k t * 2 ^ (2 ^ k * w * t) := by
  set m := 2 ^ k with hm
  have hm0 : 0 < m := Nat.two_pow_pos k
  have hw : 0 < w := by omega
  have hW : 0 < 2 * m * w := by positivity
  set lo : ℕ → ℕ := fun t => blk b e k (2 * t) with hlo
  set hi : ℕ → ℕ := fun t => blk b e k (2 * t + 1) with hhi
  have hlolt : ∀ t, lo t < 2 ^ (m * b) := fun t => by
    rw [Nat.mul_comm]; exact blk_lt he k _
  have hV : ∀ t, blk b e (k + 1) t = lo t + 2 ^ (m * b) * hi t := fun t => by
    rw [blk_succ, Nat.mul_comm m b]
  have hVlt : ∀ t, blk b e (k + 1) t < 2 ^ (2 * m * w) := fun t => by
    refine (blk_lt he (k + 1) t).trans_le (Nat.pow_le_pow_right (by norm_num) ?_)
    rw [pow_succ, ← hm]; nlinarith
  -- packed forms
  set es := (List.range nb).map (blk b e (k + 1)) with hes
  have hXp : X = natPack (2 * m * w) es := by
    rw [hX, hes, natPack_range]
  have hesl : ∀ x ∈ es, x < 2 ^ (2 * m * w) := fun x hx => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx; exact hVlt t
  have hmask : periodic (2 * m * w) nb (2 ^ (m * b) - 1) =
      natPack (2 * m * w) (List.replicate es.length (2 ^ (m * b) - 1)) := by
    rw [periodic_eq_natPack hW, hes, List.length_map, List.length_range]
  have hmb : m * b ≤ 2 * m * w := by nlinarith
  have hland : X &&& periodic (2 * m * w) nb (2 ^ (m * b) - 1) =
      ∑ t ∈ range nb, lo t * 2 ^ (2 * m * w * t) := by
    rw [hXp, hmask, natPack_land_mask hmb hesl, hes, List.map_map, natPack_range]
    refine sum_congr rfl fun t _ => ?_
    simp only [Function.comp_apply]
    rw [hV, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hlolt t)]
  have hXs : X = (∑ t ∈ range nb, lo t * 2 ^ (2 * m * w * t)) +
      2 ^ (m * b) * ∑ t ∈ range nb, hi t * 2 ^ (2 * m * w * t) := by
    rw [hX, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun t _ => ?_
    rw [hV]; ring
  have hsub : X - ∑ t ∈ range nb, lo t * 2 ^ (2 * m * w * t) =
      2 ^ (m * b) * ∑ t ∈ range nb, hi t * 2 ^ (2 * m * w * t) := by
    conv_lhs => rw [hXs]
    exact Nat.add_sub_cancel_left _ _
  have hpw : ∀ Y : ℕ, 2 ^ (m * b) * Y * 2 ^ (m * (w - b)) = Y * 2 ^ (m * w) := fun Y => by
    rw [Nat.mul_comm (2 ^ (m * b)) Y, Nat.mul_assoc, ← pow_add, ← Nat.mul_add,
      Nat.add_sub_cancel' hbw]
  unfold spreadRound
  rw [hland, hsub, Nat.shiftLeft_eq, hpw, sum_mul, sum_range_mul_regroup 2 _ nb,
    ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_range_succ, sum_range_one]
  simp only [hlo, hhi, Nat.zero_add, show 1 + 2 * t = 2 * t + 1 by ring]
  rw [Nat.mul_assoc (blk b e k (2 * t + 1)), ← pow_add]
  congr 1
  · congr 2; ring
  · congr 2; ring

theorem pspreadAux_eq {b w : ℕ} (hb : 0 < b) (hbw : b ≤ w) {e : ℕ → ℕ} (he : ∀ i, e i < 2 ^ b) :
    ∀ (k nb X : ℕ), X = ∑ t ∈ range nb, blk b e k t * 2 ^ (2 ^ k * w * t) →
      pspreadAux b w k nb X = ∑ t ∈ range (nb * 2 ^ k), e t * 2 ^ (w * t)
  | 0, nb, X, hX => by
    rw [pspreadAux, hX, pow_zero, Nat.mul_one]
    refine sum_congr rfl fun t _ => ?_
    simp [blk, Nat.mul_comm w t]
  | k + 1, nb, X, hX => by
    have hX' : X = ∑ t ∈ range nb, blk b e (k + 1) t * 2 ^ (2 * 2 ^ k * w * t) := by
      rw [hX]
      refine sum_congr rfl fun t _ => ?_
      rw [pow_succ, Nat.mul_comm (2 ^ k) 2]
    rw [pspreadAux, pspreadAux_eq hb hbw he k (2 * nb) _ (spreadRound_eq hb hbw he k nb hX'),
      show 2 * nb * 2 ^ k = nb * 2 ^ (k + 1) by rw [pow_succ]; ring]

/-- **The parallel spread is digit re-spacing.** -/
theorem pspread_eq {b w L X : ℕ} (hb : 0 < b) (hbw : b ≤ w) (hX : X < 2 ^ (b * 2 ^ L)) :
    pspread b w L X = ∑ i ∈ range (2 ^ L), dig b X i * 2 ^ (w * i) := by
  unfold pspread
  rw [pspreadAux_eq hb hbw (dig_lt b X) L 1 X (by
    rw [sum_range_one, Nat.mul_zero, pow_zero, Nat.mul_one]
    unfold blk
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [← mod_pow_eq_sum, Nat.mod_eq_of_lt hX]), Nat.one_mul]

/-! ### Expansion of a compact square-box literal -/

/-- Expand the `(2C+1)²` compact digits of `X` (base `2^b`, row-major) to the packed layout of
half-width `C`, row stride `S` and slot width `w`: digit `c + (2C+1) r` goes to slot `c + S r`.
Two parallel spreads (`L₁` rounds over the digits, `(2C+1)² ≤ 2^L₁`; `L₂` rounds over the rows,
`2C+1 ≤ 2^L₂`). -/
def expand (C S b w L₁ L₂ X : ℕ) : ℕ :=
  pspread ((2 * C + 1) * w) (S * w) L₂
    (pspread b w L₁ (X &&& (2 ^ (b * ((2 * C + 1) * (2 * C + 1))) - 1)))

theorem expand_eq {C S b w L₁ L₂ X : ℕ} (hb : 0 < b) (hbw : b ≤ w) (hKS : 2 * C + 1 ≤ S)
    (hL₁ : (2 * C + 1) * (2 * C + 1) ≤ 2 ^ L₁) (hL₂ : 2 * C + 1 ≤ 2 ^ L₂) :
    expand C S b w L₁ L₂ X = ∑ r ∈ range (2 * C + 1), ∑ c ∈ range (2 * C + 1),
      dig b X (c + (2 * C + 1) * r) * 2 ^ (w * (c + S * r)) := by
  set K := 2 * C + 1 with hK
  have hw : 0 < w := by omega
  have hmask : X &&& (2 ^ (b * (K * K)) - 1) = X % 2 ^ (b * (K * K)) :=
    Nat.and_two_pow_sub_one_eq_mod X _
  have hX' : X % 2 ^ (b * (K * K)) < 2 ^ (b * 2 ^ L₁) :=
    (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left b hL₁))
  have hdlt : ∀ i, dig b X i < 2 ^ w := fun i =>
    (dig_lt b X i).trans_le (Nat.pow_le_pow_right (by norm_num) hbw)
  -- the digit spread, cut to the `K²` real digits
  have hin : pspread b w L₁ (X % 2 ^ (b * (K * K))) =
      ∑ r ∈ range K, (∑ c ∈ range K, dig b X (c + K * r) * 2 ^ (w * c)) * 2 ^ ((K * w) * r) := by
    rw [pspread_eq hb hbw hX']
    rw [← sum_subset (range_subset_range.mpr hL₁) (fun i _ hi => by
      rw [dig_mod_of_ge b X _ i (by simpa using hi), zero_mul])]
    rw [sum_range_mul_regroup K _ K]
    refine sum_congr rfl fun r hr => ?_
    rw [sum_mul]
    refine sum_congr rfl fun c hc => ?_
    have hidx : c + K * r < K * K := by
      have := mem_range.mp hr; have := mem_range.mp hc; nlinarith
    rw [dig_mod b X _ _ hidx, mul_assoc, ← pow_add]
    congr 2
    ring
  have hrow : ∀ r, ∑ c ∈ range K, dig b X (c + K * r) * 2 ^ (w * c) < 2 ^ (K * w) := fun r => by
    rw [Nat.mul_comm K w]
    exact digitSum_lt fun i _ => hdlt _
  have hYlt : ∑ r ∈ range K, (∑ c ∈ range K, dig b X (c + K * r) * 2 ^ (w * c)) *
      2 ^ ((K * w) * r) < 2 ^ ((K * w) * 2 ^ L₂) :=
    (digitSum_lt fun i _ => hrow i).trans_le
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hL₂))
  unfold expand
  rw [← hK, hmask, hin, pspread_eq (by positivity) (Nat.mul_le_mul_right w hKS) hYlt]
  rw [← sum_subset (range_subset_range.mpr hL₂) (fun i _ hi => by
    rw [dig, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt, Nat.zero_mod, zero_mul]
    exact (digitSum_lt fun i _ => hrow i).trans_le
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by simpa using hi))))]
  refine sum_congr rfl fun r hr => ?_
  rw [dig_digitSum (fun i _ => hrow i) (mem_range.mp hr), sum_mul]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_assoc, ← pow_add]
  congr 2
  ring

end KAM.EffectiveStability.Tube

end
