/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Packed.Digits

/-!
# Advice-free rounding, the load check and balanced unpacking of packed slots

For a signed packed integer `Z = packSum w d` (`N` slots of width `w`):

* `gmpRound w N l s Z` rounds every slot to the nearest multiple of `2^s` (ties up) with four
  big-integer operations and no advice: add the offset `2^l + 2^(s-1)` to every slot, clear the
  low `s` bits of every digit by a periodic mask, shift right by `s`, remove the offset
  `2^(l-s)`. `gmpRound_spec`: when every slot satisfies `|d_i| ≤ 2^l`, `1 ≤ s ≤ l` and
  `l + 2 ≤ w`, the result packs `r_i = ⌊(d_i + 2^(s-1)) / 2^s⌋`, and `|d_i - 2^s r_i| ≤ 2^(s-1)`
  (`round_err`).
* `loadOk w N l Z` certifies with one mask that `Z` packs `N` slots in `[-2^l, 2^l)`
  (`loadOk_sound`).
* `unpackSlots w N Z` reads the `N` signed slots by balanced mask/shift halving (`natDigitsSh`),
  and inverts `packSum` on slots with `2|d_i| < 2^w` (`unpackSlots_packSum`);
* `natJoin` joins the chunks of a large packed literal (a balanced tree, written by the producer).
-/

@[expose] public section

namespace KAM.Certificate

/-! ### Rounding by mask and shift -/

/-- Clear the low `s` bits of each of the `N` digits of `Y` and shift right by `s`: every digit is
divided by `2^s` (`natPack_clear_shift`). Kernel: one mask, one subtraction, one shift. -/
def digitShift (w N s Y : ℕ) : ℕ := (Y - (Y &&& periodic w N (2 ^ s - 1))) >>> s

/-- **Advice-free rounding** of every slot of `Z` to the nearest multiple of `2^s` (ties up), the
slots being within `2^l` (`gmpRound_spec`): offset digits, `digitShift`, offset removed. -/
def gmpRound (w N l s : ℕ) (Z : ℤ) : ℤ :=
  (digitShift w N s (Z + (periodic w N (2 ^ l + 2 ^ (s - 1)) : ℤ)).toNat : ℤ) -
    (periodic w N (2 ^ (l - s)) : ℤ)

/-- The rounded slot `⌊(d + 2^(s-1)) / 2^s⌋`. -/
def roundSlot (s : ℕ) (d : ℤ) : ℤ := (d + 2 ^ (s - 1)) / 2 ^ s

/-- Round to nearest: the error is at most `2^(s-1)`. -/
theorem round_err {s : ℕ} (hs : 1 ≤ s) (d : ℤ) : |d - 2 ^ s * roundSlot s d| ≤ 2 ^ (s - 1) := by
  have h2 : (2 : ℤ) ^ s = 2 * 2 ^ (s - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hs]
  have hpos : (0 : ℤ) < 2 ^ s := by positivity
  have hdiv := Int.mul_ediv_add_emod (d + 2 ^ (s - 1)) (2 ^ s)
  have hm0 := Int.emod_nonneg (d + 2 ^ (s - 1)) hpos.ne'
  have hm1 := Int.emod_lt_of_pos (d + 2 ^ (s - 1)) hpos
  unfold roundSlot
  rw [abs_le]
  constructor <;> linarith

/-- The rounded slot stays within `2^l` when the slot does (`1 ≤ s`). -/
theorem roundSlot_abs_le {s l : ℕ} (hs : 1 ≤ s) {d : ℤ} (hd : |d| ≤ 2 ^ l) :
    |roundSlot s d| ≤ 2 ^ l := by
  have he := round_err hs d
  have h2 : (2 : ℤ) ^ s = 2 * 2 ^ (s - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hs]
  have hp : (0 : ℤ) < 2 ^ (s - 1) := by positivity
  have hl : (0 : ℤ) < 2 ^ l := by positivity
  have hle : (1 : ℤ) ≤ 2 ^ (s - 1) := one_le_pow₀ (by norm_num)
  rw [abs_le] at he hd ⊢
  set r := roundSlot s d
  constructor <;> nlinarith

/-- **Rounding by mask and shift is exact round-to-nearest on every slot.** -/
theorem gmpRound_spec {w N l s : ℕ} (hs : 1 ≤ s) (hsl : s ≤ l) (hlw : l + 2 ≤ w) {cs : List ℤ}
    (hN : cs.length = N) (hB : ∀ c ∈ cs, |c| ≤ 2 ^ l) :
    gmpRound w N l s (packSum w cs) = packSum w (cs.map (roundSlot s)) := by
  have hw : 0 < w := by omega
  subst hN
  set O : ℕ := 2 ^ l + 2 ^ (s - 1) with hO
  have hA : (2 : ℤ) ^ (s - 1) < 2 ^ l := pow_lt_pow_right₀ (by norm_num) (by omega)
  have h4 : (4 : ℤ) * 2 ^ l ≤ 2 ^ w := by
    calc (4 : ℤ) * 2 ^ l = 2 ^ (l + 2) := by ring
      _ ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) hlw
  -- the offset digits
  have hnn : ∀ c ∈ cs, 0 ≤ c + (O : ℤ) := fun c hc => by
    have := (abs_le.mp (hB c hc)).1
    have : (0 : ℤ) ≤ 2 ^ (s - 1) := by positivity
    push_cast [hO]; linarith
  set es := cs.map fun c : ℤ => (c + (O : ℤ)).toNat with hes
  have hdig : ∀ e ∈ es, e < 2 ^ w := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    have h1 := (abs_le.mp (hB c hc)).2
    have h0 := hnn c hc
    have : ((c + (O : ℤ)).toNat : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]
      push_cast [hO]
      linarith
    exact_mod_cast this
  have hY : (packSum w cs + (periodic w cs.length O : ℤ)).toNat = natPack w es := by
    rw [periodic_cast hw, packSum_add_periodic w O cs hnn, Int.toNat_natCast]
  have hlen : es.length = cs.length := by simp [hes]
  have hshift : digitShift w cs.length s (natPack w es) = natPack w (es.map (· / 2 ^ s)) := by
    unfold digitShift
    rw [periodic_eq_natPack hw, ← hlen]
    exact natPack_clear_shift (by omega) hdig
  -- each quotient is the rounded slot plus `2^(l-s)`
  have hq : ∀ c ∈ cs, ((((c + (O : ℤ)).toNat / 2 ^ s : ℕ)) : ℤ) =
      roundSlot s c + ((2 ^ (l - s) : ℕ) : ℤ) := by
    intro c hc
    rw [Int.natCast_ediv, Int.toNat_of_nonneg (hnn c hc), roundSlot]
    have hsplit : c + (O : ℤ) = (c + 2 ^ (s - 1)) + ((2 ^ (l - s) : ℕ) : ℤ) * 2 ^ s := by
      push_cast [hO]
      rw [← pow_add, Nat.sub_add_cancel hsl]
      ring
    rw [hsplit]
    push_cast
    exact Int.add_mul_ediv_right _ _ (by positivity)
  unfold gmpRound
  rw [hY, hshift, natPack_cast, List.map_map, periodic_cast hw]
  have hmap : (es.map (· / 2 ^ s)).map (Nat.cast : ℕ → ℤ) =
      (cs.map (roundSlot s)).map fun r => r + ((2 ^ (l - s) : ℕ) : ℤ) := by
    rw [hes, List.map_map, List.map_map, List.map_map]
    exact List.map_congr_left fun c hc => hq c hc
  rw [← List.map_map, hmap]
  have := packSum_map_sub w ((2 ^ (l - s) : ℕ) : ℤ)
    ((cs.map (roundSlot s)).map fun r => r + ((2 ^ (l - s) : ℕ) : ℤ))
  rw [List.map_map] at this
  simp only [Function.comp_def, add_sub_cancel_right, List.length_map, List.map_id'] at this
  rw [this]

/-! ### The load check -/

/-- **Load check**: `Z` packs `N` slots in `[-2^l, 2^l)`, by one mask on the offset digits
(`loadOk_sound`). Kernel: one addition, one comparison, one mask, one equality. -/
def loadOk (w N l : ℕ) (Z : ℤ) : Bool :=
  decide (0 < w) && decide (l + 1 ≤ w) && decide (0 ≤ Z + (periodic w N (2 ^ l) : ℤ)) &&
    decide ((Z + (periodic w N (2 ^ l) : ℤ)).toNat < 2 ^ (w * N)) &&
    ((Z + (periodic w N (2 ^ l) : ℤ)).toNat &&& periodic w N (2 ^ (l + 1) - 1) ==
      (Z + (periodic w N (2 ^ l) : ℤ)).toNat)

theorem loadOk_sound {w N l : ℕ} {Z : ℤ} (h : loadOk w N l Z = true) :
    ∃ cs : List ℤ, cs.length = N ∧ (∀ c ∈ cs, -2 ^ l ≤ c ∧ c < 2 ^ l) ∧ packSum w cs = Z := by
  simp only [loadOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hw, hlw⟩, h0⟩, hlt⟩, hmask⟩ := h
  set Y := (Z + (periodic w N (2 ^ l) : ℤ)).toNat with hYdef
  obtain ⟨es, hl, hd, hX⟩ := natPack_digits w N Y hlt
  rw [← hX, periodic_eq_natPack hw, ← hl, natPack_land_mask hlw hd] at hmask
  have hmod := natPack_injective (fun e he => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
      exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by norm_num) hlw)) hd (by simp) hmask
  have hsmall : ∀ e ∈ es, e < 2 ^ (l + 1) := fun e he => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i < (es.map (· % 2 ^ (l + 1))).length := by simpa using hi
    have := List.getElem_of_eq hmod hi'
    simp only [List.getElem_map] at this
    rw [← this]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  refine ⟨es.map fun e : ℕ => (e : ℤ) - 2 ^ l, by simp [hl], fun c hc => ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    have := hsmall e he
    have h2 : ((e : ℕ) : ℤ) < ((2 ^ (l + 1) : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h2
    constructor
    · have : (0 : ℤ) ≤ e := by positivity
      linarith
    · rw [pow_succ] at h2; linarith
  · have hsub := packSum_map_sub w (2 ^ l) (es.map (Nat.cast : ℕ → ℤ))
    rw [List.map_map] at hsub
    simp only [Function.comp_def] at hsub
    rw [hsub, ← natPack_cast, hX, List.length_map, hl]
    have hp := periodic_cast hw N (2 ^ l)
    push_cast at hp
    rw [← hp, hYdef, Int.toNat_of_nonneg h0]
    ring

/-! ### Literal ingestion -/

/-- Join two chunks of a packed literal: `a + b · 2^k` (kernel: one shift and one addition).
Large packed literals are written as balanced trees of `natJoin` over short hexadecimal chunks:
the elaborator's numeral parser is quadratic in the digit count, and source lines are short. -/
def natJoin (k a b : ℕ) : ℕ := a + (b <<< k)

/-! ### Balanced unpacking -/

/-- Digit-by-digit reading of `N` base-`2^w` digits (low mask, then shift). -/
def natDigitsLin (w : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | N + 1, Y => (Y &&& (2 ^ w - 1)) :: natDigitsLin w N (Y >>> w)

/-- Balanced reading of `N` digits: split in halves by mask and shift (`fuel` levels), then digit
by digit; every intermediate integer is only as wide as the slots it covers. -/
def natDigitsSh (w : ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, N, Y => natDigitsLin w N Y
  | f + 1, N, Y =>
    if N ≤ 16 then natDigitsLin w N Y else
      natDigitsSh w f (N / 2) (Y &&& (2 ^ (w * (N / 2)) - 1)) ++
        natDigitsSh w f (N - N / 2) (Y >>> (w * (N / 2)))

theorem natPack_append (w : ℕ) : ∀ es fs : List ℕ,
    natPack w (es ++ fs) = natPack w es + 2 ^ (w * es.length) * natPack w fs
  | [], fs => by simp [natPack_nil]
  | e :: es, fs => by
    rw [List.cons_append, natPack_cons, natPack_cons, natPack_append w es fs, List.length_cons,
      Nat.mul_succ, pow_add]
    ring

theorem natDigitsLin_natPack (w : ℕ) : ∀ es : List ℕ, (∀ e ∈ es, e < 2 ^ w) →
    natDigitsLin w es.length (natPack w es) = es
  | [], _ => rfl
  | e :: es, h => by
    have he := h e (by simp)
    rw [List.length_cons, natDigitsLin, natPack_cons, Nat.and_two_pow_sub_one_eq_mod,
      Nat.shiftRight_eq_div_pow, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt he, Nat.zero_add,
      natDigitsLin_natPack w es fun x hx => h x (by simp [hx])]

theorem natDigitsSh_natPack (w : ℕ) : ∀ (f : ℕ) (es : List ℕ), (∀ e ∈ es, e < 2 ^ w) →
    natDigitsSh w f es.length (natPack w es) = es
  | 0, es, h => natDigitsLin_natPack w es h
  | f + 1, es, h => by
    rw [natDigitsSh]
    split_ifs with h16
    · exact natDigitsLin_natPack w es h
    · set k := es.length / 2 with hk
      have hk' : k ≤ es.length := Nat.div_le_self _ _
      have hsplit := List.take_append_drop k es
      have h1 : ∀ e ∈ es.take k, e < 2 ^ w := fun e he => h e (List.mem_of_mem_take he)
      have h2 : ∀ e ∈ es.drop k, e < 2 ^ w := fun e he => h e (List.mem_of_mem_drop he)
      have hl1 : (es.take k).length = k := List.length_take_of_le hk'
      have hl2 : (es.drop k).length = es.length - k := List.length_drop
      have hval : natPack w es = natPack w (es.take k) + 2 ^ (w * k) * natPack w (es.drop k) := by
        conv_lhs => rw [← hsplit]
        rw [natPack_append, hl1]
      have hlt := natPack_lt h1
      rw [hl1] at hlt
      rw [hval, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt,
        Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]
      have e1 := natDigitsSh_natPack w f (es.take k) h1
      have e2 := natDigitsSh_natPack w f (es.drop k) h2
      rw [hl1] at e1
      rw [hl2] at e2
      rw [e1, e2, hsplit]

/-- The `N` signed slots of `Z` at width `w`, read on the offset natural `Z + Σ 2^(w-1) 2^(w i)`
by balanced halving (`64` levels; the digit loop keeps it exact for any length). -/
def unpackSlots (w N : ℕ) (Z : ℤ) : List ℤ :=
  (natDigitsSh w 64 N (Z + (periodic w N (2 ^ (w - 1)) : ℤ)).toNat).map
    fun e : ℕ => (e : ℤ) - 2 ^ (w - 1)

/-- **Unpacking inverts packing** on slots with `2|d_i| < 2^w`. -/
theorem unpackSlots_packSum {w : ℕ} (hw : 0 < w) {cs : List ℤ} (hc : SlotsBounded w cs) :
    unpackSlots w cs.length (packSum w cs) = cs := by
  have h2 : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hw]
  have hnn : ∀ c ∈ cs, 0 ≤ c + ((2 ^ (w - 1) : ℕ) : ℤ) := fun c hc' => by
    have := hc c hc'
    push_cast
    have : -c ≤ |c| := neg_le_abs c
    linarith
  have hdig : ∀ e ∈ cs.map fun c : ℤ => (c + ((2 ^ (w - 1) : ℕ) : ℤ)).toNat, e < 2 ^ w := by
    intro e he
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp he
    have hb := hc c hcm
    have : ((c + ((2 ^ (w - 1) : ℕ) : ℤ)).toNat : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (hnn c hcm)]
      push_cast
      have : c ≤ |c| := le_abs_self c
      linarith
    exact_mod_cast this
  unfold unpackSlots
  rw [periodic_cast hw, packSum_add_periodic w _ cs hnn, Int.toNat_natCast]
  have hlen : (cs.map fun c : ℤ => (c + ((2 ^ (w - 1) : ℕ) : ℤ)).toNat).length = cs.length := by
    simp
  conv_lhs => rw [← hlen]
  rw [natDigitsSh_natPack w 64 _ hdig, List.map_map]
  conv_rhs => rw [← List.map_id cs]
  refine List.map_congr_left fun c hcm => ?_
  simp only [Function.comp_apply, id, Int.toNat_of_nonneg (hnn c hcm)]
  push_cast
  ring

end KAM.Certificate
