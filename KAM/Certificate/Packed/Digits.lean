/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.Packed

/-!
# Digit-wise mask arithmetic on base-`2^w` naturals

A natural number `natPack w e = Σ_i e_i 2^{w i}` with digits `e_i < 2^w` is a packed array of
nonnegative slots. This module proves the digit-wise facts that let the kernel operate on every slot
of such a number with a constant number of big-integer operations (`Nat.land`, `Nat.shiftRight`,
`Nat.sub`, all GMP-accelerated in the kernel), never walking the slots:

* `periodic w N m = m · (2^{wN} - 1)/(2^w - 1)` is the constant `Σ_{i<N} m 2^{w i}` in closed form
  (`periodic_eq_natPack`, `periodic_cast`);
* a mask with every digit `2^t - 1` reduces every digit modulo `2^t` (`natPack_land_mask`);
* clearing the low `t` bits of every digit and shifting divides every digit by `2^t`
  (`natPack_clear_shift`);
* packing is injective on digits below `2^w` (`natPack_injective`), and every natural below
  `2^{wN}` has its `N` digits (`natPack_digits`);
* the signed packing `packSum` plus an offset per slot is the natural packing of the shifted slots
  (`packSum_add_periodic`).
-/

@[expose] public section

namespace KAM.Certificate

/-- Natural-number Kronecker packing of digits: `Σ_i e_i 2^{w i}`. -/
def natPack (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | e :: es => e + 2 ^ w * natPack w es

/-- The periodic constant `Σ_{i<N} m 2^{w i}` in closed form: one power, one subtraction, one
division and one multiplication (kernel GMP; no loop over the slots). -/
def periodic (w N m : ℕ) : ℕ := m * ((2 ^ (w * N) - 1) / (2 ^ w - 1))

theorem natPack_nil (w : ℕ) : natPack w [] = 0 := rfl

theorem natPack_cons (w e : ℕ) (es : List ℕ) : natPack w (e :: es) = e + 2 ^ w * natPack w es :=
  rfl

/-- The natural packing is the signed packing of the cast digits. -/
theorem natPack_cast (w : ℕ) : ∀ es : List ℕ, (natPack w es : ℤ) = packSum w (es.map (↑))
  | [] => by simp [natPack_nil, packSum_nil]
  | e :: es => by
    rw [natPack_cons, List.map_cons, packSum_cons, ← natPack_cast w es]
    push_cast
    ring

/-- The closed form of the periodic constant. -/
theorem periodic_cast {w : ℕ} (hw : 0 < w) (N m : ℕ) :
    (periodic w N m : ℤ) = packSum w (List.replicate N (m : ℤ)) := by
  rw [packSum_replicate, periodic, pow_mul, ← Nat.geomSum_eq (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw)]
  push_cast
  ring

theorem periodic_eq_natPack {w : ℕ} (hw : 0 < w) (N m : ℕ) :
    periodic w N m = natPack w (List.replicate N m) := by
  have h := periodic_cast hw N m
  rw [← List.map_replicate, ← natPack_cast] at h
  exact_mod_cast h

/-! ### Bits of one slot split -/

/-- `AND` splits at a slot boundary: the low digits and the high parts are combined separately. -/
theorem land_split {w b d : ℕ} (hb : b < 2 ^ w) (hd : d < 2 ^ w) (a c : ℕ) :
    (b + 2 ^ w * a) &&& (d + 2 ^ w * c) = (b &&& d) + 2 ^ w * (a &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hbd : (b &&& d) < 2 ^ w := Nat.and_lt_two_pow b hd
  rw [Nat.testBit_and, Nat.add_comm b, Nat.add_comm d, Nat.add_comm (b &&& d),
    Nat.testBit_two_pow_mul_add a hb, Nat.testBit_two_pow_mul_add c hd,
    Nat.testBit_two_pow_mul_add (a &&& c) hbd]
  split_ifs <;> simp [Nat.testBit_and]

theorem natPack_lt {w : ℕ} : ∀ {es : List ℕ}, (∀ e ∈ es, e < 2 ^ w) →
    natPack w es < 2 ^ (w * es.length)
  | [], _ => by simp [natPack_nil]
  | e :: es, h => by
    have he := h e (by simp)
    have ih := natPack_lt (es := es) fun x hx => h x (by simp [hx])
    rw [natPack_cons, List.length_cons, Nat.mul_succ, pow_add, Nat.mul_comm (2 ^ (w * _))]
    calc e + 2 ^ w * natPack w es < 2 ^ w + 2 ^ w * natPack w es := by omega
      _ = 2 ^ w * (natPack w es + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * es.length) := Nat.mul_le_mul_left _ ih

/-- **Digit-wise mask.** With every digit below `2^w` and `t ≤ w`, the periodic mask of the low `t`
bits reduces every digit modulo `2^t`. -/
theorem natPack_land_mask {w t : ℕ} (ht : t ≤ w) : ∀ {es : List ℕ}, (∀ e ∈ es, e < 2 ^ w) →
    natPack w es &&& natPack w (List.replicate es.length (2 ^ t - 1)) =
      natPack w (es.map (· % 2 ^ t))
  | [], _ => by simp [natPack_nil]
  | e :: es, h => by
    have he := h e (by simp)
    have hm : 2 ^ t - 1 < 2 ^ w :=
      lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos t) (by norm_num))
        (Nat.pow_le_pow_right (by norm_num) ht)
    rw [List.length_cons, List.replicate_succ, natPack_cons, natPack_cons, land_split he hm,
      Nat.and_two_pow_sub_one_eq_mod, natPack_land_mask ht fun x hx => h x (by simp [hx]),
      List.map_cons, natPack_cons]

theorem natPack_map_add (w : ℕ) (f g : ℕ → ℕ) : ∀ es : List ℕ,
    natPack w (es.map fun e => f e + g e) = natPack w (es.map f) + natPack w (es.map g)
  | [] => by simp [natPack_nil]
  | e :: es => by
    simp only [List.map_cons, natPack_cons, natPack_map_add w f g es]
    ring

theorem natPack_map_mul (w c : ℕ) : ∀ es : List ℕ,
    natPack w (es.map fun e => c * e) = c * natPack w es
  | [] => by simp [natPack_nil]
  | e :: es => by
    simp only [List.map_cons, natPack_cons, natPack_map_mul w c es]
    ring

/-- **Digit-wise division.** Clearing the low `t` bits of every digit (by the mask) and shifting
right by `t` divides every digit by `2^t`, with no carry between slots. -/
theorem natPack_clear_shift {w t : ℕ} (ht : t ≤ w) {es : List ℕ} (h : ∀ e ∈ es, e < 2 ^ w) :
    (natPack w es - (natPack w es &&& natPack w (List.replicate es.length (2 ^ t - 1)))) >>> t =
      natPack w (es.map (· / 2 ^ t)) := by
  rw [natPack_land_mask ht h, Nat.shiftRight_eq_div_pow]
  have hsplit : natPack w es = natPack w (es.map (· % 2 ^ t)) +
      2 ^ t * natPack w (es.map (· / 2 ^ t)) := by
    rw [← natPack_map_mul, List.map_map, ← natPack_map_add]
    congr 1
    conv_lhs => rw [← List.map_id es]
    exact List.map_congr_left fun e _ => (Nat.mod_add_div e (2 ^ t)).symm
  rw [hsplit, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (Nat.two_pow_pos t)]

/-- Packing is injective on digits below `2^w`. -/
theorem natPack_injective {w : ℕ} : ∀ {es fs : List ℕ}, (∀ e ∈ es, e < 2 ^ w) →
    (∀ f ∈ fs, f < 2 ^ w) → es.length = fs.length → natPack w es = natPack w fs → es = fs
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | e :: es, f :: fs, he, hf, hl, h => by
    rw [natPack_cons, natPack_cons] at h
    have h1 := he e (by simp)
    have h2 := hf f (by simp)
    have hmod := congrArg (· % 2 ^ w) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
    subst hmod
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    have htail : natPack w es = natPack w fs :=
      Nat.eq_of_mul_eq_mul_left hpos (Nat.add_left_cancel h)
    rw [natPack_injective (fun x hx => he x (by simp [hx])) (fun x hx => hf x (by simp [hx]))
      (by simpa using hl) htail]

/-- Every natural below `2^{wN}` is the packing of `N` digits below `2^w`. -/
theorem natPack_digits (w : ℕ) : ∀ (N X : ℕ), X < 2 ^ (w * N) →
    ∃ es : List ℕ, es.length = N ∧ (∀ e ∈ es, e < 2 ^ w) ∧ natPack w es = X
  | 0, X, h => ⟨[], rfl, by simp, by simp at h; simp [natPack_nil, h]⟩
  | N + 1, X, h => by
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    have hq : X / 2 ^ w < 2 ^ (w * N) := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, show w * N + w = w * (N + 1) by ring]
      exact h
    obtain ⟨es, hl, hd, hX⟩ := natPack_digits w N (X / 2 ^ w) hq
    refine ⟨X % 2 ^ w :: es, by simp [hl], ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact Nat.mod_lt _ hpos
      · exact hd e he
    · rw [natPack_cons, hX, Nat.mod_add_div]

/-- **Offset digits.** A signed packing plus the offset `O` in every slot is the natural packing of
the shifted slots, when they are nonnegative. -/
theorem packSum_add_periodic (w O : ℕ) : ∀ cs : List ℤ, (∀ c ∈ cs, 0 ≤ c + O) →
    packSum w cs + packSum w (List.replicate cs.length (O : ℤ)) =
      (natPack w (cs.map fun c : ℤ => (c + (O : ℤ)).toNat) : ℤ)
  | [], _ => by simp [packSum_nil, natPack_nil]
  | c :: cs, h => by
    have hc := h c (by simp)
    rw [List.length_cons, List.replicate_succ, packSum_cons, packSum_cons, List.map_cons,
      natPack_cons]
    push_cast
    rw [← packSum_add_periodic w O cs fun x hx => h x (by simp [hx]), Int.toNat_of_nonneg hc]
    ring

end KAM.Certificate
