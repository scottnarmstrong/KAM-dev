/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Complex

/-!
# The box check: a packed integer on a two-axis box, by one mask

For a layout `L` with two axes (`dims = [D₀, D₁]`, `stride = [S, 1]`, `D₁ ≤ S`, slot width `w`),
the slot `i < N = (D₀ - 1) S + D₁` is a box slot iff `i % S < D₁`; the others are the gap slots
between rows. `boxOk L l Z` checks, by one closed-form pattern, one addition, one comparison, one
mask and one equality, that `Z` packs digits in `[-2^l, 2^l]` on the box slots and `0` on the gap
slots (`boxOk_sound`: an `SRep L (2^l) Z d`). No digit list is built in the kernel, and nothing is
assumed about how `Z` was computed: a candidate computed in the kernel (`V2-PACKED.md` §12.4 (Z))
is validated by this check alone.

* `boxDigits S D₁ N v`: the digit pattern (`v` on the box slots, `0` on the gap slots);
* `boxPat w S D₀ D₁ v`: its packing in closed form (`natPack_boxDigits`), the row
  `periodic w D₁ v` repeated `D₀` times with period `w S`;
* `natPack_land`: `AND` of two packings is the packing of the digit-wise `AND`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM.Certificate

/-! ### The pattern -/

/-- The digit pattern of a two-axis box: `v` on the box slots (`i % S < D₁`), `0` on the gap
slots, `N` slots. -/
def boxDigits (S D1 N v : ℕ) : List ℕ := (List.range N).map fun i => if i % S < D1 then v else 0

/-- Its packing in closed form (kernel: two `periodic` constants). -/
def boxPat (w S D0 D1 v : ℕ) : ℕ := periodic (w * S) D0 (periodic w D1 v)

theorem periodic_succ {W : ℕ} (hW : 0 < W) (N m : ℕ) :
    periodic W (N + 1) m = m + 2 ^ W * periodic W N m := by
  rw [periodic_eq_natPack hW, periodic_eq_natPack hW, List.replicate_succ, natPack_cons]

theorem periodic_one {W : ℕ} (hW : 0 < W) (m : ℕ) : periodic W 1 m = m := by
  rw [periodic_succ hW, periodic_eq_natPack hW]
  simp [natPack_nil]

theorem natPack_replicate_zero (w : ℕ) : ∀ k : ℕ, natPack w (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, natPack_cons, natPack_replicate_zero w k]; simp

theorem boxDigits_length (S D1 N v : ℕ) : (boxDigits S D1 N v).length = N := by
  simp [boxDigits]

theorem boxDigits_getD {S D1 N v i : ℕ} (hi : i < N) :
    (boxDigits S D1 N v).getD i 0 = if i % S < D1 then v else 0 := by
  simp [boxDigits, List.getD_eq_getElem?_getD, hi]

/-- The first row. -/
theorem boxDigits_row {S D1 v : ℕ} (hD : D1 ≤ S) :
    boxDigits S D1 S v = List.replicate D1 v ++ List.replicate (S - D1) 0 := by
  apply List.ext_getElem
  · simp [boxDigits]; omega
  · intro i h1 h2
    simp only [boxDigits, List.getElem_map, List.getElem_range]
    rw [List.getElem_append]
    have hi : i < S := by simpa [boxDigits] using h1
    rw [Nat.mod_eq_of_lt hi]
    split_ifs with h3 h4 h4
    · simp
    · simp at h4; omega
    · simp at h4; omega
    · simp

/-- One more row in front. -/
theorem boxDigits_add (S D1 N v : ℕ) :
    boxDigits S D1 (S + N) v = boxDigits S D1 S v ++ boxDigits S D1 N v := by
  simp only [boxDigits, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, Nat.add_mod_left]

/-- **The closed form of the box pattern.** -/
theorem natPack_boxDigits {w S D1 v : ℕ} (hw : 0 < w) (hS : 0 < S) (hD : D1 ≤ S) :
    ∀ D0 : ℕ, 1 ≤ D0 → natPack w (boxDigits S D1 ((D0 - 1) * S + D1) v) = boxPat w S D0 D1 v
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    have hrow : boxDigits S D1 D1 v = List.replicate D1 v := by
      apply List.ext_getElem
      · simp [boxDigits]
      · intro i h1 _
        have hi : i < D1 := by simpa [boxDigits] using h1
        simp [boxDigits, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hD), hi]
    simp only [Nat.sub_self, zero_mul, zero_add, boxPat]
    rw [hrow, periodic_one (Nat.mul_pos hw hS), periodic_eq_natPack hw]
  | D0 + 2, _ => by
    have ih := natPack_boxDigits (v := v) hw hS hD (D0 + 1) (by omega)
    have hN : (D0 + 2 - 1) * S + D1 = S + ((D0 + 1 - 1) * S + D1) := by
      rw [show D0 + 2 - 1 = (D0 + 1 - 1) + 1 by omega, Nat.add_mul, one_mul]; ring
    rw [hN, boxDigits_add, natPack_append, ih, boxDigits_length, boxDigits_row hD,
      natPack_append, natPack_replicate_zero, ← periodic_eq_natPack hw D1 v]
    simp only [boxPat, show D0 + 2 = (D0 + 1) + 1 from rfl, periodic_succ (Nat.mul_pos hw hS)]
    ring

/-! ### `AND` of packings -/

/-- `AND` of two packings with digits below `2^w` is the packing of the digit-wise `AND`. -/
theorem natPack_land {w : ℕ} : ∀ {es ms : List ℕ}, es.length = ms.length →
    (∀ e ∈ es, e < 2 ^ w) → (∀ m ∈ ms, m < 2 ^ w) →
    (natPack w es &&& natPack w ms) = natPack w (List.zipWith (· &&& ·) es ms)
  | [], [], _, _, _ => by simp [natPack_nil]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl
  | e :: es, m :: ms, hl, he, hm => by
    rw [natPack_cons, natPack_cons, land_split (he e (by simp)) (hm m (by simp)),
      natPack_land (by simpa using hl) (fun x hx => he x (by simp [hx]))
        (fun x hx => hm x (by simp [hx])), List.zipWith_cons_cons, natPack_cons]

/-- The signed packing of digit differences. -/
theorem packSum_zipWith_sub (w : ℕ) : ∀ {es os : List ℕ}, es.length = os.length →
    packSum w (List.zipWith (fun (e o : ℕ) => (e : ℤ) - (o : ℤ)) es os) =
      (natPack w es : ℤ) - (natPack w os : ℤ)
  | [], [], _ => by simp [packSum_nil, natPack_nil]
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl
  | e :: es, o :: os, hl => by
    rw [List.zipWith_cons_cons, packSum_cons, packSum_zipWith_sub w (by simpa using hl),
      natPack_cons, natPack_cons]
    push_cast
    ring

/-! ### The check -/

/-- The number of slots of a two-axis box `[D₀, D₁]` with row stride `S`. -/
def boxLen (S D0 D1 : ℕ) : ℕ := (D0 - 1) * S + D1

/-- The shape of a two-axis box layout (decidable). -/
def boxShapeOk (L : PackLayout) : Bool :=
  L.dims.length == 2 && L.stride == [L.stride.getD 0 0, 1] && decide (0 < L.dims.getD 0 0) &&
    decide (0 < L.dims.getD 1 0) && decide (L.dims.getD 1 0 ≤ L.stride.getD 0 0) &&
    decide (0 < L.width)

/-- **Box check**: `Z` packs, on the two-axis box `L`, digits in `[-2^l, 2^l]` on the box slots
and `0` on the gap slots (`boxOk_sound`). -/
def boxOk (L : PackLayout) (l : ℕ) (Z : ℤ) : Bool :=
  boxShapeOk L && decide (l + 1 ≤ L.width) &&
    decide (0 ≤ Z + (boxPat L.width (L.stride.getD 0 0) (L.dims.getD 0 0) (L.dims.getD 1 0)
      (2 ^ l) : ℤ)) &&
    decide ((Z + (boxPat L.width (L.stride.getD 0 0) (L.dims.getD 0 0) (L.dims.getD 1 0)
      (2 ^ l) : ℤ)).toNat < 2 ^ (L.width * boxLen (L.stride.getD 0 0) (L.dims.getD 0 0)
        (L.dims.getD 1 0))) &&
    ((Z + (boxPat L.width (L.stride.getD 0 0) (L.dims.getD 0 0) (L.dims.getD 1 0)
      (2 ^ l) : ℤ)).toNat &&& boxPat L.width (L.stride.getD 0 0) (L.dims.getD 0 0)
        (L.dims.getD 1 0) (2 ^ (l + 1) - 1) ==
      (Z + (boxPat L.width (L.stride.getD 0 0) (L.dims.getD 0 0) (L.dims.getD 1 0)
        (2 ^ l) : ℤ)).toNat)

/-- The shape facts. -/
theorem boxShapeOk_spec {L : PackLayout} (h : boxShapeOk L = true) :
    ∃ D0 D1 S, L.dims = [D0, D1] ∧ L.stride = [S, 1] ∧ 0 < D0 ∧ 0 < D1 ∧ D1 ≤ S ∧
      0 < L.width := by
  simp only [boxShapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hl, hs⟩, h0⟩, h1⟩, hD⟩, hw⟩ := h
  match hd : L.dims, hl with
  | [D0, D1], _ =>
    rw [hd] at h0 h1 hD
    exact ⟨D0, D1, L.stride.getD 0 0, rfl, hs, by simpa using h0, by simpa using h1,
      by simpa using hD, hw⟩

theorem boxLen_eq_denseLen {L : PackLayout} {D0 D1 S : ℕ} (hd : L.dims = [D0, D1])
    (hs : L.stride = [S, 1]) (h0 : 0 < D0) (h1 : 0 < D1) :
    boxLen S D0 D1 = L.denseLen := by
  unfold PackLayout.denseLen
  rw [hd, hs]
  simp only [List.all_cons, List.all_nil, decide_eq_true h0, decide_eq_true h1, Bool.and_true,
    ↓reduceIte, boxLen, packDot, List.map_cons, List.map_nil, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.sum_cons, List.sum_nil]
  omega

/-- A box slot of a two-axis box layout is in the box. -/
theorem inBox_of_mod {L : PackLayout} {D0 D1 S : ℕ} (hd : L.dims = [D0, D1])
    (hs : L.stride = [S, 1]) (h0 : 0 < D0) (hD : D1 ≤ S) {i : ℕ} (hi : i < boxLen S D0 D1)
    (hm : i % S < D1) : InBox L i := by
  have hS : 0 < S := lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hm) hD
  have hrow : i / S < D0 := by
    rw [Nat.div_lt_iff_lt_mul hS]
    unfold boxLen at hi
    obtain ⟨D, rfl⟩ : ∃ D, D0 = D + 1 := ⟨D0 - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hi
    rw [Nat.succ_mul]
    omega
  refine ⟨[i / S, i % S], by simp [hd], fun j hj => ?_, ?_⟩
  · rw [hd] at hj ⊢
    simp at hj
    rcases j with _ | _ | j
    · simpa using hrow
    · simpa using hm
    · omega
  · rw [hs, packDot]
    simp [Nat.div_add_mod']

/-- **Soundness of the box check.** -/
theorem boxOk_sound {L : PackLayout} {l : ℕ} {Z : ℤ} (h : boxOk L l Z = true) :
    ∃ d : List ℤ, SRep L (2 ^ l) Z d := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hshape, hlw⟩, h0⟩, hlt⟩, hmask⟩ := h
  obtain ⟨D0, D1, S, hd, hs, hD0, hD1, hD, hw⟩ := boxShapeOk_spec hshape
  have hS : 0 < S := lt_of_lt_of_le hD1 hD
  simp only [hd, hs, List.getD_cons_zero, List.getD_cons_succ] at h0 hlt hmask
  set w := L.width
  set N := boxLen S D0 D1 with hNdef
  set O := boxPat w S D0 D1 (2 ^ l)
  set Y := (Z + (O : ℤ)).toNat with hYdef
  obtain ⟨es, hl, hdig, hX⟩ := natPack_digits w N Y hlt
  have hpat : ∀ v, v < 2 ^ w → natPack w (boxDigits S D1 N v) = boxPat w S D0 D1 v :=
    fun v _ => natPack_boxDigits hw hS hD D0 hD0
  have hpw : ∀ {v}, v ≤ 2 ^ (l + 1) - 1 → v < 2 ^ w := fun hv =>
    lt_of_le_of_lt hv (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by norm_num))
      (Nat.pow_le_pow_right (by norm_num) hlw))
  have hdig_ms : ∀ m ∈ boxDigits S D1 N (2 ^ (l + 1) - 1), m < 2 ^ w := by
    intro m hm
    simp only [boxDigits, List.mem_map] at hm
    obtain ⟨i, -, rfl⟩ := hm
    split_ifs
    · exact hpw le_rfl
    · exact Nat.two_pow_pos _
  rw [← hpat _ (hpw le_rfl), ← hX, natPack_land (by rw [hl, boxDigits_length]) hdig hdig_ms]
    at hmask
  have hzip := natPack_injective (fun e he => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      simp only [List.getElem_zipWith]
      exact Nat.and_lt_two_pow _ (hdig_ms _ (List.getElem_mem _))) hdig
    (by simp [hl, boxDigits_length]) hmask
  -- every digit: below `2^(l+1)` on the box slots, `0` on the gap slots
  have hesi : ∀ i (hi : i < N), (if i % S < D1 then es[i]'(by rw [hl]; exact hi) < 2 ^ (l + 1)
      else es[i]'(by rw [hl]; exact hi) = 0) := by
    intro i hi
    have hi' : i < (List.zipWith (· &&& ·) es (boxDigits S D1 N (2 ^ (l + 1) - 1))).length := by
      simp [hl, boxDigits_length, hi]
    have := List.getElem_of_eq hzip hi'
    simp only [List.getElem_zipWith, boxDigits, List.getElem_map, List.getElem_range] at this
    split_ifs at this ⊢ with hm
    · rw [← this, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · rw [← this]; simp
  -- the signed digits
  set os := boxDigits S D1 N (2 ^ l)
  refine ⟨List.zipWith (fun (e o : ℕ) => (e : ℤ) - (o : ℤ)) es os, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [List.length_zipWith, hl, boxDigits_length, min_self, hNdef,
      boxLen_eq_denseLen hd hs hD0 hD1]
  · rw [packSum_zipWith_sub w (by simp [hl, os, boxDigits_length]), hX, hpat _ (hpw (by
      calc 2 ^ l ≤ 2 ^ l + (2 ^ l - 1) := Nat.le_add_right _ _
        _ = 2 ^ (l + 1) - 1 := by rw [pow_succ]; omega)), hYdef, Int.toNat_of_nonneg h0]
    ring
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hiN : i < N := by simpa [hl, os, boxDigits_length] using hi
    simp only [List.getElem_zipWith, os, boxDigits, List.getElem_map, List.getElem_range]
    have := hesi i hiN
    split_ifs at this ⊢ with hm
    · have h2 : ((es[i]'(by rw [hl]; exact hiN) : ℕ) : ℤ) < ((2 ^ (l + 1) : ℕ) : ℤ) := by
        exact_mod_cast this
      push_cast at h2 ⊢
      rw [abs_le]; constructor
      · have : (0 : ℤ) ≤ (es[i]'(by rw [hl]; exact hiN) : ℕ) := by positivity
        linarith
      · rw [pow_succ] at h2; linarith
    · rw [this]; simp
  · intro i hne
    have hiN : i < N := by
      by_contra hc
      apply hne
      have hlen : (List.zipWith (fun (e o : ℕ) => (e : ℤ) - (o : ℤ)) es os).length ≤ i := by
        simp only [List.length_zipWith, hl, os, boxDigits_length, min_self]
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
      rfl
    by_cases hm : i % S < D1
    · exact inBox_of_mod hd hs hD0 hD hiN hm
    · exfalso
      apply hne
      have := hesi i hiN
      simp only [hm, ↓reduceIte] at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
      simp only [List.getElem?_eq_getElem (by rw [hl]; exact hiN),
        List.getElem?_eq_getElem (by simp [os, boxDigits_length, hiN] : i < os.length)]
      simp [this, os, boxDigits, hm]

end KAM.CertificateSharp.Packed
