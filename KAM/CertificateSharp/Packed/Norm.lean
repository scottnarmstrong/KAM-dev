/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Slots

/-!
# Packed absolute values and weighted `ℓ¹` norms

On packed slot data the weighted norm `Σ_i |d_i| w^{|key(i)|₁}` of the strip bound is computed with
a constant number of big-integer operations:

* `packAbs`: every slot's absolute value, from the offset digits by a digit shift (the sign bits), a
  mask and three subtractions (`packAbs_spec`);
* the weighted sum is the middle digit of **one product** with a reversed packed weight table, when
  no digit of the product carries (`natPack_digit`, `dot_extract`);
* the table (`weightRev`) is the outer product of reversed row and column tables of upper bounds
  `⌈w^e 2^q⌉` (`wCeil`) on a two-axis layout (`rowsPack_eq`).

`slotSum_le_packNorm`: under the decidable guard `normOk`, on the strip,
`‖slotSum L n d θ‖ ≤ packNorm / 2^(2q)`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM.Certificate

open KAM

/-! ### Digit-wise maps -/

theorem natPack_land_map {w : ℕ} (f g : ℕ → ℕ) : ∀ es : List ℕ, (∀ e ∈ es, f e < 2 ^ w) →
    (∀ e ∈ es, g e < 2 ^ w) →
    natPack w (es.map f) &&& natPack w (es.map g) = natPack w (es.map fun e => f e &&& g e)
  | [], _, _ => by simp [natPack_nil]
  | e :: es, hf, hg => by
    simp only [List.map_cons, natPack_cons]
    rw [land_split (hf e (by simp)) (hg e (by simp)),
      natPack_land_map f g es (fun x hx => hf x (by simp [hx])) (fun x hx => hg x (by simp [hx]))]

theorem natPack_map_sub {w : ℕ} (f g : ℕ → ℕ) (es : List ℕ) (h : ∀ e ∈ es, g e ≤ f e) :
    natPack w (es.map f) - natPack w (es.map g) = natPack w (es.map fun e => f e - g e) := by
  have : natPack w (es.map f) = natPack w (es.map g) + natPack w (es.map fun e => f e - g e) := by
    rw [← natPack_map_add]
    congr 1
    exact List.map_congr_left fun e he => (Nat.add_sub_cancel' (h e he)).symm
  omega

/-! ### Absolute values -/

/-- Packed absolute values of `N` slots within `[-2^l, 2^l)`: offset digits `Y`, sign bits
`S = digitShift l Y`, the nonnegative digits `P = Y &&& S (2^(l+1) - 1)`, then
`(P - 2^l S) + ((2^l·1 - 2^l S) - (Y - P))` digit by digit. -/
def packAbs (w N l : ℕ) (Z : ℤ) : ℕ :=
  let Y := (Z + (periodic w N (2 ^ l) : ℤ)).toNat
  let S := digitShift w N l Y
  let P := Y &&& (S * (2 ^ (l + 1) - 1))
  (P - S * 2 ^ l) + ((periodic w N (2 ^ l) - S * 2 ^ l) - (Y - P))

theorem packAbs_spec {w N l : ℕ} (hlw : l + 2 ≤ w) {cs : List ℤ} (hN : cs.length = N)
    (hB : ∀ c ∈ cs, -2 ^ l ≤ c ∧ c < 2 ^ l) :
    packAbs w N l (packSum w cs) = natPack w (cs.map Int.natAbs) := by
  have hw : 0 < w := by omega
  subst hN
  have hl1 : (2 : ℕ) ^ (l + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnn : ∀ c ∈ cs, 0 ≤ c + ((2 ^ l : ℕ) : ℤ) := fun c hc => by
    have := (hB c hc).1; push_cast; linarith
  set es := cs.map fun c : ℤ => (c + ((2 ^ l : ℕ) : ℤ)).toNat with hes
  have hlt : ∀ e ∈ es, e < 2 ^ (l + 1) := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    have h1 := (hB c hc).2
    have : ((c + ((2 ^ l : ℕ) : ℤ)).toNat : ℤ) < ((2 ^ (l + 1) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (hnn c hc)]; push_cast; rw [pow_succ]; linarith
    exact_mod_cast this
  have hdig : ∀ e ∈ es, e < 2 ^ w := fun e he => (hlt e he).trans_le hl1
  have hlen : es.length = cs.length := by simp [hes]
  have hY : (packSum w cs + (periodic w cs.length (2 ^ l) : ℤ)).toNat = natPack w es := by
    rw [periodic_cast hw, packSum_add_periodic w (2 ^ l) cs hnn, Int.toNat_natCast]
  have hS : digitShift w cs.length l (natPack w es) = natPack w (es.map (· / 2 ^ l)) := by
    unfold digitShift
    rw [periodic_eq_natPack hw, ← hlen]
    exact natPack_clear_shift (by omega) hdig
  have hpow : (0 : ℕ) < 2 ^ l := Nat.two_pow_pos l
  have hbit : ∀ e ∈ es, e / 2 ^ l = if 2 ^ l ≤ e then 1 else 0 := by
    intro e he
    have := hlt e he
    rw [pow_succ] at this
    split_ifs with h
    · exact le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpow).mpr (by omega)))
        ((Nat.le_div_iff_mul_le hpow).mpr (by omega))
    · exact Nat.div_eq_of_lt (by omega)
  -- the five digit-wise intermediates
  have hSK : natPack w (es.map (· / 2 ^ l)) * (2 ^ (l + 1) - 1) =
      natPack w (es.map fun e => (2 ^ (l + 1) - 1) * (e / 2 ^ l)) := by
    rw [mul_comm, ← natPack_map_mul, List.map_map]; rfl
  have hP : natPack w es &&& natPack w (es.map fun e => (2 ^ (l + 1) - 1) * (e / 2 ^ l)) =
      natPack w (es.map fun e => if 2 ^ l ≤ e then e else 0) := by
    have hid : natPack w es = natPack w (es.map id) := by rw [List.map_id]
    rw [hid, natPack_land_map id _ es hdig (fun e he => by
      rw [hbit e he]; split_ifs <;> omega)]
    congr 1
    refine List.map_congr_left fun e he => ?_
    rw [hbit e he]
    split_ifs with h
    · rw [mul_one, id, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hlt e he)]
    · simp
  have hS2 : natPack w (es.map (· / 2 ^ l)) * 2 ^ l =
      natPack w (es.map fun e => if 2 ^ l ≤ e then 2 ^ l else 0) := by
    rw [mul_comm, ← natPack_map_mul, List.map_map]
    congr 1
    refine List.map_congr_left fun e he => ?_
    simp only [Function.comp_apply, hbit e he]
    split_ifs <;> simp
  have hper : periodic w cs.length (2 ^ l) = natPack w (es.map fun _ => 2 ^ l) := by
    rw [periodic_eq_natPack hw, ← hlen, List.map_const']
  unfold packAbs
  simp only []
  rw [hY, hS, hSK, hP, hS2, hper,
    natPack_map_sub _ _ es (fun e _ => by split_ifs <;> omega),
    natPack_map_sub (fun _ => 2 ^ l) _ es (fun e _ => by split_ifs <;> omega),
    show natPack w es = natPack w (es.map fun e => e) by rw [List.map_id'],
    natPack_map_sub (fun e => e) (fun e => if 2 ^ l ≤ e then e else 0) es
      (fun e _ => by split_ifs <;> omega)]
  · rw [natPack_map_sub _ _ es (fun e he => by
      have := hlt e he; split_ifs <;> omega), ← natPack_map_add, hes, List.map_map]
    congr 1
    refine List.map_congr_left fun c hc => ?_
    have h0 := hnn c hc
    simp only [Function.comp_apply]
    have ht : (((c + ((2 ^ l : ℕ) : ℤ)).toNat : ℕ) : ℤ) = c + ((2 ^ l : ℕ) : ℤ) :=
      Int.toNat_of_nonneg h0
    generalize (c + ((2 ^ l : ℕ) : ℤ)).toNat = E at ht ⊢
    generalize (2 ^ l : ℕ) = L at ht ⊢
    by_cases h1 : L ≤ E
    · simp only [h1, ite_true]; omega
    · simp only [h1, ite_false]; omega

/-! ### Reading a digit -/

/-- Digit `k` of a packing with digits below `2^w`, by a shift and a mask. -/
theorem natPack_digit {w : ℕ} : ∀ (es : List ℕ) (k : ℕ), (∀ e ∈ es, e < 2 ^ w) →
    (natPack w es >>> (w * k)) &&& (2 ^ w - 1) = es.getD k 0
  | [], k, _ => by simp [natPack_nil]
  | e :: es, 0, h => by
    rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod, natPack_cons,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h e (by simp))]
    rfl
  | e :: es, k + 1, h => by
    have he := h e (by simp)
    rw [Nat.mul_succ, Nat.add_comm, Nat.shiftRight_add, natPack_cons,
      Nat.shiftRight_eq_div_pow (e + 2 ^ w * natPack w es) w,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt he, Nat.zero_add,
      natPack_digit es k fun x hx => h x (by simp [hx])]
    rfl

/-- **The no-carry product digit.** If the convolution of two nonnegative slot lists has every
entry below `2^w`, digit `k` of the product of their packings is its entry `k`. -/
theorem dot_extract {w : ℕ} {a v : List ℤ} (ha0 : ∀ x ∈ a, 0 ≤ x) (hv0 : ∀ x ∈ v, 0 ≤ x)
    (hbound : ∀ c ∈ listConv a v, c < 2 ^ w) {X : ℕ}
    (hX : (X : ℤ) = packSum w a * packSum w v) (k : ℕ) :
    ((X >>> (w * k)) &&& (2 ^ w - 1) : ℕ) = ((listConv a v).getD k 0).toNat := by
  have hnn : ∀ c ∈ listConv a v, 0 ≤ c := by
    intro c hc
    unfold listConv at hc
    split_ifs at hc
    · simp at hc
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hc
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    have h1 : 0 ≤ a.getD i 0 := by
      by_cases hi : i < a.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact ha0 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]; rfl
    have h2 : 0 ≤ v.getD (k - i) 0 := by
      by_cases hi : k - i < v.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact hv0 _ (List.getElem_mem _)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]; rfl
    exact mul_nonneg h1 h2
  have hXp : X = natPack w ((listConv a v).map Int.toNat) := by
    have : ((natPack w ((listConv a v).map Int.toNat) : ℕ) : ℤ) = (X : ℤ) := by
      rw [natPack_cast, List.map_map, hX, ← packSum_listConv]
      congr 1
      conv_rhs => rw [← List.map_id (listConv a v)]
      exact List.map_congr_left fun c hc => by simp [Int.toNat_of_nonneg (hnn c hc)]
    exact_mod_cast this.symm
  rw [hXp, natPack_digit _ k (fun e he => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    have := hbound c hc
    have h0 := hnn c hc
    have : (c.toNat : ℤ) < ((2 ^ w : ℕ) : ℤ) := by rw [Int.toNat_of_nonneg h0]; exact_mod_cast this
    exact_mod_cast this)]
  by_cases hk : k < (listConv a v).length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hk)]

/-! ### Weight tables on a two-axis layout -/

/-- An upper bound `⌈w^e 2^q⌉` of `w^e 2^q` for the rational weight `w = num/den`. -/
def wCeil (W : CertWeight) (q e : ℕ) : ℕ :=
  (W.w.num.toNat ^ e * 2 ^ q + W.w.den ^ e - 1) / W.w.den ^ e

theorem le_ceilDiv_mul (x d : ℕ) (hd : 0 < d) : x ≤ (x + d - 1) / d * d := by
  have h1 := Nat.div_add_mod (x + d - 1) d
  have h2 := Nat.mod_lt (x + d - 1) hd
  rw [mul_comm]
  generalize d * ((x + d - 1) / d) = m at h1 ⊢
  omega

theorem wCeil_ge {W : CertWeight} (hw : 0 < W.w) (q e : ℕ) :
    (W.w : ℝ) ^ e * 2 ^ q ≤ (wCeil W q e : ℝ) := by
  have hnum : (0 : ℤ) < W.w.num := Rat.num_pos.mpr hw
  have hden : 0 < W.w.den ^ e := pow_pos W.w.den_pos e
  have hceil : W.w.num.toNat ^ e * 2 ^ q ≤ wCeil W q e * W.w.den ^ e :=
    le_ceilDiv_mul _ _ hden
  have hwR : (W.w : ℝ) = (W.w.num.toNat : ℝ) / (W.w.den : ℝ) := by
    have : ((W.w.num.toNat : ℕ) : ℝ) = (W.w.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    rw [this, ← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hdR : (0 : ℝ) < (W.w.den : ℝ) ^ e := by positivity
  rw [hwR, div_pow, div_mul_eq_mul_div, div_le_iff₀ hdR]
  exact_mod_cast hceil

/-- The rows `a < D₀` of a two-axis layout, reversed, with the row weights `⌈w^{|lo₀+a|} 2^q⌉`. -/
def rowsRev (W : CertWeight) (q : ℕ) (L : PackLayout) : List ℕ :=
  (List.range (L.dims.getD 0 0)).reverse.map fun a => wCeil W q (L.lo.getD 0 0 + a).natAbs

/-- The columns `b < s₀` (the row stride), reversed, with the column weights (`0` past `D₁`). -/
def colsRev (W : CertWeight) (q : ℕ) (L : PackLayout) : List ℕ :=
  (List.range (L.stride.getD 0 0)).reverse.map fun b =>
    if b < L.dims.getD 1 0 then wCeil W q (L.lo.getD 1 0 + b).natAbs else 0

/-- Rows of a table packed one block of `s₀` slots after the other (`r · C` per row). -/
def rowsPack (w s0 Cpk : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r * Cpk + (rowsPack w s0 Cpk rs <<< (w * s0))

/-- The reversed packed weight table of a two-axis layout. -/
def weightRev (W : CertWeight) (q : ℕ) (L : PackLayout) : ℕ :=
  rowsPack L.width (L.stride.getD 0 0) (natPack L.width (colsRev W q L)) (rowsRev W q L)

/-- The largest entry of a list of naturals. -/
def listMax (l : List ℕ) : ℕ := l.foldr max 0

theorem le_listMax {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ listMax l := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem rowsPack_eq {w s0 : ℕ} {cr : List ℕ} (hcl : cr.length = s0) :
    ∀ rs : List ℕ, rowsPack w s0 (natPack w cr) rs =
      natPack w (rs.flatMap fun r => cr.map (r * ·))
  | [] => by simp [rowsPack, natPack_nil]
  | r :: rs => by
    rw [rowsPack, rowsPack_eq hcl rs, List.flatMap_cons, natPack_append, List.length_map, hcl,
      Nat.shiftLeft_eq, ← natPack_map_mul]
    ring

/-- The packed norm: digit `N' - 1` of `|Z| · weightRev`, `N' = D₀ s₀`. -/
def packNorm (W : CertWeight) (q l : ℕ) (L : PackLayout) (Z : ℤ) : ℕ :=
  ((packAbs L.width L.denseLen l Z * weightRev W q L) >>>
    (L.width * (L.dims.getD 0 0 * L.stride.getD 0 0 - 1))) &&& (2 ^ L.width - 1)

/-- The guard of the packed norm (decidable, from the layout and the bounds only): a well-formed
two-axis layout with unit column stride and `D₁ ≤ s₀`, a positive weight, `B < 2^l`,
`l + 2 ≤ w`, and no carry in the product: `D₀ s₀ 2^l · max row · max column < 2^w`. -/
def normOk (W : CertWeight) (q l B : ℕ) (L : PackLayout) : Bool :=
  layoutWf L && L.dims.length == 2 && L.stride.length == 2 && L.stride.getD 1 0 == 1 &&
    decide (L.dims.getD 1 0 ≤ L.stride.getD 0 0) && decide (0 < W.w) && decide (B < 2 ^ l) &&
    decide (l + 2 ≤ L.width) &&
    decide (L.dims.getD 0 0 * L.stride.getD 0 0 * 2 ^ l *
      (listMax (rowsRev W q L) * listMax (colsRev W q L)) < 2 ^ L.width)

end KAM.CertificateSharp.Packed
