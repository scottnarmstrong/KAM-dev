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

/-- The convolution of nonnegative slot lists is nonnegative. -/
theorem listConv_nonneg {a v : List ℤ} (ha0 : ∀ x ∈ a, 0 ≤ x) (hv0 : ∀ x ∈ v, 0 ≤ x) :
    ∀ c ∈ listConv a v, 0 ≤ c := by
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

theorem getD_nonneg {l : List ℤ} (h : ∀ x ∈ l, 0 ≤ x) (k : ℕ) : 0 ≤ l.getD k 0 := by
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact h _ (List.getElem_mem _)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hk)]; rfl

/-- **The no-carry product digit.** If the convolution of two nonnegative slot lists has every
entry below `2^w`, digit `k` of the product of their packings is its entry `k`. -/
theorem dot_extract {w : ℕ} {a v : List ℤ} (ha0 : ∀ x ∈ a, 0 ≤ x) (hv0 : ∀ x ∈ v, 0 ≤ x)
    (hbound : ∀ c ∈ listConv a v, c < 2 ^ w) {X : ℕ}
    (hX : (X : ℤ) = packSum w a * packSum w v) (k : ℕ) :
    ((X >>> (w * k)) &&& (2 ^ w - 1) : ℕ) = ((listConv a v).getD k 0).toNat := by
  have hnn := listConv_nonneg ha0 hv0
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
  (List.range (L.dims.getD 0 0)).reverse.map fun a : ℕ => wCeil W q (L.lo.getD 0 0 + (a : ℤ)).natAbs

/-- The columns `b < s₀` (the row stride), reversed, with the column weights (`0` past `D₁`). -/
def colsRev (W : CertWeight) (q : ℕ) (L : PackLayout) : List ℕ :=
  (List.range (L.stride.getD 0 0)).reverse.map fun b : ℕ =>
    if b < L.dims.getD 1 0 then wCeil W q (L.lo.getD 1 0 + (b : ℤ)).natAbs else 0

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

/-! ### The strip bound -/

/-- The weight of slot `p` of a two-axis layout: row weight times column weight (`0` off the
columns). -/
def slotWeight (W : CertWeight) (q : ℕ) (L : PackLayout) (p : ℕ) : ℕ :=
  wCeil W q (L.lo.getD 0 0 + (p / L.stride.getD 0 0 : ℕ)).natAbs *
    (if p % L.stride.getD 0 0 < L.dims.getD 1 0 then
      wCeil W q (L.lo.getD 1 0 + (p % L.stride.getD 0 0 : ℕ)).natAbs else 0)

/-- The reversed table as an integer slot list (blocks of `s₀` slots, one per row). -/
def weightRevList (W : CertWeight) (q : ℕ) (L : PackLayout) : List ℤ :=
  ((rowsRev W q L).map fun r => (colsRev W q L).map fun c => ((r * c : ℕ) : ℤ)).flatten

theorem length_rowsRev (W : CertWeight) (q : ℕ) (L : PackLayout) :
    (rowsRev W q L).length = L.dims.getD 0 0 := by simp [rowsRev]

theorem length_colsRev (W : CertWeight) (q : ℕ) (L : PackLayout) :
    (colsRev W q L).length = L.stride.getD 0 0 := by simp [colsRev]

theorem weightRev_cast (W : CertWeight) (q : ℕ) (L : PackLayout) :
    ((weightRev W q L : ℕ) : ℤ) = packSum L.width (weightRevList W q L) := by
  rw [weightRev, rowsPack_eq (length_colsRev W q L), natPack_cast]
  unfold weightRevList
  congr 1
  simp [List.flatMap, List.map_flatten, List.map_map, Function.comp_def]

theorem length_weightRevList (W : CertWeight) (q : ℕ) (L : PackLayout) :
    (weightRevList W q L).length = L.dims.getD 0 0 * L.stride.getD 0 0 := by
  unfold weightRevList
  rw [List.length_flatten, List.map_map]
  have : ∀ x ∈ rowsRev W q L,
      ((fun r => (colsRev W q L).map fun c => ((r * c : ℕ) : ℤ)) x).length =
        L.stride.getD 0 0 := fun x _ => by simp [length_colsRev]
  rw [List.map_congr_left (f := List.length ∘ _) (g := fun _ => L.stride.getD 0 0)
    (fun x hx => this x hx), List.map_const', List.sum_replicate, length_rowsRev, smul_eq_mul]

/-- The reversed table at slot `N' - 1 - p` is the weight of slot `p`. -/
theorem weightRevList_getD (W : CertWeight) (q : ℕ) (L : PackLayout) {p : ℕ}
    (hp : p < L.dims.getD 0 0 * L.stride.getD 0 0) :
    (weightRevList W q L).getD (L.dims.getD 0 0 * L.stride.getD 0 0 - 1 - p) 0 =
      (slotWeight W q L p : ℤ) := by
  generalize hD0 : L.dims.getD 0 0 = D0 at hp ⊢
  generalize hs0d : L.stride.getD 0 0 = s0 at hp ⊢
  have hs0 : 0 < s0 := by
    rcases Nat.eq_zero_or_pos s0 with h | h
    · rw [h, Nat.mul_zero] at hp; omega
    · exact h
  have hb : p % s0 < s0 := Nat.mod_lt _ hs0
  have hpab : p = p / s0 * s0 + p % s0 := by rw [Nat.mul_comm]; exact (Nat.div_add_mod p s0).symm
  have ha : p / s0 < D0 := by
    by_contra h
    have : D0 * s0 ≤ p / s0 * s0 := Nat.mul_le_mul_right _ (not_lt.mp h)
    omega
  generalize p / s0 = a at hpab ha
  generalize p % s0 = b at hpab hb
  have hidx : D0 * s0 - 1 - p = (D0 - 1 - a) * s0 + (s0 - 1 - b) := by
    obtain ⟨k, hk⟩ : ∃ k, D0 = a + 1 + k := ⟨D0 - 1 - a, by omega⟩
    rw [hk, hpab]
    have e1 : (a + 1 + k) * s0 = a * s0 + s0 + k * s0 := by ring
    have e2 : (a + 1 + k - 1 - a) = k := by omega
    rw [e1, e2]
    omega
  have hi : D0 - 1 - a < (rowsRev W q L).length := by rw [length_rowsRev, hD0]; omega
  have hj : s0 - 1 - b < (colsRev W q L).length := by rw [length_colsRev, hs0d]; omega
  have hblk : ∀ x ∈ (rowsRev W q L).map (fun r => (colsRev W q L).map fun c => ((r * c : ℕ) : ℤ)),
      x.length = s0 := by
    intro x hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
    simp only [List.length_map, length_colsRev]
    exact hs0d
  have hC : ((rowsRev W q L).map (fun r => (colsRev W q L).map fun c => ((r * c : ℕ) : ℤ))).getD
      (D0 - 1 - a) [] =
      (colsRev W q L).map fun c => (((rowsRev W q L)[D0 - 1 - a] * c : ℕ) : ℤ) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  rw [hidx]
  unfold weightRevList
  rw [← getD_getD_of_flatten _ hblk _ _ (by omega), hC, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]
  simp only [rowsRev, colsRev, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range, hD0, hs0d]
  have e3 : D0 - 1 - (D0 - 1 - a) = a := by omega
  have e4 : s0 - 1 - (s0 - 1 - b) = b := by omega
  have e5 : p / s0 = a := by rw [hpab, Nat.add_comm, Nat.add_mul_div_right _ _ hs0,
    Nat.div_eq_of_lt hb, Nat.zero_add]
  have e6 : p % s0 = b := by rw [hpab, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  rw [e3, e4]
  unfold slotWeight
  rw [hs0d, e5, e6]

/-- **The strip bound of the packed norm.** -/
theorem slotSum_le_packNorm {W : CertWeight} {q l B : ℕ} {L : PackLayout} {Z : ℤ}
    {d : List ℤ} (hs : SRep L B Z d) (hok : normOk W q l B L = true) {s N : ℕ}
    (hW : checkWeight W s N = true) {n : ℕ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) :
    ‖slotSum L n d θ‖ ≤ (packNorm W q l L Z : ℝ) / 2 ^ (2 * q) := by
  simp only [normOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hwf, hdl⟩, hsl⟩, hs1⟩, hD1⟩, hw0⟩, hBl⟩, hlw⟩, hcarry⟩ := hok
  set w := L.width
  set D0 := L.dims.getD 0 0
  set D1 := L.dims.getD 1 0
  set s0 := L.stride.getD 0 0
  have hw1 := CertWeight.one_le_w hW
  -- the shape of a two-axis layout
  obtain ⟨x0, x1, hdx⟩ := List.length_eq_two.mp hdl
  obtain ⟨t0, t1, hst⟩ := List.length_eq_two.mp hsl
  have hD0e : D0 = x0 := by simp [D0, hdx]
  have hD1e : D1 = x1 := by simp [D1, hdx]
  have hs0e : s0 = t0 := by simp [s0, hst]
  have ht1 : t1 = 1 := by simpa [hst] using hs1
  have hpos := (layoutWf_spec hwf).2
  have hD0p : 0 < D0 := by rw [hD0e]; exact hpos _ (by simp [hdx])
  have hD1p : 0 < D1 := by rw [hD1e]; exact hpos _ (by simp [hdx])
  have hN : L.denseLen = (D0 - 1) * s0 + D1 := by
    rw [denseLen_eq hwf, hdx, hst, ht1, hD0e, hD1e, hs0e]
    simp [packDot]
    have : 0 < x1 := by rw [← hD1e]; exact hD1p
    omega
  have hNle : L.denseLen ≤ D0 * s0 := by
    rw [hN]
    obtain ⟨k, hk⟩ : ∃ k, D0 = k + 1 := ⟨D0 - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
    omega
  -- absolute values
  have hBd : ∀ c ∈ d, -2 ^ l ≤ c ∧ c < 2 ^ l := by
    intro c hc
    have h1 := hs.bound c hc
    have h2 : (B : ℤ) < 2 ^ l := by exact_mod_cast hBl
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hA : packAbs w L.denseLen l Z = natPack w (d.map Int.natAbs) := by
    rw [← hs.pack, ← hs.len]
    exact packAbs_spec hlw rfl hBd
  set a : List ℤ := d.map fun c => ((c.natAbs : ℕ) : ℤ) with ha_def
  have hAcast : ((packAbs w L.denseLen l Z : ℕ) : ℤ) = packSum w a := by
    rw [hA, natPack_cast, List.map_map]; rfl
  set V := weightRevList W q L with hV
  have hVlen : V.length = D0 * s0 := length_weightRevList W q L
  have hVnn : ∀ x ∈ V, 0 ≤ x := by
    intro x hx
    simp only [hV, weightRevList, List.mem_flatten, List.mem_map] at hx
    obtain ⟨_, ⟨r, -, rfl⟩, hx⟩ := hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    positivity
  have hann : ∀ x ∈ a, 0 ≤ x := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    positivity
  -- no carry
  have hVb : ∀ x ∈ V, |x| ≤ ((listMax (rowsRev W q L) * listMax (colsRev W q L) : ℕ) : ℤ) := by
    intro x hx
    simp only [hV, weightRevList, List.mem_flatten, List.mem_map] at hx
    obtain ⟨_, ⟨r, hr, rfl⟩, hx⟩ := hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Nat.mul_le_mul (le_listMax hr) (le_listMax hc)
  have hab : ∀ x ∈ a, |x| ≤ ((2 ^ l : ℕ) : ℤ) := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have h1 := hs.bound c hc
    have h2 : (B : ℤ) ≤ ((2 ^ l : ℕ) : ℤ) := by exact_mod_cast hBl.le
    rw [Int.natCast_natAbs, abs_abs]
    linarith
  have hbound : ∀ c ∈ listConv a V, c < 2 ^ w := by
    intro c hc
    have h1 := listConv_abs_le hab hVb c hc
    have hmin : min a.length V.length ≤ D0 * s0 := (min_le_right _ _).trans hVlen.le
    have h2 : (min a.length V.length * 2 ^ l *
        (listMax (rowsRev W q L) * listMax (colsRev W q L)) : ℕ) < 2 ^ w := by
      refine lt_of_le_of_lt ?_ hcarry
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hmin)
    have h3 : ((min a.length V.length * 2 ^ l *
        (listMax (rowsRev W q L) * listMax (colsRev W q L)) : ℕ) : ℤ) < 2 ^ w := by
      exact_mod_cast h2
    push_cast at h1 h3
    linarith [le_abs_self c]
  have hX : ((packAbs w L.denseLen l Z * weightRev W q L : ℕ) : ℤ) =
      packSum w a * packSum w V := by
    push_cast; rw [hAcast, weightRev_cast]
  have hdot := dot_extract hann hVnn hbound hX (D0 * s0 - 1)
  have hnorm : (packNorm W q l L Z : ℤ) = (listConv a V).getD (D0 * s0 - 1) 0 := by
    unfold packNorm
    rw [hdot, Int.toNat_of_nonneg (getD_nonneg (listConv_nonneg hann hVnn) _)]
  have hdlen : d.length = L.denseLen := hs.len
  have hNpos : 0 < L.denseLen := by rw [hN]; omega
  have hs0p : 0 < s0 := lt_of_lt_of_le hD1p hD1
  have hM : 0 < D0 * s0 := Nat.mul_pos hD0p hs0p
  have hane : a ≠ [] := List.ne_nil_of_length_pos (by simp [ha_def, hdlen, hNpos])
  have hVne : V ≠ [] := List.ne_nil_of_length_pos (by rw [hVlen]; exact hM)
  have halen : a.length = L.denseLen := by simp [ha_def, hdlen]
  have hconv : (listConv a V).getD (D0 * s0 - 1) 0 =
      ∑ p ∈ Finset.range (D0 * s0), a.getD p 0 * (slotWeight W q L p : ℤ) := by
    rw [listConv_getD_eq hane hVne (by rw [halen, hVlen]; omega), Nat.sub_add_cancel hM]
    exact Finset.sum_congr rfl fun p hp => by
      rw [weightRevList_getD W q L (Finset.mem_range.mp hp)]
  have hag : ∀ i, (a.getD i 0 : ℝ) = |(d.getD i 0 : ℝ)| := by
    intro i
    by_cases hi : i < d.length
    · simp [ha_def, List.getD_eq_getElem?_getD, hi, Nat.cast_natAbs]
    · simp [ha_def, List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]
  have hq : (0 : ℝ) < 2 ^ (2 * q) := by positivity
  -- one slot
  have hslot : ∀ i, ‖(d.getD i 0 : ℂ) * character (certKeyFun n (keyOf L i)) θ‖ ≤
      (a.getD i 0 : ℝ) * (slotWeight W q L i : ℝ) / 2 ^ (2 * q) := by
    intro i
    rw [norm_mul, Complex.norm_intCast, hag]
    by_cases hdi : d.getD i 0 = 0
    · rw [hdi]; simp
    obtain ⟨u, hul, hult, hi⟩ := hs.box i hdi
    rw [hdx] at hul hult
    obtain ⟨u0, u1, rfl⟩ := List.length_eq_two.mp hul
    have hu0 : u0 < D0 := by have := hult 0 (by simp); simpa [hdx, hD0e] using this
    have hu1 : u1 < D1 := by have := hult 1 (by simp); simpa [hdx, hD1e] using this
    have hie : i = u0 * s0 + u1 := by rw [hi, hst, ht1, hs0e]; simp [packDot]
    have hdiv : i / s0 = u0 := by
      rw [hie, Nat.add_comm, Nat.add_mul_div_right _ _ hs0p, Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    have hmod : i % s0 = u1 := by
      rw [hie, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hkey : keyOf L i = [L.lo.getD 0 0 + (u0 : ℤ), L.lo.getD 1 0 + (u1 : ℤ)] := by
      rw [hi, keyOf_packDot hwf (by simp [hdx]) (by rw [hdx]; exact hult), hdx]
      rfl
    have hw : slotWeight W q L i =
        wCeil W q (L.lo.getD 0 0 + (u0 : ℤ)).natAbs * wCeil W q (L.lo.getD 1 0 + (u1 : ℤ)).natAbs := by
      unfold slotWeight
      rw [hdiv, hmod, ite_eq_left hu1]
    set e0 := (L.lo.getD 0 0 + (u0 : ℤ)).natAbs
    set e1 := (L.lo.getD 1 0 + (u1 : ℤ)).natAbs
    have hchi : ‖character (certKeyFun n (keyOf L i)) θ‖ ≤ (W.w : ℝ) ^ (e0 + e1) := by
      refine (norm_character_le_weight hW _ hθ).trans (pow_le_pow_right₀ hw1 ?_)
      refine (sum_natAbs_certKeyFun_le n _).trans ?_
      rw [hkey]
      simp [e0, e1]
    have hW2 : (W.w : ℝ) ^ (e0 + e1) * 2 ^ (2 * q) ≤ (slotWeight W q L i : ℝ) := by
      rw [hw, Nat.cast_mul, pow_add, two_mul, pow_add]
      have h0 := wCeil_ge hw0 q e0
      have h1 := wCeil_ge hw0 q e1
      have hw0R : (0 : ℝ) ≤ W.w := by exact_mod_cast hw0.le
      have p0 : (0 : ℝ) ≤ (W.w : ℝ) ^ e0 * 2 ^ q := by positivity
      calc (W.w : ℝ) ^ e0 * (W.w : ℝ) ^ e1 * (2 ^ q * 2 ^ q) =
          ((W.w : ℝ) ^ e0 * 2 ^ q) * ((W.w : ℝ) ^ e1 * 2 ^ q) := by ring
        _ ≤ (wCeil W q e0 : ℝ) * (wCeil W q e1 : ℝ) :=
          mul_le_mul h0 h1 (by positivity) (p0.trans h0)
    rw [le_div_iff₀ hq]
    calc |(d.getD i 0 : ℝ)| * ‖character (certKeyFun n (keyOf L i)) θ‖ * 2 ^ (2 * q)
        ≤ |(d.getD i 0 : ℝ)| * ((W.w : ℝ) ^ (e0 + e1) * 2 ^ (2 * q)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hchi hq.le) (abs_nonneg _)
      _ ≤ |(d.getD i 0 : ℝ)| * (slotWeight W q L i : ℝ) :=
          mul_le_mul_of_nonneg_left hW2 (abs_nonneg _)
  -- the sum
  have hnn : ∀ p, (0 : ℝ) ≤ (a.getD p 0 : ℝ) * (slotWeight W q L p : ℝ) / 2 ^ (2 * q) := by
    intro p; rw [hag]; positivity
  unfold slotSum
  calc ‖∑ i ∈ Finset.range d.length, (d.getD i 0 : ℂ) * character (certKeyFun n (keyOf L i)) θ‖
      ≤ ∑ i ∈ Finset.range d.length,
          (a.getD i 0 : ℝ) * (slotWeight W q L i : ℝ) / 2 ^ (2 * q) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hslot i)
    _ ≤ ∑ p ∈ Finset.range (D0 * s0), (a.getD p 0 : ℝ) * (slotWeight W q L p : ℝ) / 2 ^ (2 * q) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by rw [hdlen]; exact hNle)) fun p _ _ => hnn p
    _ = (packNorm W q l L Z : ℝ) / 2 ^ (2 * q) := by
        rw [← Finset.sum_div]
        congr 1
        have := congrArg (fun z : ℤ => (z : ℝ)) (hnorm.trans hconv)
        rw [show ((packNorm W q l L Z : ℕ) : ℝ) = ((packNorm W q l L Z : ℤ) : ℝ) by norm_cast,
          this]
        push_cast
        rfl


end KAM.CertificateSharp.Packed
