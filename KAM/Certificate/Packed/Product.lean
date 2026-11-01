/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Packed.Round
public import KAM.Certificate.Poly.MulPacked

/-!
# The packed real product: one multiplication, advice-free rounding, the landed contract

Integer Fourier data `x` laid out in a landed `PackLayout L` is represented by one signed integer
`Z = packSum w (L.dense x)` with a load bound `B` on its slots (`PRep L x B Z`). At the list
boundary `packOf` packs a term list once (the landed sparse packer `spPack`) and `packRepOk`
certifies the representation (`packRepOk_sound`).

A `GmpSpec` names the two layouts, the factor load bounds, the offset exponent `l` (the exact
product's slots are within `2^l`) and the rounding shift `s`. Its guard reads metadata only. Then:

* **exact product** (`GmpSpec.round_spec`): `Z_a Z_b = packSum w (listConv d_a d_b)`, every
  convolution slot is within `2^l`, and `GmpSpec.round` (one `Int.mul`, then `gmpRound`) packs the
  slots rounded to nearest multiples of `2^s`;
* **unpack ∘ product = convolution**: `unpackSlots` inverts the packing of the rounded slots, so
  `GmpSpec.terms` reads them back with the landed product keys (`intEval_gmpTerms`);
* **strip contract** (`GmpSpec.round_sound`, `gmpRealProduct_sound`): on the strip,
  `‖x · y - 2^s · terms‖ ≤ rem · 2^P2` with the a-priori remainder
  `rem = prodLen · 2^(s-1) · w^degCap / 2^P2` (`degCap` bounds every slot degree of the product
  window from the layouts alone). This is the proposition of the landed `packedRealProduct_sound`.
-/

@[expose] public section

namespace KAM.Certificate

open KAM

/-! ### Packed real data and the list boundary -/

/-- `Z` packs the dense slots of the integer Fourier data `x` in the layout `L`, every slot within
`B`. -/
def PRep (L : PackLayout) (x : List (CertKey × ℤ)) (B : ℕ) (Z : ℤ) : Prop :=
  ∃ d : List ℤ, L.dense x = some d ∧ packSum L.width d = Z ∧ ∀ c ∈ d, |c| ≤ (B : ℤ)

/-- The packing of a term list at the boundary (the landed balanced sparse packer). -/
def packOf (L : PackLayout) (x : List (CertKey × ℤ)) : ℤ := spPack L.width 0 (L.slotTerms x)

/-- The boundary check: every key has a slot, the slots strictly increase and lie below the dense
length, and every term is within `B`. -/
def packRepOk (L : PackLayout) (x : List (CertKey × ℤ)) (B : ℕ) : Bool :=
  L.allSlots x && packStrictAsc (L.slotTerms x) &&
    ((L.slotTerms x).all fun e => decide (e.1 < L.denseLen)) && decide (spMax (L.slotTerms x) ≤ B)

/-- The linear fill of strictly increasing terms packs to their sparse pack. -/
theorem packSum_packFill (w N : ℕ) {es : List (ℕ × ℤ)} (hs : es.Pairwise fun a b => a.1 < b.1)
    (hN : ∀ e ∈ es, e.1 < N) : packSum w (packFill N 0 es) = spPack w 0 es := by
  rw [packSum_eq_sum_of_length_le w (le_of_eq (packFill_length N 0 es))]
  rw [Finset.sum_congr rfl fun a _ => by rw [packFill_getD hs hN]]
  have hwin := sum_packSlotTotal_window ((2 : ℤ) ^ w) 0 N es
  simp only [Nat.zero_add] at hwin
  rw [hwin, spPack_eq w 0 es (by simp)]
  have hf : es.filter (fun e => decide (0 ≤ e.1) && decide (e.1 < N)) = es :=
    List.filter_eq_self.mpr fun e he => by simp [hN e he]
  rw [hf]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  rw [Nat.sub_zero, pow_mul]

theorem packRepOk_sound {L : PackLayout} {x : List (CertKey × ℤ)} {B : ℕ}
    (h : packRepOk L x B = true) : PRep L x B (packOf L x) := by
  simp only [packRepOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hall, hasc⟩, hlt⟩, hmax⟩ := h
  have hs := packStrictAsc_pairwise hasc
  refine ⟨_, PackLayout.dense_eq_packFill hall hasc, packSum_packFill _ _ hs hlt, fun c hc => ?_⟩
  rw [packFill_eq _ 0 _ hs (by simp), List.mem_map] at hc
  obtain ⟨p, -, rfl⟩ := hc
  have := natAbs_packSlotTotal_le hs (0 + p)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast this.trans hmax

/-! ### The specification of one packed product -/

/-- One packed real product: layouts, factor load bounds, offset exponent `l`, rounding shift
`s`. -/
structure GmpSpec where
  la : PackLayout
  lb : PackLayout
  ba : ℕ
  bb : ℕ
  l : ℕ
  s : ℕ

/-- The product window length `|d_a| + |d_b| - 1`. -/
def GmpSpec.prodLen (g : GmpSpec) : ℕ := g.la.denseLen + g.lb.denseLen - 1

/-- **Guard** (metadata only, no slot is read): compatible layouts (landed `compat`, which includes
equal widths), nonempty boxes, positive strides, the convolution bound
`min(N_a, N_b) B_a B_b ≤ 2^l`, and the rounding guard `1 ≤ s ≤ l`, `l + 2 ≤ w`. -/
def GmpSpec.guard (g : GmpSpec) : Bool :=
  PackLayout.compat g.la.dims.length g.la g.lb && decide (0 < g.la.denseLen) &&
    decide (0 < g.lb.denseLen) && (g.la.stride.all fun s => decide (0 < s)) &&
    decide (min g.la.denseLen g.lb.denseLen * g.ba * g.bb ≤ 2 ^ g.l) &&
    decide (1 ≤ g.s) && decide (g.s ≤ g.l) && decide (g.l + 2 ≤ g.la.width)

/-- **The packed product**: one multiplication, then advice-free rounding of every slot. -/
def GmpSpec.round (g : GmpSpec) (Za Zb : ℤ) : ℤ :=
  gmpRound g.la.width g.prodLen g.l g.s (Za * Zb)

theorem GmpSpec.guard_spec {g : GmpSpec} (hg : g.guard = true) :
    PackLayout.compat g.la.dims.length g.la g.lb = true ∧ 0 < g.la.denseLen ∧
      0 < g.lb.denseLen ∧ (∀ s ∈ g.la.stride, 0 < s) ∧
      min g.la.denseLen g.lb.denseLen * g.ba * g.bb ≤ 2 ^ g.l ∧ 1 ≤ g.s ∧ g.s ≤ g.l ∧
      g.l + 2 ≤ g.la.width := by
  simp only [GmpSpec.guard, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨hc, ha⟩, hb⟩, hst⟩, hbd⟩, hs⟩, hsl⟩, hlw⟩ := hg
  exact ⟨hc, ha, hb, hst, hbd, hs, hsl, hlw⟩

theorem compat_width {m : ℕ} {La Lb : PackLayout} (h : PackLayout.compat m La Lb = true) :
    La.width = Lb.width := by
  simp only [PackLayout.compat, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

/-- Every slot of the exact convolution is within `min(|a|, |b|) · B_a · B_b`. -/
theorem listConv_abs_le {a b : List ℤ} {Ba Bb : ℕ} (ha : ∀ c ∈ a, |c| ≤ (Ba : ℤ))
    (hb : ∀ c ∈ b, |c| ≤ (Bb : ℤ)) :
    ∀ c ∈ listConv a b, |c| ≤ ((min a.length b.length * Ba * Bb : ℕ) : ℤ) := by
  intro c hc
  unfold listConv at hc
  split_ifs at hc with he
  · simp at hc
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hc
  rw [sum_map_range_eq]
  have hma : maxAbs a ≤ Ba := maxAbs_le_of_forall fun c hc => by
    have := ha c hc; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  have hmb : maxAbs b ≤ Bb := maxAbs_le_of_forall fun c hc => by
    have := hb c hc; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  refine (abs_conv_entry_le a b k).trans ?_
  have h1 : (maxAbs a : ℤ) ≤ Ba := by exact_mod_cast hma
  have h2 : (maxAbs b : ℤ) ≤ Bb := by exact_mod_cast hmb
  have h0 : (0 : ℤ) ≤ (min a.length b.length : ℕ) := by positivity
  have h3 : (0 : ℤ) ≤ maxAbs a := by positivity
  have h4 : (0 : ℤ) ≤ Bb := by positivity
  calc ((min a.length b.length : ℕ) : ℤ) * maxAbs a * maxAbs b
      ≤ ((min a.length b.length : ℕ) : ℤ) * maxAbs a * Bb :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg h0 h3)
    _ ≤ ((min a.length b.length : ℕ) : ℤ) * Ba * Bb :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h0) h4
    _ = ((min a.length b.length * Ba * Bb : ℕ) : ℤ) := by push_cast; ring

/-- **Exact packed product and its rounding.** The product of the packings is the packing of the
exact convolution (every slot within `2^l`), and `GmpSpec.round` packs its slots rounded to the
nearest multiples of `2^s`. -/
theorem GmpSpec.round_spec {g : GmpSpec} (hg : g.guard = true) {x y : List (CertKey × ℤ)}
    {Za Zb : ℤ} (ha : PRep g.la x g.ba Za) (hb : PRep g.lb y g.bb Zb) :
    ∃ da db : List ℤ, g.la.dense x = some da ∧ g.lb.dense y = some db ∧
      (listConv da db).length = g.prodLen ∧ (∀ c ∈ listConv da db, |c| ≤ 2 ^ g.l) ∧
      Za * Zb = packSum g.la.width (listConv da db) ∧
      g.round Za Zb = packSum g.la.width ((listConv da db).map (roundSlot g.s)) := by
  obtain ⟨hc, hpa, hpb, -, hbd, hs, hsl, hlw⟩ := GmpSpec.guard_spec hg
  obtain ⟨da, hda, hZa, hBa⟩ := ha
  obtain ⟨db, hdb, hZb, hBb⟩ := hb
  have hla := PackLayout.dense_length hda
  have hlb := PackLayout.dense_length hdb
  have hw := compat_width hc
  have hprod : Za * Zb = packSum g.la.width (listConv da db) := by
    rw [packSum_listConv, ← hZa, ← hZb, hw]
  have hlen : (listConv da db).length = g.prodLen := by
    rw [listConv_length (List.ne_nil_of_length_pos (hla ▸ hpa))
      (List.ne_nil_of_length_pos (hlb ▸ hpb)), GmpSpec.prodLen, hla, hlb]
  have hbound : ∀ c ∈ listConv da db, |c| ≤ 2 ^ g.l := fun c hcm => by
    refine (listConv_abs_le hBa hBb c hcm).trans ?_
    rw [hla, hlb]
    exact_mod_cast hbd
  refine ⟨da, db, hda, hdb, hlen, hbound, hprod, ?_⟩
  rw [GmpSpec.round, hprod, ← hlen]
  exact gmpRound_spec hs hsl hlw rfl hbound

/-! ### Reading the rounded product back -/

/-- The keyed nonzero entry of an indexed product slot (the landed product key). -/
def gmpEntry (la lb : PackLayout) (ic : ℕ × ℤ) : Option (CertKey × ℤ) :=
  if ic.2 = 0 then none else some (la.prodKey lb ic.1, ic.2)

/-- The integer Fourier data of a rounded packed product: its unpacked slots with their product
keys, zeros dropped (only the list boundary needs it; packed consumers never compute it). -/
def GmpSpec.terms (g : GmpSpec) (R : ℤ) : List (CertKey × ℤ) :=
  ((List.range g.prodLen).zip (unpackSlots g.la.width g.prodLen R)).filterMap (gmpEntry g.la g.lb)

theorem intEval_gmpEntry (la lb : PackLayout) (n : ℕ) (θ : Fin n → ℂ) :
    ∀ (cs : List ℤ) (k : ℕ), intEval n (((List.range' k cs.length).zip cs).filterMap
      (gmpEntry la lb)) θ = ∑ j ∈ Finset.range cs.length,
        (cs.getD j 0 : ℂ) * character (certKeyFun n (la.prodKey lb (k + j))) θ
  | [], k => by simp [intEval_nil]
  | c :: cs, k => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have ih := intEval_gmpEntry la lb n θ cs (k + 1)
    simp only [show ∀ j, k + 1 + j = k + (j + 1) from fun j => by omega] at ih
    by_cases hc : c = 0
    · rw [List.filterMap_cons_none (by simp [gmpEntry, hc]), ih, hc]
      simp
    · rw [List.filterMap_cons_some (b := (la.prodKey lb k, c)) (by simp [gmpEntry, hc]),
        intEval_cons, ih, add_comm]

/-- **Unpack ∘ packed product**: the terms read back from the packed rounded product are the
rounded convolution slots with their product keys. -/
theorem intEval_gmpTerms {g : GmpSpec} {rs : List ℤ} (hw : 0 < g.la.width)
    (hlen : rs.length = g.prodLen) (hb : SlotsBounded g.la.width rs) (n : ℕ) (θ : Fin n → ℂ) :
    intEval n (g.terms (packSum g.la.width rs)) θ = ∑ j ∈ Finset.range g.prodLen,
      (rs.getD j 0 : ℂ) * character (certKeyFun n (g.la.prodKey g.lb j)) θ := by
  unfold GmpSpec.terms
  rw [← hlen, unpackSlots_packSum hw hb, List.range_eq_range', intEval_gmpEntry]
  simp

/-! ### The a-priori remainder -/

/-- Caps of the mixed-radix digits of the slots below `N`: `(N - 1)/s₀`, then
`(s_j - 1)/s_{j+1}`. -/
def digitCaps : List ℕ → ℕ → List ℕ
  | [], _ => []
  | s :: ss, N => (N - 1) / s :: digitCaps ss s

theorem packDigits_le_caps : ∀ (ss : List ℕ) (N i : ℕ), (∀ s ∈ ss, 0 < s) → i < N →
    ∀ j, (packDigits ss i).getD j 0 ≤ (digitCaps ss N).getD j 0
  | [], _, _, _, _, j => by simp [packDigits, digitCaps]
  | s :: ss, N, i, _, hi, 0 => by
    simp only [packDigits, digitCaps, List.getD_cons_zero]
    exact Nat.div_le_div_right (by omega)
  | s :: ss, _, i, hs, _, j + 1 => by
    simp only [packDigits, digitCaps, List.getD_cons_succ]
    exact packDigits_le_caps ss s (i % s) (fun x hx => hs x (by simp [hx]))
      (Nat.mod_lt _ (hs s (by simp))) j

/-- The `ℓ¹` size of the key of product slot `i`. -/
def prodDeg (la lb : PackLayout) (i : ℕ) : ℕ := ((la.prodKey lb i).map Int.natAbs).sum

/-- The low corner of the product window on axis `j`. -/
def GmpSpec.loSum (g : GmpSpec) (j : ℕ) : ℤ := g.la.lo.getD j 0 + g.lb.lo.getD j 0

/-- A bound on the `ℓ¹` size of every key of the product window, from the layouts alone. -/
def GmpSpec.degCap (g : GmpSpec) : ℕ :=
  ((List.range g.la.dims.length).map fun j =>
    max (g.loSum j).natAbs
      (g.loSum j + ((digitCaps g.la.stride g.prodLen).getD j 0 : ℤ)).natAbs).sum

theorem natAbs_add_le_max (a : ℤ) {d c : ℕ} (hd : d ≤ c) :
    (a + d).natAbs ≤ max a.natAbs (a + c).natAbs := by
  rcases le_or_gt 0 (a + d) with h | h
  · exact le_max_of_le_right (by omega)
  · exact le_max_of_le_left (by omega)

theorem prodDeg_le_degCap (g : GmpSpec) (hst : ∀ s ∈ g.la.stride, 0 < s) {i : ℕ}
    (hi : i < g.prodLen) : prodDeg g.la g.lb i ≤ g.degCap := by
  unfold prodDeg GmpSpec.degCap PackLayout.prodKey
  rw [List.map_map]
  refine List.sum_le_sum fun j _ => ?_
  simp only [Function.comp_apply]
  exact natAbs_add_le_max _ (packDigits_le_caps g.la.stride g.prodLen i hst hi j)

/-- The a-priori remainder of a rounded packed product (scaled by `2^P2`). -/
def GmpSpec.rem (g : GmpSpec) (W : CertWeight) (P2 : ℕ) : ℚ :=
  ((g.prodLen * 2 ^ (g.s - 1) : ℕ) : ℚ) * W.w ^ g.degCap / 2 ^ P2

/-! ### The strip contract -/

/-- **Strip contract of the packed product** (packed factors): the exact product of the two integer
Fourier sums is `2^s` times the read-back rounded product up to `rem · 2^P2` on the strip. -/
theorem GmpSpec.round_sound {g : GmpSpec} (hg : g.guard = true) {x y : List (CertKey × ℤ)}
    {Za Zb : ℤ} (ha : PRep g.la x g.ba Za) (hb : PRep g.lb y g.bb Zb) {W : CertWeight}
    {s N : ℕ} (hW : checkWeight W s N = true) (P2 : ℕ) {n : ℕ} {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) :
    ‖intEval n x θ * intEval n y θ - 2 ^ g.s * intEval n (g.terms (g.round Za Zb)) θ‖ ≤
      ((g.rem W P2 : ℚ) : ℝ) * 2 ^ P2 := by
  obtain ⟨hc, -, -, hst, -, hs, -, hlw⟩ := GmpSpec.guard_spec hg
  obtain ⟨da, db, hda, hdb, hlen, hbound, -, hR⟩ := GmpSpec.round_spec hg ha hb
  set conv := listConv da db with hconv
  set rs := conv.map (roundSlot g.s) with hrs
  have hw : 0 < g.la.width := by omega
  have hrsl : rs.length = g.prodLen := by rw [hrs, List.length_map, hlen]
  have hrb : SlotsBounded g.la.width rs := by
    intro r hr
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hr
    have h1 := roundSlot_abs_le hs (hbound c hcm)
    have h2 : (2 : ℤ) * 2 ^ g.l < 2 ^ g.la.width := by
      calc (2 : ℤ) * 2 ^ g.l = 2 ^ (g.l + 1) := by ring
        _ < 2 ^ g.la.width := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  have hw1 := CertWeight.one_le_w hW
  rw [hR, intEval_gmpTerms hw hrsl hrb, PackLayout.intEval_mul_of_compat hc hda hdb θ,
    list_sum_map_range_eq, ← hconv, hlen, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- the remainder, slot by slot
  have hrem : ((g.rem W P2 : ℚ) : ℝ) * 2 ^ P2 =
      ∑ _i ∈ Finset.range g.prodLen, (2 : ℝ) ^ (g.s - 1) * (W.w : ℝ) ^ g.degCap := by
    rw [GmpSpec.rem, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  rw [hrem]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' := Finset.mem_range.mp hi
  have hci : i < conv.length := hlen ▸ hi'
  have hget : rs.getD i 0 = roundSlot g.s (conv.getD i 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hrs, List.getElem?_map,
      List.getElem?_eq_getElem hci]
    rfl
  have hdiff : (conv.getD i 0 : ℂ) * character (certKeyFun n (g.la.prodKey g.lb i)) θ -
      2 ^ g.s * ((rs.getD i 0 : ℂ) * character (certKeyFun n (g.la.prodKey g.lb i)) θ) =
      ((conv.getD i 0 - 2 ^ g.s * rs.getD i 0 : ℤ) : ℂ) *
        character (certKeyFun n (g.la.prodKey g.lb i)) θ := by
    push_cast
    ring
  rw [hdiff, norm_mul, Complex.norm_intCast, hget]
  have herr : |((conv.getD i 0 - 2 ^ g.s * roundSlot g.s (conv.getD i 0) : ℤ) : ℝ)| ≤
      (2 : ℝ) ^ (g.s - 1) := by
    rw [← Int.cast_abs]
    exact_mod_cast round_err hs (conv.getD i 0)
  have hchi : ‖character (certKeyFun n (g.la.prodKey g.lb i)) θ‖ ≤ (W.w : ℝ) ^ g.degCap :=
    (norm_character_le_weight hW _ hθ).trans
      (pow_le_pow_right₀ hw1 ((sum_natAbs_certKeyFun_le n _).trans
        (prodDeg_le_degCap g hst hi')))
  exact mul_le_mul herr hchi (norm_nonneg _) (by positivity)

/-! ### The landed signature -/

/-- **The packed real product with the landed signature** (`packedRealProduct`'s, with a spec in
place of the advice): an empty factor is the exact zero product; otherwise the factors are packed
at the boundary (`packOf`, checked by `packRepOk`), multiplied once, rounded without advice, and
read back. The remainder is the a-priori `GmpSpec.rem`. -/
def gmpRealProduct (g : GmpSpec) (W : CertWeight) (P2 : ℕ) (x y : List (CertKey × ℤ)) :
    Option (List (CertKey × ℤ) × ℚ) :=
  if x.isEmpty || y.isEmpty then some ([], 0) else
    if g.guard && packRepOk g.la x g.ba && packRepOk g.lb y g.bb then
      some (g.terms (g.round (packOf g.la x) (packOf g.lb y)), g.rem W P2)
    else none

/-- **Bridge B1 (real part)**: the packed product proves the proposition of the landed
`packedRealProduct_sound`, with `2^s` for `2^scale`. -/
theorem gmpRealProduct_sound {g : GmpSpec} {W : CertWeight} {P2 : ℕ}
    {x y : List (CertKey × ℤ)} {out : List (CertKey × ℤ) × ℚ}
    (h : gmpRealProduct g W P2 x y = some out) {s N : ℕ} (hW : checkWeight W s N = true)
    {n : ℕ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n W.rho) :
    ‖intEval n x θ * intEval n y θ - 2 ^ g.s * intEval n out.1 θ‖ ≤
      ((out.2 : ℚ) : ℝ) * 2 ^ P2 := by
  unfold gmpRealProduct at h
  split_ifs at h with hemp hck
  · simp only [Option.some.injEq] at h
    subst h
    rcases Bool.or_eq_true_iff.mp hemp with he | he <;>
      simp [List.isEmpty_iff.mp he, intEval_nil]
  · simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hck
    obtain ⟨⟨hg, hx⟩, hy⟩ := hck
    exact GmpSpec.round_sound hg (packRepOk_sound hx) (packRepOk_sound hy) hW P2 hθ

end KAM.Certificate
