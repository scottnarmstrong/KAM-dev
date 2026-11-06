/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Trig.Product
public import KAM.CertificateSharp.Packed.Round

/-!
# Packed products of trigonometric polynomials (T2-CONF, N3)

A polynomial's slot list `d` (dense square layout of stride `S`) is packed into ONE integer
`packSum w d = Σ_i d_i 2^{w i}` (`KAM.Certificate.Poly.Packed`, signed slots of width `w`); a
product of two polynomials is ONE big-integer multiplication (`packSum_listConv`), and the product's
slots are read back by `unpackSlots` (offset digits, balanced mask-and-shift reading;
`KAM.CertificateSharp.Packed.Round`). In the kernel every step is a GMP operation on `Nat`.

The data are packed integers, and a model's slot list is **defined** by decoding:
`unpackSlots w N Z`. The packing round-trips on every integer whose offset form fits `N` slots
(`packSum_unpackSlots`), so the kernel product of two literals decodes to the convolution of the
decoded lists (`unpackSlots_mul`) under the explicit no-overflow condition `convFits` (or its
a-priori form `convFits_of_le`: `2 · min(N_a, N_b) · B_a · B_b < 2^w` with slot bounds `B_a`,
`B_b`; or `convFitsL1`).

Main result, `evalK_unpackSlots_mul`: the real product of two decoded models is `psgn (p ∧ q)`
times the model decoded from the product of the two packed integers, on the layout of half-width
`C_a + C_b`.

Signed literals: `zOf neg n` (a sign and a magnitude), so the kernel multiplies one pair of
naturals per product (`Int.mul` reduces to one `Nat.mul`).
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open KAM.Certificate KAM.CertificateSharp.Packed

/-- A signed integer from a sign bit and a natural magnitude (the literal form of packed data). -/
def zOf (neg : Bool) (n : ℕ) : ℤ := if neg then -(n : ℤ) else n

/-- The offset of `N` signed slots of width `w`: `Σ_{i<N} 2^(w-1) 2^(w i)`. -/
def slotOff (w N : ℕ) : ℕ := periodic w N (2 ^ (w - 1))

/-- The decodability condition of a packed integer: its offset form is a natural number below
`2^(w N)` (decidable; one addition and one comparison in the kernel). -/
def packOk (w N : ℕ) (Z : ℤ) : Bool :=
  decide (0 ≤ Z + slotOff w N) && decide (Z + slotOff w N < 2 ^ (w * N))

/-! ### Decoding round trips -/

theorem natDigitsLin_length (w : ℕ) : ∀ N Y : ℕ, (natDigitsLin w N Y).length = N
  | 0, _ => rfl
  | N + 1, Y => by simp [natDigitsLin, natDigitsLin_length w N]

theorem natDigitsSh_length (w : ℕ) : ∀ f N Y : ℕ, (natDigitsSh w f N Y).length = N
  | 0, N, Y => natDigitsLin_length w N Y
  | f + 1, N, Y => by
    rw [natDigitsSh]
    split_ifs
    · exact natDigitsLin_length w N Y
    · rw [List.length_append, natDigitsSh_length w f, natDigitsSh_length w f]
      omega

theorem length_unpackSlots (w N : ℕ) (Z : ℤ) : (unpackSlots w N Z).length = N := by
  simp [unpackSlots, natDigitsSh_length]

/-- **Packing inverts decoding** on every integer accepted by `packOk`. -/
theorem packSum_unpackSlots {w N : ℕ} (hw : 0 < w) {Z : ℤ} (h : packOk w N Z = true) :
    packSum w (unpackSlots w N Z) = Z := by
  simp only [packOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  set X : ℕ := (Z + slotOff w N).toNat with hX
  have hXZ : (X : ℤ) = Z + slotOff w N := Int.toNat_of_nonneg h0
  have hXlt : X < 2 ^ (w * N) := by
    have : (X : ℤ) < ((2 ^ (w * N) : ℕ) : ℤ) := by rw [hXZ]; exact_mod_cast h1
    exact_mod_cast this
  obtain ⟨es, hlen, hdig, hpack⟩ := natPack_digits w N X hXlt
  have hdec : unpackSlots w N Z = es.map fun e : ℕ => (e : ℤ) - 2 ^ (w - 1) := by
    unfold unpackSlots
    rw [show (Z + (periodic w N (2 ^ (w - 1)) : ℤ)).toNat = X from rfl, ← hpack, ← hlen,
      natDigitsSh_natPack w 64 es hdig]
  rw [hdec]
  have hnn : ∀ c ∈ es.map (fun e : ℕ => (e : ℤ) - 2 ^ (w - 1)),
      0 ≤ c + ((2 ^ (w - 1) : ℕ) : ℤ) := by
    intro c hc
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hc
    push_cast
    linarith [(Nat.cast_nonneg e : (0 : ℤ) ≤ e)]
  have hsum := packSum_add_periodic w (2 ^ (w - 1)) _ hnn
  have hmap : ((es.map fun e : ℕ => (e : ℤ) - 2 ^ (w - 1)).map
      fun c : ℤ => (c + ((2 ^ (w - 1) : ℕ) : ℤ)).toNat) = es := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id es]
    refine List.map_congr_left fun e _ => ?_
    simp
  rw [hmap, hpack, List.length_map, hlen, ← periodic_cast hw] at hsum
  have : (X : ℤ) = Z + (periodic w N (2 ^ (w - 1)) : ℤ) := hXZ
  push_cast at hsum
  linarith

/-! ### The no-overflow condition -/

theorem maxAbs_le {cs : List ℤ} {B : ℕ} (h : ∀ c ∈ cs, |c| ≤ (B : ℤ)) : maxAbs cs ≤ B := by
  induction cs with
  | nil => simp [maxAbs]
  | cons c cs ih =>
    rw [maxAbs, List.foldr_cons]
    refine max_le ?_ (ih fun x hx => h x (by simp [hx]))
    have := h c (by simp)
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this

/-- **The explicit width condition**: slot bounds `B_a`, `B_b` and `2 · min(N_a, N_b) · B_a · B_b <
2^w` make the convolution fit the slots. -/
theorem convFits_of_le {w : ℕ} {a b : List ℤ} {Ba Bb : ℕ} (ha : ∀ c ∈ a, |c| ≤ (Ba : ℤ))
    (hb : ∀ c ∈ b, |c| ≤ (Bb : ℤ)) (h : 2 * min a.length b.length * Ba * Bb < 2 ^ w) :
    convFits w a b = true := by
  simp only [convFits, decide_eq_true_eq]
  calc 2 * min a.length b.length * maxAbs a * maxAbs b
      ≤ 2 * min a.length b.length * Ba * Bb := by
        have h1 := maxAbs_le ha
        have h2 := maxAbs_le hb
        gcongr
    _ < 2 ^ w := h

/-- Every convolution slot is at most `ℓ¹(a) · max |b|`. -/
theorem abs_listConv_getD_le (a b : List ℤ) (m : ℕ) :
    |(listConv a b).getD m 0| ≤ l1 a * (maxAbs b : ℤ) := by
  by_cases hae : a = []
  · subst hae
    simp only [listConv, List.isEmpty_nil, Bool.true_or, ↓reduceIte, List.getD_nil, abs_zero]
    exact mul_nonneg (l1_nonneg _) (by positivity)
  by_cases hbe : b = []
  · subst hbe
    simp only [listConv, List.isEmpty_nil, Bool.or_true, ↓reduceIte, List.getD_nil, abs_zero]
    exact mul_nonneg (l1_nonneg a) (by positivity)
  by_cases hm : m < a.length + b.length - 1
  · rw [listConv_getD hae hbe hm, l1_eq]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ Finset.range (m + 1), |a.getD p 0 * b.getD (m - p) 0|
        ≤ ∑ p ∈ Finset.range (m + 1), |a.getD p 0| * (maxAbs b : ℤ) :=
          Finset.sum_le_sum fun p _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (abs_getD_le b _) (abs_nonneg _)
      _ ≤ ∑ p ∈ Finset.range (max (m + 1) a.length), |a.getD p 0| * (maxAbs b : ℤ) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (le_max_left _ _)) fun _ _ _ => by positivity
      _ = ∑ p ∈ Finset.range a.length, |a.getD p 0| * (maxAbs b : ℤ) := by
          refine (Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _))
            fun p _ hp => ?_).symm
          rw [Finset.mem_range, not_lt] at hp
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hp]
      _ = (∑ p ∈ Finset.range a.length, |a.getD p 0|) * (maxAbs b : ℤ) := by
          rw [Finset.sum_mul]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [length_listConv hae hbe]; omega)]
    simp only [Option.getD_none, abs_zero]
    exact mul_nonneg (l1_nonneg a) (by positivity)

/-- The `ℓ¹` form of the no-overflow condition, with an explicit slot bound `M_b` of `b` checked
slotwise (`List.all`, kernel tail-recursive): `2 · ℓ¹(a) · M_b < 2^w`. -/
def convFitsL1 (w Mb : ℕ) (a b : List ℤ) : Bool :=
  decide (2 * l1 a * (Mb : ℤ) < 2 ^ w) && b.all fun c => decide (c.natAbs ≤ Mb)

theorem slotsBounded_listConv_of_l1 {w Mb : ℕ} {a b : List ℤ} (h : convFitsL1 w Mb a b = true) :
    SlotsBounded w (listConv a b) := by
  intro c hc
  simp only [convFitsL1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hM : maxAbs b ≤ Mb := maxAbs_le fun c hc => by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h.2 c hc
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
  have := abs_listConv_getD_le a b m
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some] at this
  have h2 : l1 a * (maxAbs b : ℤ) ≤ l1 a * (Mb : ℤ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hM) (l1_nonneg a)
  linarith [h.1]

/-- **Decode of a packed product is the convolution** (unpack ∘ product = convolution), whenever
the convolution fits the slots (`convFits`, `convFitsL1`, `convFits_of_le`). -/
theorem unpackSlots_mul {w Na Nb : ℕ} (hw : 0 < w) (hNa : 0 < Na) (hNb : 0 < Nb) {Za Zb : ℤ}
    (ha : packOk w Na Za = true) (hb : packOk w Nb Zb = true)
    (hfit : SlotsBounded w (listConv (unpackSlots w Na Za) (unpackSlots w Nb Zb))) :
    unpackSlots w (Na + Nb - 1) (Za * Zb) =
      listConv (unpackSlots w Na Za) (unpackSlots w Nb Zb) := by
  have hl : (listConv (unpackSlots w Na Za) (unpackSlots w Nb Zb)).length = Na + Nb - 1 := by
    rw [length_listConv, length_unpackSlots, length_unpackSlots]
    · rw [← List.length_pos_iff, length_unpackSlots]; exact hNa
    · rw [← List.length_pos_iff, length_unpackSlots]; exact hNb
  conv_lhs => rw [← packSum_unpackSlots hw ha, ← packSum_unpackSlots hw hb,
    ← packSum_listConv, ← hl]
  exact unpackSlots_packSum hw hfit

/-- **The packed product of two models.** For models decoded from packed integers `Z_a` (layout
`C_a`) and `Z_b` (layout `C_b`, symmetric of parity `q`), on a common stride without row wrap and
with zero padding, the real product is `psgn (p ∧ q)` times the model decoded from `Z_a · Z_b` on
the layout `C_a + C_b`. -/
theorem evalK_unpackSlots_mul {w Ca Cb S : ℕ} {p q : Bool} {Za Zb : ℤ} (hw : 0 < w)
    (hS : 2 * (Ca + Cb) < S)
    (ha : packOk w (Layout.len Ca S) Za = true) (hb : packOk w (Layout.len Cb S) Zb = true)
    (hfit : SlotsBounded w (listConv (unpackSlots w (Layout.len Ca S) Za)
      (unpackSlots w (Layout.len Cb S) Zb)))
    (hca : colsOk Ca S (unpackSlots w (Layout.len Ca S) Za) = true)
    (hcb : colsOk Cb S (unpackSlots w (Layout.len Cb S) Zb) = true)
    (hsb : symOk q (unpackSlots w (Layout.len Cb S) Zb) = true) (φ : Fin 2 → ℝ) :
    evalK (Layout.key Ca S) p (unpackSlots w (Layout.len Ca S) Za) φ *
        evalK (Layout.key Cb S) q (unpackSlots w (Layout.len Cb S) Zb) φ =
      (psgn (p && q) : ℝ) * evalK (Layout.key (Ca + Cb) S) (xor p q)
        (unpackSlots w (Layout.len (Ca + Cb) S) (Za * Zb)) φ := by
  have hlen : Layout.len (Ca + Cb) S = Layout.len Ca S + Layout.len Cb S - 1 := by
    unfold Layout.len; rw [Nat.mul_add, add_mul]; omega
  rw [evalK_mul hS hca hcb (length_unpackSlots _ _ _) hsb φ, hlen,
    unpackSlots_mul hw (Layout.len_pos _ _) (Layout.len_pos _ _) ha hb hfit]

end KAM.EffectiveStability.Tube

end
