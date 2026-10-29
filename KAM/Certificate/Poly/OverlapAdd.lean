/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.Advice

/-!
# Soundness of a packed product: the overlap-add glue

The exact convolution of two dense factors is the overlap-add of the exact shard windows
(`listConv_eq_overlapAdd`): both sides pack to the same integer at EVERY width (Kronecker
substitution, the shard decomposition and the packing of an overlap-add), so they agree by
injectivity at a width larger than all their slots. The advice windows are overlap-added the same
way (`PackedAdvice.combined`), and every product slot lies in at most two windows, each erring by
at most `2^(scale - 1)` on the target box (`checkShard_sound`) and `2^outLog` elsewhere; with
`1 ≤ scale` this gives `checkPackedProduct_sound`. Off the target the advice is zero
(`shapeOK`), so there the exact slot itself is small.
-/

@[expose] public section

namespace KAM.Certificate

/-! ### Zero padding, slotwise sums and the overlap-add -/

theorem packSum_replicate_zero (w n : ℕ) : packSum w (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, packSum_cons, ih]; ring

theorem packSum_append_replicate_zero (w : ℕ) (l : List ℤ) (n : ℕ) :
    packSum w (l ++ List.replicate n 0) = packSum w l := by
  rw [packSum_append, packSum_replicate_zero, mul_zero, add_zero]

theorem getD_append_replicate_zero (l : List ℤ) (n k : ℕ) :
    (l ++ List.replicate n 0).getD k 0 = l.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hk : k < l.length
  · rw [List.getElem?_append_left hk]
  · rw [List.getElem?_append_right (not_lt.mp hk), List.getElem?_eq_none (not_lt.mp hk),
      List.getElem?_replicate]
    split_ifs <;> rfl

theorem getD_replicate_zero_append (L : ℕ) (z : List ℤ) (k : ℕ) :
    (List.replicate L 0 ++ z).getD k 0 = if k < L then 0 else z.getD (k - L) 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with hk
  · rw [List.getElem?_append_left (by simpa using hk), List.getElem?_replicate]
    simp [hk]
  · rw [List.getElem?_append_right (by simpa using not_lt.mp hk), List.length_replicate]

theorem packAddZ_getD : ∀ (x y : List ℤ) (k : ℕ),
    (packAddZ x y).getD k 0 = x.getD k 0 + y.getD k 0
  | [], y, k => by simp [packAddZ]
  | a :: x, [], k => by simp [packAddZ]
  | a :: x, b :: y, 0 => by simp [packAddZ]
  | a :: x, b :: y, k + 1 => by
    rw [packAddZ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
      packAddZ_getD x y k]

theorem packSum_packAddZ (w : ℕ) : ∀ (x y : List ℤ),
    packSum w (packAddZ x y) = packSum w x + packSum w y
  | [], y => by simp [packAddZ, packSum_nil]
  | a :: x, [] => by simp [packAddZ, packSum_nil]
  | a :: x, b :: y => by
    rw [packAddZ, packSum_cons, packSum_cons, packSum_cons, packSum_packAddZ w x y]
    ring

theorem packOverlapAdd_cons_getD (L : ℕ) (x : List ℤ) (xs : List (List ℤ)) (k : ℕ) :
    (packOverlapAdd L (x :: xs)).getD k 0 =
      x.getD k 0 + if k < L then 0 else (packOverlapAdd L xs).getD (k - L) 0 := by
  rw [packOverlapAdd, packAddZ_getD, getD_replicate_zero_append]

/-- The packing of an overlap-add is the shifted sum of the window packings. -/
theorem packSum_packOverlapAdd (w L : ℕ) : ∀ ws : List (List ℤ),
    packSum w (packOverlapAdd L ws) =
      ∑ s ∈ Finset.range ws.length, 2 ^ (w * L * s) * packSum w (ws.getD s [])
  | [] => by simp [packOverlapAdd, packSum_nil]
  | x :: xs => by
    rw [packOverlapAdd, packSum_packAddZ, packSum_append, packSum_replicate_zero, zero_add,
      List.length_replicate, packSum_packOverlapAdd w L xs, List.length_cons,
      Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_zero, List.getD_cons_succ, mul_zero, pow_zero, one_mul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show w * L * (s + 1) = w * L + w * L * s by ring, pow_add]
    ring

/-- **At most two windows per slot.** If window `s` (at offset `o + s·L`) differs from the
`c`-scaled second window by at most `F` at its global slot (and both vanish past `2L - 1`), the
overlap-added difference is at most `2 F`, and at most `F` on the first `L` slots. -/
theorem packOverlapAdd_sub_abs_le {L : ℕ} (hL : 0 < L) (c : ℤ) (F : ℕ → ℤ)
    (hF : ∀ k, 0 ≤ F k) : ∀ (xs ys : List (List ℤ)) (o : ℕ), xs.length = ys.length →
    (∀ s < xs.length, ∀ m, |(xs.getD s []).getD m 0 - c * (ys.getD s []).getD m 0| ≤
      if m < 2 * L - 1 then F (o + s * L + m) else 0) →
    ∀ k, |(packOverlapAdd L xs).getD k 0 - c * (packOverlapAdd L ys).getD k 0| ≤ 2 * F (o + k) ∧
      (k < L → |(packOverlapAdd L xs).getD k 0 - c * (packOverlapAdd L ys).getD k 0| ≤ F (o + k))
  | [], [], o, _, _, k => by
    simp only [packOverlapAdd, List.getD_nil, mul_zero, sub_self, abs_zero]
    exact ⟨by linarith [hF (o + k)], fun _ => hF _⟩
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | x :: xs, y :: ys, o, hl, hw, k => by
    have h0 := hw 0 (by simp)
    simp only [List.getD_cons_zero, Nat.zero_mul, Nat.add_zero] at h0
    have ih := packOverlapAdd_sub_abs_le hL c F hF xs ys (o + L) (by simpa using hl)
      fun s hs m => by
        have := hw (s + 1) (by simp; omega) m
        simp only [List.getD_cons_succ] at this
        rwa [show o + (s + 1) * L + m = o + L + s * L + m by ring] at this
    rw [packOverlapAdd_cons_getD, packOverlapAdd_cons_getD]
    have hxk := h0 k
    by_cases hk : k < L
    · simp only [hk, ite_true, add_zero]
      have hk2 : k < 2 * L - 1 := by omega
      simp only [hk2, ite_true] at hxk
      exact ⟨by linarith [hF (o + k)], fun _ => hxk⟩
    · refine ⟨?_, fun h => absurd h hk⟩
      simp only [hk, ite_false]
      have hrw : x.getD k 0 + (packOverlapAdd L xs).getD (k - L) 0 -
          c * (y.getD k 0 + (packOverlapAdd L ys).getD (k - L) 0) =
          (x.getD k 0 - c * y.getD k 0) +
            ((packOverlapAdd L xs).getD (k - L) 0 - c * (packOverlapAdd L ys).getD (k - L) 0) := by
        ring
      rw [hrw]
      have ho : o + L + (k - L) = o + k := by omega
      by_cases hk2 : k < 2 * L - 1
      · simp only [hk2, ite_true] at hxk
        have := (ih (k - L)).2 (by omega)
        rw [ho] at this
        linarith [abs_add_le (x.getD k 0 - c * y.getD k 0)
          ((packOverlapAdd L xs).getD (k - L) 0 - c * (packOverlapAdd L ys).getD (k - L) 0)]
      · simp only [hk2, ite_false] at hxk
        have := (ih (k - L)).1
        rw [ho] at this
        have hz : x.getD k 0 - c * y.getD k 0 = 0 := abs_nonpos_iff.mp hxk
        rw [hz, zero_add]
        exact this

/-- An overlap-add vanishes at a slot where every window vanishes. -/
theorem packOverlapAdd_getD_eq_zero {L : ℕ} (P : ℕ → Prop) : ∀ (ws : List (List ℤ)) (o : ℕ),
    (∀ s < ws.length, ∀ m, P (o + s * L + m) → (ws.getD s []).getD m 0 = 0) →
    ∀ k, P (o + k) → (packOverlapAdd L ws).getD k 0 = 0
  | [], _, _, k, _ => by simp [packOverlapAdd]
  | x :: xs, o, hw, k, hk => by
    rw [packOverlapAdd_cons_getD]
    have hx : x.getD k 0 = 0 := by
      simpa using hw 0 (by simp) k (by simpa using hk)
    rw [hx, zero_add]
    split_ifs with hkL
    · rfl
    · refine packOverlapAdd_getD_eq_zero P xs (o + L) (fun s hs m hm => ?_) (k - L) ?_
      · have := hw (s + 1) (by simp; omega) m (by
          rwa [show o + (s + 1) * L + m = o + L + s * L + m by ring])
        simpa using this
      · rwa [show o + L + (k - L) = o + k by omega]

/-- Two lists of equal length that pack to the same integer at every width are equal. -/
theorem eq_of_packSum_forall {x y : List ℤ} (hl : x.length = y.length)
    (h : ∀ w, packSum w x = packSum w y) : x = y := by
  set M := maxAbs x + maxAbs y with hM
  have hb : ∀ (z : List ℤ), maxAbs z ≤ M → SlotsBounded (M + 1) z := by
    intro z hz c hc
    have h1 : (c.natAbs : ℤ) ≤ M := by exact_mod_cast (natAbs_le_maxAbs hc).trans hz
    have h2 : (M : ℤ) < 2 ^ M := by exact_mod_cast Nat.lt_two_pow_self
    rw [Int.abs_eq_natAbs, pow_succ]
    linarith
  exact packSum_injective (hb x (by omega)) (hb y (by omega)) hl (h (M + 1))

/-! ### The exact product as an overlap-add of shard windows -/

/-- **Overlap-add of the exact shards**: the convolution of two positive-length factors is the
overlap-add of the exact shard convolutions of their blocks. -/
theorem listConv_getD_eq_overlapAdd {L : ℕ} {da db : List ℤ} {A B : List (List ℤ)}
    (hA : ∀ x ∈ A, x.length = L) (hB : ∀ x ∈ B, x.length = L)
    (hfA : ∃ k, A.flatten = da ++ List.replicate k 0)
    (hfB : ∃ k, B.flatten = db ++ List.replicate k 0) (k : ℕ) :
    (listConv da db).getD k 0 = (packOverlapAdd L ((List.range (A.length + B.length - 1)).map
      (shardConv L A B))).getD k 0 := by
  set conv := listConv da db
  set ov := packOverlapAdd L ((List.range (A.length + B.length - 1)).map (shardConv L A B))
  set M := max conv.length ov.length
  have heq : conv ++ List.replicate (M - conv.length) 0 = ov ++ List.replicate (M - ov.length) 0 := by
    refine eq_of_packSum_forall (by simp; omega) fun w => ?_
    rw [packSum_append_replicate_zero, packSum_append_replicate_zero, packSum_listConv]
    obtain ⟨ka, hka⟩ := hfA
    obtain ⟨kb, hkb⟩ := hfB
    rw [← packSum_append_replicate_zero w da ka, ← hka, ← packSum_append_replicate_zero w db kb,
      ← hkb, packSum_flatten_mul_shards w L A B hA hB, packSum_packOverlapAdd]
    simp only [List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs, Option.map_some,
      Option.getD_some, packSum_shardConv w L A B hA hB s]
  have := congrArg (fun l => l.getD k 0) heq
  simpa only [getD_append_replicate_zero] using this

/-! ### Unpacking the zero-advice guard -/

theorem PackedAdvice.windowZeroOK_spec {adv : PackedAdvice} : ∀ (cs : List ℤ) (i : ℕ),
    adv.windowZeroOK i cs = true → ∀ m, cs.getD m 0 ≠ 0 →
      adv.inBox (i + m) = true ∧ i + m < adv.prodLen
  | [], i, _, m, hm => by simp at hm
  | c :: cs, i, h, m, hm => by
    simp only [PackedAdvice.windowZeroOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    obtain ⟨hc, hrest⟩ := h
    cases m with
    | zero =>
      simp only [List.getD_cons_zero, ne_eq] at hm
      simpa [hm] using hc
    | succ m =>
      simp only [List.getD_cons_succ] at hm
      have := PackedAdvice.windowZeroOK_spec cs (i + 1) hrest m hm
      rwa [show i + 1 + m = i + (m + 1) by omega] at this

theorem PackedAdvice.adviceZeroOK_spec {adv : PackedAdvice} : ∀ (rs : List (List ℤ)) (s₀ : ℕ),
    adv.adviceZeroOK s₀ rs = true → ∀ s < rs.length, ∀ m, (rs.getD s []).getD m 0 ≠ 0 →
      adv.inBox ((s₀ + s) * adv.blockLen + m) = true ∧ (s₀ + s) * adv.blockLen + m < adv.prodLen
  | [], _, _, s, hs, _, _ => by simp at hs
  | r :: rs, s₀, h, s, hs, m, hm => by
    simp only [PackedAdvice.adviceZeroOK, Bool.and_eq_true] at h
    cases s with
    | zero =>
      simpa using PackedAdvice.windowZeroOK_spec r _ h.1 m (by simpa using hm)
    | succ s =>
      have := PackedAdvice.adviceZeroOK_spec rs (s₀ + 1) h.2 s (by simpa using hs) m
        (by simpa using hm)
      rwa [show s₀ + 1 + s = s₀ + (s + 1) by omega] at this

/-- Off the target box the combined advice is zero. -/
theorem PackedAdvice.combined_getD_eq_zero {adv : PackedAdvice} (hs : adv.shapeOK = true)
    {k : ℕ} (hk : adv.inBox k = false) : adv.combined.getD k 0 = 0 := by
  simp only [PackedAdvice.shapeOK, Bool.and_eq_true] at hs
  have hz := PackedAdvice.adviceZeroOK_spec adv.rounded 0 hs.2
  have hov : (packOverlapAdd adv.blockLen adv.rounded).getD k 0 = 0 :=
    packOverlapAdd_getD_eq_zero (fun j => adv.inBox j = false) adv.rounded 0
      (fun s hs' m hm => by
        by_contra hne
        have := (hz s hs' m hne).1
        rw [Nat.zero_add] at this
        rw [Nat.zero_add] at hm
        rw [hm] at this
        exact Bool.false_ne_true this)
      k (by simpa using hk)
  unfold PackedAdvice.combined
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs with hkp
  · have := getD_append_replicate_zero (packOverlapAdd adv.blockLen adv.rounded) adv.prodLen k
    simp only [List.getD_eq_getElem?_getD] at this hov
    rw [this, hov]
  · rfl

/-! ### The slotwise contract -/

/-- **Slotwise contract of a passing check**: on every product slot the exact convolution is
`2^scale · combined` up to `2^scale` on the target box and `2^(outLog+1)` elsewhere, and the
combined advice is zero off the target box. -/
theorem checkPackedProduct_slots {adv : PackedAdvice} {da db : List ℤ}
    (h : checkPackedProduct adv da db = true) :
    adv.combined.length = (listConv da db).length ∧ ∀ i < (listConv da db).length,
      |(listConv da db).getD i 0 - 2 ^ adv.scale * adv.combined.getD i 0| ≤
        (if adv.inBox i then 2 ^ adv.scale else 2 ^ (adv.outLog + 1)) ∧
      (adv.inBox i = false → adv.combined.getD i 0 = 0) := by
  obtain ⟨hsc, hs, hL, hla, hlb, hpa, hpb, hlr, hsh⟩ := checkPackedProduct_guards h
  have hconvlen : (listConv da db).length = adv.prodLen := by
    rw [listConv_length (List.ne_nil_of_length_pos hpa) (List.ne_nil_of_length_pos hpb),
      PackedAdvice.prodLen, hla, hlb]
  refine ⟨by rw [PackedAdvice.combined_length, hconvlen], fun i hi => ?_⟩
  refine ⟨?_, PackedAdvice.combined_getD_eq_zero hs⟩
  set L := adv.blockLen
  set A := adv.cut da
  set B := adv.cut db
  set S := A.length + B.length - 1
  have hconv := listConv_getD_eq_overlapAdd (PackedAdvice.cut_length (d := da))
    (PackedAdvice.cut_length (d := db)) (PackedAdvice.cut_flatten hL da)
    (PackedAdvice.cut_flatten hL db) i
  have hcomb : adv.combined.getD i 0 = (packOverlapAdd L adv.rounded).getD i 0 := by
    unfold PackedAdvice.combined
    rw [hconvlen] at hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true]
    have := getD_append_replicate_zero (packOverlapAdd adv.blockLen adv.rounded) adv.prodLen i
    simpa only [List.getD_eq_getElem?_getD] using this
  rw [hconv, hcomb]
  set F : ℕ → ℤ := fun k => if adv.inBox k then 2 ^ (adv.scale - 1) else 2 ^ adv.outLog with hF
  have hbd := (packOverlapAdd_sub_abs_le hL (2 ^ adv.scale) F
    (fun k => by simp only [hF]; split_ifs <;> positivity)
    ((List.range S).map (shardConv L A B)) adv.rounded 0 (by simp [hlr, S, A, B])
    (fun s hs m => by
      have hs' : s < S := by simpa using hs
      have hE : ((List.map (shardConv L A B) (List.range S)).getD s []) = shardConv L A B s := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs',
          Option.map_some, Option.getD_some]
      rw [hE]
      obtain ⟨hlen, hsnd⟩ := checkShard_sound (hsh s hs')
      split_ifs with hm
      · have := hsnd m hm
        simp only [PackedAdvice.shardLogs] at this
        simp only [hF, Nat.zero_add]
        split_ifs at this ⊢ <;> exact_mod_cast this
      · have h1 : (shardConv L A B s).getD m 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [shardConv_length]; omega)]
          rfl
        have h2 : (adv.rounded.getD s []).getD m 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; omega)]
          rfl
        rw [h1, h2]
        simp) i).1
  rw [Nat.zero_add] at hbd
  refine hbd.trans ?_
  simp only [hF]
  split_ifs
  · rw [← pow_succ', Nat.sub_add_cancel hsc]
  · rw [pow_succ]
    linarith

/-- **Rounding/remainder glue (slots).** A passing check (the ONLY premise) gives, slot by slot of
the exact convolution, `|conv_i - 2^scale r_i| ≤ 2^scale` on the target box (at most two
overlapping shard windows, each `≤ 2^(scale-1)`, and `1 ≤ scale` from the guards) and
`|conv_i| ≤ 2^(outLog+1)` elsewhere (advice zero there). The length conjunct follows from the
exported raw shapes: `combined_length`, `prodLen` and `listConv_length` (F14). Route:
`checkPackedProduct_guards`, `checkShard_sound` (via `shard_reconstruct`),
`packSum_flatten_mul_shards`, overlap-add. -/
theorem checkPackedProduct_sound {adv : PackedAdvice} {da db : List ℤ}
    (h : checkPackedProduct adv da db = true) :
    adv.combined.length = (listConv da db).length ∧ ∀ i < (listConv da db).length,
      (adv.inBox i = true →
        |(listConv da db).getD i 0 - 2 ^ adv.scale * adv.combined.getD i 0| ≤ 2 ^ adv.scale) ∧
      (adv.inBox i = false → |(listConv da db).getD i 0| ≤ 2 ^ (adv.outLog + 1)) := by
  obtain ⟨hlen, hsl⟩ := checkPackedProduct_slots h
  refine ⟨hlen, fun i hi => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · simpa [hb] using (hsl i hi).1
  · have := (hsl i hi).1
    rw [(hsl i hi).2 hb, mul_zero, sub_zero] at this
    simpa [hb] using this

end KAM.Certificate
