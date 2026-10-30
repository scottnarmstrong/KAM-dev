/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.OverlapAdd

/-!
# Sparse (term-driven) packed products

The dense route (`checkPackedProduct` on `PackLayout.dense` lists, cut into blocks) walks every
slot of every factor block, and almost all of them are zeros. The sparse route works on the
factor's own `(slot, value)` terms: `spBlocks` cuts strictly increasing terms into blocks of
`blockLen` slots in one pass, `spPack` packs a block from its terms (shift by the slot offset),
and the fit guard uses the largest term (`spMax`). `checkShardSp` is `checkShard` with these
ingredients; `checkPackedSp` runs it on every shard.

`checkPackedSp_dense` is the bridge: a passing sparse check makes the dense check pass on the
linear fills of the same terms, so every consumer of `checkPackedProduct` applies unchanged. The
dense lists are only named in the proof, never computed.
-/

@[expose] public section

namespace KAM.Certificate

/-! ### Sparse blocks -/

/-- Cut terms with global slots into `n` blocks of `L` slots, block `b` first (one pass:
`takeWhile` / `dropWhile` on strictly increasing slots). -/
def spBlocks (L : ℕ) : ℕ → ℕ → List (ℕ × ℤ) → List (List (ℕ × ℤ))
  | 0, _, _ => []
  | n + 1, b, es => es.takeWhile (fun e => decide (e.1 < (b + 1) * L)) ::
      spBlocks L n (b + 1) (es.dropWhile fun e => decide (e.1 < (b + 1) * L))

/-- Packing of a block's terms relative to the slot `base` (positive and negative parts
accumulated separately with `Nat.shiftLeft`). -/
def spPackAux (w base : ℕ) : List (ℕ × ℤ) → ℕ → ℕ → ℤ
  | [], p, n => (p : ℤ) - (n : ℤ)
  | e :: es, p, n =>
    if 0 ≤ e.2 then spPackAux w base es (p + (e.2.toNat <<< (w * (e.1 - base)))) n
    else spPackAux w base es p (n + ((-e.2).toNat <<< (w * (e.1 - base))))

/-- `Σ_e e.2 · 2^(w (e.1 - base))` over the terms of a block. -/
def spPack (w base : ℕ) (es : List (ℕ × ℤ)) : ℤ := spPackAux w base es 0 0

/-- The largest absolute term value. -/
def spMax (es : List (ℕ × ℤ)) : ℕ := packMaxAbsAux 0 (es.map Prod.snd)

/-- The sparse shard sum `Σ_{i+j=s} spPack(A_i) · spPack(B_j)` (block `i` relative to `i L`). -/
def shardPackedSp (w L : ℕ) (SA SB : List (List (ℕ × ℤ))) (s : ℕ) : ℤ :=
  ((List.range (s + 1)).map fun i =>
    spPack w (i * L) (SA.getD i []) * spPack w ((s - i) * L) (SB.getD (s - i) [])).sum

theorem spPackAux_eq (w base : ℕ) : ∀ (es : List (ℕ × ℤ)) (p n : ℕ),
    spPackAux w base es p n = (p : ℤ) - n + (es.map fun e => e.2 * 2 ^ (w * (e.1 - base))).sum
  | [], p, n => by simp [spPackAux]
  | e :: es, p, n => by
    rw [spPackAux]
    split_ifs with h
    · rw [spPackAux_eq w base es, Nat.shiftLeft_eq]
      have : ((e.2.toNat : ℕ) : ℤ) = e.2 := Int.toNat_of_nonneg h
      push_cast
      rw [this, List.map_cons, List.sum_cons]
      ring
    · rw [spPackAux_eq w base es, Nat.shiftLeft_eq]
      have : (((-e.2).toNat : ℕ) : ℤ) = -e.2 := Int.toNat_of_nonneg (by omega)
      push_cast
      rw [this, List.map_cons, List.sum_cons]
      ring

theorem spPack_eq (w base : ℕ) (es : List (ℕ × ℤ)) :
    spPack w base es = (es.map fun e => e.2 * 2 ^ (w * (e.1 - base))).sum := by
  simp [spPack, spPackAux_eq]

theorem takeWhile_lt_eq_filter (c : ℕ) : ∀ es : List (ℕ × ℤ),
    es.Pairwise (fun a b => a.1 < b.1) →
      es.takeWhile (fun e => decide (e.1 < c)) = es.filter (fun e => decide (e.1 < c)) ∧
        es.dropWhile (fun e => decide (e.1 < c)) = es.filter (fun e => !decide (e.1 < c))
  | [], _ => by simp
  | e :: es, h => by
    have ih := takeWhile_lt_eq_filter c es (List.Pairwise.of_cons h)
    have hr : ∀ e' ∈ es, e.1 < e'.1 := fun e' he' => List.rel_of_pairwise_cons h he'
    by_cases he : e.1 < c
    · simp [he, ih.1, ih.2]
    · have h1 : es.filter (fun e => decide (e.1 < c)) = [] :=
        List.filter_eq_nil_iff.mpr fun e' he' => by have := hr e' he'; simp; omega
      have h2 : es.filter (fun e => !decide (e.1 < c)) = es :=
        List.filter_eq_self.mpr fun e' he' => by have := hr e' he'; simp; omega
      simp [he, h1, h2]

theorem spBlocks_length (L : ℕ) : ∀ (n b : ℕ) (es : List (ℕ × ℤ)), (spBlocks L n b es).length = n
  | 0, _, _ => rfl
  | n + 1, b, es => by simp [spBlocks, spBlocks_length L n]

/-- Block `i` of the sparse cut is the filter of the terms in its slot range. -/
theorem spBlocks_getD (L : ℕ) : ∀ (n b : ℕ) (es : List (ℕ × ℤ)),
    es.Pairwise (fun a b => a.1 < b.1) → (∀ e ∈ es, b * L ≤ e.1) → ∀ i < n,
      (spBlocks L n b es).getD i [] =
        es.filter fun e => decide ((b + i) * L ≤ e.1) && decide (e.1 < (b + i) * L + L)
  | 0, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, b, es, hs, hb, i, hi => by
    obtain ⟨ht, hd⟩ := takeWhile_lt_eq_filter ((b + 1) * L) es hs
    cases i with
    | zero =>
      rw [spBlocks, List.getD_cons_zero, ht]
      refine List.filter_congr fun e he => ?_
      have := hb e he
      simp only [Nat.add_zero, Nat.succ_mul] at this ⊢
      simp [this]
    | succ i =>
      rw [spBlocks, List.getD_cons_succ, hd,
        spBlocks_getD L n (b + 1) _ (hs.filter _) (fun e he => by
          have := (List.mem_filter.mp he).2; simp at this; omega) i (by omega),
        List.filter_filter]
      refine List.filter_congr fun e _ => ?_
      rw [show b + 1 + i = b + (i + 1) by omega]
      by_cases h1 : (b + (i + 1)) * L ≤ e.1
      · have : (b + 1) * L ≤ e.1 :=
          le_trans (Nat.mul_le_mul_right _ (by omega)) h1
        simp [h1, this]
      · simp [h1]

/-! ### Dense blocks of a linear fill -/

/-- The slot totals over a window `[B, B + D)` with a geometric weight are the terms in the
window, each weighted by its offset. -/
theorem sum_packSlotTotal_window (Y : ℤ) (B D : ℕ) : ∀ es : List (ℕ × ℤ),
    ∑ a ∈ Finset.range D, packSlotTotal es (B + a) * Y ^ a =
      ((es.filter fun e => decide (B ≤ e.1) && decide (e.1 < B + D)).map
        fun e => e.2 * Y ^ (e.1 - B)).sum
  | [] => by simp [packSlotTotal]
  | e :: es => by
    have ih := sum_packSlotTotal_window Y B D es
    have hsplit : ∀ a, packSlotTotal (e :: es) (B + a) * Y ^ a =
        (if B + a = e.1 then e.2 * Y ^ a else 0) + packSlotTotal es (B + a) * Y ^ a := by
      intro a
      by_cases h : e.1 = B + a
      · simp [packSlotTotal, h, add_mul]
      · have h' : ¬ B + a = e.1 := fun h' => h h'.symm
        simp [packSlotTotal, h, h']
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib, ih]
    by_cases hw : B ≤ e.1 ∧ e.1 < B + D
    · have hmem : e.1 - B ∈ Finset.range D := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single (e.1 - B) (fun a _ ha => by
          rw [ite_eq_right_iff.mpr fun h => absurd h (by omega)]) (fun h => absurd hmem h),
        ite_eq_left_iff.mpr fun h => absurd (by omega) h]
      simp [hw.1, hw.2]
    · have hz : ∀ a ∈ Finset.range D, (if B + a = e.1 then e.2 * Y ^ a else 0) = 0 := by
        intro a ha
        have := Finset.mem_range.mp ha
        exact ite_eq_right_iff.mpr fun h => absurd h (by omega)
      rw [Finset.sum_eq_zero hz]
      have : ¬ (decide (B ≤ e.1) && decide (e.1 < B + D)) = true := by
        simpa using fun h1 => by omega
      simp [this]

/-- A block of a list whose blocks all have length `L` is read off the flattening. -/
theorem getD_getD_of_flatten {L : ℕ} : ∀ (C : List (List ℤ)), (∀ x ∈ C, x.length = L) →
    ∀ (i a : ℕ), a < L → (C.getD i []).getD a 0 = C.flatten.getD (i * L + a) 0
  | [], _, i, a, _ => by simp
  | x :: C, hC, i, a, ha => by
    have hx : x.length = L := hC x (by simp)
    cases i with
    | zero =>
      rw [List.getD_cons_zero, List.flatten_cons, Nat.zero_mul, Nat.zero_add,
        List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    | succ i =>
      rw [List.getD_cons_succ, getD_getD_of_flatten C (fun y hy => hC y (by simp [hy])) i a ha,
        List.flatten_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hx, Nat.succ_mul]; omega), hx]
      congr 2
      rw [Nat.succ_mul]; omega

/-- The length of a cut: `⌈|d| / L⌉` blocks. -/
theorem packCutAux_length_eq {L : ℕ} (hL : 0 < L) : ∀ (f : ℕ) (d : List ℤ), d.length ≤ f * L →
    (packCutAux L f d).length = (d.length + L - 1) / L
  | 0, d, hd => by
    have : d = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst this
    simp only [packCutAux, List.length_nil, Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  | f + 1, d, hd => by
    rw [packCutAux]
    split_ifs with he
    · rw [List.isEmpty_iff.mp he, List.length_nil, List.length_nil, Nat.zero_add]
      exact (Nat.div_eq_of_lt (by omega)).symm
    · have hpos : 0 < d.length := by
        rcases d with _ | ⟨x, d⟩
        · simp at he
        · simp
      rw [List.length_cons, packCutAux_length_eq hL f _ (by
          rw [List.length_drop]; rw [Nat.succ_mul] at hd; omega), List.length_drop]
      by_cases hdl : d.length ≤ L
      · rw [show d.length - L = 0 by omega, Nat.zero_add, Nat.div_eq_of_lt (by omega),
          Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
      · rw [show d.length + L - 1 = (d.length - L + L - 1) + L by omega, Nat.add_div_right _ hL]

theorem PackedAdvice.cut_length_eq {adv : PackedAdvice} (hL : 0 < adv.blockLen) (d : List ℤ) :
    (adv.cut d).length = (d.length + adv.blockLen - 1) / adv.blockLen := by
  unfold PackedAdvice.cut
  rw [packLengthAux_eq, Nat.zero_add]
  exact packCutAux_length_eq hL _ _ (Nat.le_mul_of_pos_right _ hL)

theorem packFill_getD {N : ℕ} {es : List (ℕ × ℤ)} (hs : es.Pairwise fun a b => a.1 < b.1)
    (hN : ∀ e ∈ es, e.1 < N) (p : ℕ) : (packFill N 0 es).getD p 0 = packSlotTotal es p := by
  rw [packFill_eq N 0 es hs (by simp)]
  by_cases hp : p < N
  · simp [List.getD_eq_getElem?_getD, hp]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using not_lt.mp hp),
      Option.getD_none, packSlotTotal_eq_zero fun e he => by have := hN e he; omega]

theorem packFill_length (N : ℕ) : ∀ (p : ℕ) (es : List (ℕ × ℤ)), (packFill N p es).length = N := by
  induction N with
  | zero => intro p es; rfl
  | succ N ih =>
    intro p es
    cases es with
    | nil => simp [packFill, ih]
    | cons e es => rw [packFill]; split_ifs <;> simp [ih]

/-- The packed value of dense block `i` of a cut linear fill is the sparse pack of block `i`. -/
theorem packSum_cut_packFill {adv : PackedAdvice} (hL : 0 < adv.blockLen) {N : ℕ}
    {es : List (ℕ × ℤ)} (hs : es.Pairwise fun a b => a.1 < b.1) (hN : ∀ e ∈ es, e.1 < N)
    (w i : ℕ) :
    packSum w ((adv.cut (packFill N 0 es)).getD i []) =
      spPack w (i * adv.blockLen)
        ((spBlocks adv.blockLen ((N + adv.blockLen - 1) / adv.blockLen) 0 es).getD i []) := by
  set L := adv.blockLen
  have hlen : (adv.cut (packFill N 0 es)).length = (N + L - 1) / L := by
    rw [PackedAdvice.cut_length_eq hL, packFill_length]
  by_cases hi : i < (N + L - 1) / L
  · have hmem : (adv.cut (packFill N 0 es)).getD i [] ∈ adv.cut (packFill N 0 es) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨k, hk⟩ := PackedAdvice.cut_flatten hL (packFill N 0 es)
    rw [packSum_eq_sum_of_length_le w (PackedAdvice.cut_length _ hmem).le,
      spBlocks_getD L _ 0 es hs (by simp) i hi, spPack_eq, Nat.zero_add]
    rw [Finset.sum_congr rfl fun a ha => by
      rw [getD_getD_of_flatten _ (fun x hx => PackedAdvice.cut_length x hx) i a
        (Finset.mem_range.mp ha), hk, getD_append_replicate_zero, packFill_getD hs hN]]
    rw [sum_packSlotTotal_window]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    rw [pow_mul]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [spBlocks_length]; omega)]
    simp [packSum_nil, spPack_eq]

/-- Every entry of a linear fill of strictly increasing terms is bounded by the largest term. -/
theorem natAbs_packSlotTotal_le {es : List (ℕ × ℤ)} (hs : es.Pairwise fun a b => a.1 < b.1)
    (p : ℕ) : (packSlotTotal es p).natAbs ≤ spMax es := by
  rw [spMax, packMaxAbsAux_eq, Nat.zero_max]
  induction es with
  | nil => simp [packSlotTotal]
  | cons e es ih =>
    have hr : ∀ e' ∈ es, e.1 < e'.1 := fun e' he' => List.rel_of_pairwise_cons hs he'
    have ih' := ih (List.Pairwise.of_cons hs)
    have hle : maxAbs (es.map Prod.snd) ≤ maxAbs ((e :: es).map Prod.snd) := by
      simp only [List.map_cons, maxAbs, List.foldr_cons]
      exact le_max_right _ _
    by_cases he : e.1 = p
    · have h0 := packSlotTotal_eq_zero (es := es) (p := p) fun e' he' => by
        have := hr e' he'; omega
      rw [packSlotTotal] at h0 ⊢
      simp only [List.filter_cons, he, beq_self_eq_true, ite_true, List.map_cons, List.sum_cons,
        h0, add_zero]
      exact natAbs_le_maxAbs (by simp)
    · have : packSlotTotal (e :: es) p = packSlotTotal es p := by
        simp [packSlotTotal, he]
      rw [this]
      exact ih'.trans hle

/-! ### The sparse checks and the bridge to the dense check -/

/-- Number of blocks of `blockLen` slots covering `N` slots. -/
def PackedAdvice.spCount (adv : PackedAdvice) (N : ℕ) : ℕ :=
  (N + adv.blockLen - 1) / adv.blockLen

/-- One shard from sparse blocks (`checkShard` with sparse packing): the advice window has length
`2·blockLen - 1`, the fit guard `2 (s + 1) blockLen mA mB < 2^w` holds for the given term bounds,
`reconFits` holds with `shardLogs s`, and the packed residual passes `intSlotsBound`. -/
def checkShardSp (adv : PackedAdvice) (SA SB : List (List (ℕ × ℤ))) (mA mB s : ℕ) : Bool :=
  packLenEq (adv.rounded.getD s []) (2 * adv.blockLen - 1) &&
    decide (2 * (s + 1) * adv.blockLen * mA * mB < 2 ^ adv.la.width) &&
    reconFitsAux adv.la.width adv.scale (adv.shardLogs s) 0 (adv.rounded.getD s []) &&
    intSlotsBound adv.la.width (2 * adv.blockLen - 1) (adv.shardLogs s)
      (shardPackedSp adv.la.width adv.blockLen SA SB s -
        ((2 ^ adv.scale : ℕ) : ℤ) * packShift adv.la.width (adv.rounded.getD s []))

/-- The whole product from the factors' `(slot, value)` terms: `shapeOK`; positive dense lengths;
strictly increasing slots below the dense lengths; the advice has one window per shard; and
`checkShardSp` on every shard, with the blocks cut once by `spBlocks` and the largest terms as
the fit bounds. -/
def checkPackedSp (adv : PackedAdvice) (ea eb : List (ℕ × ℤ)) : Bool :=
  adv.shapeOK && decide (0 < adv.la.denseLen) && decide (0 < adv.lb.denseLen) &&
    packStrictAsc ea && packStrictAsc eb &&
    (ea.all fun e => decide (e.1 < adv.la.denseLen)) &&
    (eb.all fun e => decide (e.1 < adv.lb.denseLen)) &&
    adv.rounded.length == adv.spCount adv.la.denseLen + adv.spCount adv.lb.denseLen - 1 &&
    (List.range (adv.spCount adv.la.denseLen + adv.spCount adv.lb.denseLen - 1)).all fun s =>
      checkShardSp adv (spBlocks adv.blockLen (adv.spCount adv.la.denseLen) 0 ea)
        (spBlocks adv.blockLen (adv.spCount adv.lb.denseLen) 0 eb) (spMax ea) (spMax eb) s

theorem maxAbs_take_cut_packFill_le {adv : PackedAdvice} (hL : 0 < adv.blockLen) {N : ℕ}
    {es : List (ℕ × ℤ)} (hs : es.Pairwise fun a b => a.1 < b.1) (n : ℕ) :
    maxAbs ((adv.cut (packFill N 0 es)).take n).flatten ≤ spMax es := by
  obtain ⟨k, hk⟩ := PackedAdvice.cut_flatten hL (packFill N 0 es)
  refine maxAbs_le_of_forall fun c hc => ?_
  have hc' : c ∈ (adv.cut (packFill N 0 es)).flatten := by
    obtain ⟨x, hx, hcx⟩ := List.mem_flatten.mp hc
    exact List.mem_flatten.mpr ⟨x, List.mem_of_mem_take hx, hcx⟩
  rw [hk, List.mem_append] at hc'
  rcases hc' with hc' | hc'
  · rw [packFill_eq N 0 es hs (by simp), List.mem_map] at hc'
    obtain ⟨p, -, rfl⟩ := hc'
    exact natAbs_packSlotTotal_le hs _
  · rw [List.eq_of_mem_replicate hc']
    simp

/-- **Shard bridge**: a passing sparse shard makes the dense shard of the linear fills pass. -/
theorem checkShardSp_dense {adv : PackedAdvice} (hL : 0 < adv.blockLen) {N M : ℕ}
    {ea eb : List (ℕ × ℤ)} (hsa : ea.Pairwise fun a b => a.1 < b.1) (hNa : ∀ e ∈ ea, e.1 < N)
    (hsb : eb.Pairwise fun a b => a.1 < b.1) (hNb : ∀ e ∈ eb, e.1 < M) {s : ℕ}
    (h : checkShardSp adv (spBlocks adv.blockLen (adv.spCount N) 0 ea)
      (spBlocks adv.blockLen (adv.spCount M) 0 eb) (spMax ea) (spMax eb) s = true) :
    checkShard adv (adv.cut (packFill N 0 ea)) (adv.cut (packFill M 0 eb)) s = true := by
  simp only [checkShardSp, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hfit⟩, hrec⟩, hdec⟩ := h
  have hpk : shardPacked adv.la.width (adv.cut (packFill N 0 ea)) (adv.cut (packFill M 0 eb)) s =
      shardPackedSp adv.la.width adv.blockLen (spBlocks adv.blockLen (adv.spCount N) 0 ea)
        (spBlocks adv.blockLen (adv.spCount M) 0 eb) s := by
    unfold shardPacked shardPackedSp
    congr 1
    refine List.map_congr_left fun i _ => ?_
    rw [packShift_eq, packShift_eq, packSum_cut_packFill hL hsa hNa,
      packSum_cut_packFill hL hsb hNb]
    rfl
  have hlenA : ∀ x ∈ adv.cut (packFill N 0 ea), packLenLe x adv.blockLen = true :=
    fun x hx => (packLenLe_iff _ _).mpr (PackedAdvice.cut_length x hx).le
  have hlenB : ∀ x ∈ adv.cut (packFill M 0 eb), packLenLe x adv.blockLen = true :=
    fun x hx => (packLenLe_iff _ _).mpr (PackedAdvice.cut_length x hx).le
  simp only [checkShard, shardFits, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    packLenLeBlocks_eq, packMaxBlocks_eq, Nat.zero_max]
  refine ⟨⟨⟨⟨⟨fun x hx => (packLenEq_iff _ _).mpr (PackedAdvice.cut_length x hx),
    fun x hx => (packLenEq_iff _ _).mpr (PackedAdvice.cut_length x hx)⟩, hlen⟩,
    ⟨⟨fun x hx => hlenA x (List.mem_of_mem_take hx),
      fun x hx => hlenB x (List.mem_of_mem_take hx)⟩, ?_⟩⟩, hrec⟩, ?_⟩
  · refine lt_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul_left _ ?_) ?_) hfit
    · exact maxAbs_take_cut_packFill_le hL hsa _
    · exact maxAbs_take_cut_packFill_le hL hsb _
  · rw [hpk]
    exact hdec

/-- **Product bridge**: a passing sparse check makes `checkPackedProduct` pass on the linear fills
of the same terms (so every consumer of the dense check applies). -/
theorem checkPackedSp_dense {adv : PackedAdvice} {ea eb : List (ℕ × ℤ)}
    (h : checkPackedSp adv ea eb = true) :
    checkPackedProduct adv (packFill adv.la.denseLen 0 ea) (packFill adv.lb.denseLen 0 eb) =
      true := by
  simp only [checkPackedSp, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, hpa⟩, hpb⟩, hsa⟩, hsb⟩, hNa⟩, hNb⟩, hr⟩, hsh⟩ := h
  have hL := (PackedAdvice.shapeOK_scale hs).2
  have hsa' := packStrictAsc_pairwise hsa
  have hsb' := packStrictAsc_pairwise hsb
  have hcA : (adv.cut (packFill adv.la.denseLen 0 ea)).length = adv.spCount adv.la.denseLen := by
    rw [PackedAdvice.cut_length_eq hL, packFill_length]; rfl
  have hcB : (adv.cut (packFill adv.lb.denseLen 0 eb)).length = adv.spCount adv.lb.denseLen := by
    rw [PackedAdvice.cut_length_eq hL, packFill_length]; rfl
  refine checkPackedProduct_eq_true_iff.mpr ⟨hs, packFill_length _ _ _, packFill_length _ _ _,
    (by rw [packFill_length]; exact hpa), (by rw [packFill_length]; exact hpb),
    (by rw [hcA, hcB]; exact hr), fun s hs' => ?_⟩
  rw [hcA, hcB] at hs'
  exact checkShardSp_dense hL hsa' (fun e he => by simpa using hNa e he) hsb'
    (fun e he => by simpa using hNb e he) (hsh s hs')

end KAM.Certificate
