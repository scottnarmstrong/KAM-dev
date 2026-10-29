/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Poly.Layout

/-!
# Design-B advice for one packed real product: validation and the shard check

A `PackedAdvice` carries, for one real product, the two factor layouts, the target box, the
rounding scale, the rounded in-box result of every output shard window (in units `2^scale`) and
a log-bound for the slots off the target. The advice is UNTRUSTED (audit 5, F12): a shard passes
`checkShard` only if its blocks have the block length, the exact side fits the signed slots
(`shardFits`), the advice side fits (`reconFits`, the anti-carry guard on `2^scale · r + e`), and
the packed residual `Σ_{i+j=s} pack(A_i) pack(B_j) - 2^scale pack(r_s)` decodes slot by slot within
the per-slot logs (`intSlotsBound`). Then `shard_reconstruct` recovers the slotwise error bound by
injectivity, since both compared lists are in the signed-slot range. `shapeOK` checks the
structural guards (`1 ≤ scale`, F13; layouts; advice lengths; zero advice off the target box and
beyond the product window), and `checkPackedProduct` the raw factor shapes (F14) and every shard.
-/

@[expose] public section

namespace KAM.Certificate

/-- Design-B advice for ONE real product (integers only): the two factor layouts, the result
box (`target`, a sub-box of the product window), the rounding scale, the rounded in-box result
of each output shard window (in units `2^scale`), and the log-bound of out-of-box slots. -/
structure PackedAdvice where
  la : PackLayout
  lb : PackLayout
  target : PackLayout
  scale : ℕ
  rounded : List (List ℤ)
  outLog : ℕ

/-! ### Untrusted-advice validation (Revision 6, audit 5 F12 and F13) -/

/-- Slotwise reconstruction `2^scale · r_i + e_i` of a shard from advice and residual digits. -/
def reconSlots (scale : ℕ) (r e : List ℤ) : List ℤ :=
  List.zipWith (fun a b => 2 ^ scale * a + b) r e

theorem packSum_reconSlots (w scale : ℕ) {r e : List ℤ} (hl : r.length = e.length) :
    packSum w (reconSlots scale r e) = 2 ^ scale * packSum w r + packSum w e := by
  induction r generalizing e with
  | nil =>
    cases e with
    | nil => simp [reconSlots, packSum_nil]
    | cons _ _ => simp at hl
  | cons a r ih =>
    cases e with
    | nil => simp at hl
    | cons b e =>
      simp only [reconSlots, List.zipWith_cons_cons] at ih ⊢
      rw [packSum_cons, packSum_cons, packSum_cons, ih (by simpa using hl)]
      ring

/-- **Anti-carry guard on untrusted advice (F12).** Every advice slot plus its residual budget
stays in the signed slot range: `2 · (2^scale |r_i| + 2^(logs i)) < 2^w`. -/
def reconFits (w scale : ℕ) (logs : ℕ → ℕ) (r : List ℤ) : Bool :=
  (List.range r.length).all fun i => decide (2 * (2 ^ scale * |r.getD i 0| + 2 ^ logs i) < 2 ^ w)

/-- `reconFits` in one pass over the advice with natural-number arithmetic (the kernel form used
by `checkShard`; `reconFitsAux_eq` identifies the two). -/
def reconFitsAux (w scale : ℕ) (logs : ℕ → ℕ) : ℕ → List ℤ → Bool
  | _, [] => true
  | i, c :: cs => decide (2 * (2 ^ scale * c.natAbs + 2 ^ logs i) < 2 ^ w) &&
      reconFitsAux w scale logs (i + 1) cs

theorem reconFitsAux_eq_all (w scale : ℕ) (logs : ℕ → ℕ) (r : List ℤ) : ∀ i : ℕ,
    reconFitsAux w scale logs i r = (List.range r.length).all fun j =>
      decide (2 * (2 ^ scale * |r.getD j 0| + 2 ^ logs (i + j)) < (2 : ℤ) ^ w) := by
  induction r with
  | nil => intro i; simp [reconFitsAux]
  | cons c r ih =>
    intro i
    rw [reconFitsAux, ih (i + 1), List.length_cons, List.range_succ_eq_map, List.all_cons,
      List.all_map]
    congr 1
    · simp only [List.getD_cons_zero, Nat.add_zero]
      refine decide_eq_decide.mpr ?_
      rw [← Int.natCast_natAbs]
      constructor <;> intro h <;> exact_mod_cast h
    · refine List.all_congr rfl fun j => ?_
      simp only [Function.comp_apply, List.getD_cons_succ, show i + (j + 1) = i + 1 + j by omega]

theorem reconFitsAux_eq (w scale : ℕ) (logs : ℕ → ℕ) (r : List ℤ) :
    reconFitsAux w scale logs 0 r = reconFits w scale logs r := by
  rw [reconFitsAux_eq_all, reconFits]
  simp

theorem slotsBounded_reconSlots {w scale : ℕ} {logs : ℕ → ℕ} {r e : List ℤ}
    (h : reconFits w scale logs r = true) (hl : e.length = r.length)
    (he : ∀ i < r.length, |e.getD i 0| ≤ 2 ^ logs i) :
    SlotsBounded w (reconSlots scale r e) := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hir : i < r.length := by simp [reconSlots] at hi; omega
  have hie : i < e.length := by omega
  simp only [reconSlots, List.getElem_zipWith]
  have hfit := List.all_eq_true.mp h i (List.mem_range.mpr hir)
  simp only [decide_eq_true_eq] at hfit
  have hr : r.getD i 0 = r[i] := by simp [List.getD_eq_getElem?_getD, hir]
  have hb := he i hir
  have heq : e.getD i 0 = e[i] := by simp [List.getD_eq_getElem?_getD, hie]
  rw [hr] at hfit
  rw [heq] at hb
  have h2 : (0 : ℤ) ≤ 2 ^ scale := by positivity
  have h3 : |2 ^ scale * r[i] + e[i]| ≤ 2 ^ scale * |r[i]| + 2 ^ logs i := by
    calc |2 ^ scale * r[i] + e[i]| ≤ |2 ^ scale * r[i]| + |e[i]| := abs_add_le _ _
      _ = 2 ^ scale * |r[i]| + |e[i]| := by rw [abs_mul, abs_of_nonneg h2]
      _ ≤ 2 ^ scale * |r[i]| + 2 ^ logs i := by linarith
  linarith

/-- The exact local convolution of shard `s` (blocks of `L` slots): `Σ_{i+j=s} A_i * B_j`,
zero-padded to `2L - 1` slots. -/
def shardConv (L : ℕ) (A B : List (List ℤ)) (s : ℕ) : List ℤ :=
  (List.range (2 * L - 1)).map fun m =>
    ((List.range (s + 1)).map fun i =>
      ((List.range (m + 1)).map fun a =>
        (A.getD i []).getD a 0 * (B.getD (s - i) []).getD (m - a) 0).sum).sum

theorem shardConv_length (L : ℕ) (A B : List (List ℤ)) (s : ℕ) :
    (shardConv L A B s).length = 2 * L - 1 := by
  simp [shardConv]

theorem shardConv_getD {L : ℕ} {A B : List (List ℤ)} {s m : ℕ} (hm : m < 2 * L - 1) :
    (shardConv L A B s).getD m 0 = ∑ i ∈ Finset.range (s + 1),
      ∑ a ∈ Finset.range (m + 1), (A.getD i []).getD a 0 * (B.getD (s - i) []).getD (m - a) 0 := by
  simp only [shardConv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm,
    Option.map_some, Option.getD_some, sum_map_range_eq]

/-- Packing with the range extended past the list's length. -/
theorem packSum_eq_sum_of_length_le (w : ℕ) {x : List ℤ} {L : ℕ} (hx : x.length ≤ L) :
    packSum w x = ∑ a ∈ Finset.range L, x.getD a 0 * (2 ^ w) ^ a := by
  rw [packSum_eq_sum, ← Finset.sum_range_add_sum_Ico _ hx]
  rw [Finset.sum_eq_zero (s := Finset.Ico x.length L) fun a ha => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Finset.mem_Ico.mp ha).1]; simp]
  simp

/-- Kronecker substitution for one shard (factor blocks of length `L`). -/
theorem packSum_shardConv (w L : ℕ) (A B : List (List ℤ))
    (hA : ∀ x ∈ A, x.length = L) (hB : ∀ x ∈ B, x.length = L) (s : ℕ) :
    packSum w (shardConv L A B s) =
      ∑ i ∈ Finset.range (s + 1), packSum w (A.getD i []) * packSum w (B.getD (s - i) []) := by
  have hlen : ∀ (C : List (List ℤ)), (∀ x ∈ C, x.length = L) → ∀ i, (C.getD i []).length ≤ L := by
    intro C hC i
    by_cases hi : i < C.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact (hC _ (List.getElem_mem hi)).le
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]
      simp
  have hz : ∀ (C : List (List ℤ)), (∀ x ∈ C, x.length = L) → ∀ i a, L ≤ a →
      (C.getD i []).getD a 0 = 0 := by
    intro C hC i a ha
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ((hlen C hC i).trans ha)]
    simp
  rw [packSum_eq_sum, shardConv_length]
  rw [Finset.sum_congr rfl fun m hm => by rw [shardConv_getD (Finset.mem_range.mp hm)]]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [packSum_eq_sum_of_length_le w (hlen A hA i),
    packSum_eq_sum_of_length_le w (hlen B hB (s - i)),
    sum_mul_sum_range_cauchy _ _ L L (fun a ha => hz A hA i a ha)
      (fun b hb => hz B hB (s - i) b hb),
    show L + L - 1 = 2 * L - 1 by omega]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]

/-- Cheap sufficient test that the exact shard convolution fits the slots:
`2 · (s + 1) · L · max|A| · max|B| < 2^w` (maxima over the blocks `0, …, s`, which are checked to
have at most `L` slots). -/
def shardFits (w L : ℕ) (A B : List (List ℤ)) (s : ℕ) : Bool :=
  ((A.take (s + 1)).all fun x => decide (x.length ≤ L)) &&
    ((B.take (s + 1)).all fun x => decide (x.length ≤ L)) &&
    decide (2 * (s + 1) * L * maxAbs (A.take (s + 1)).flatten *
      maxAbs (B.take (s + 1)).flatten < 2 ^ w)

theorem maxAbs_le_of_forall {cs : List ℤ} {M : ℕ} (h : ∀ c ∈ cs, c.natAbs ≤ M) :
    maxAbs cs ≤ M := by
  induction cs with
  | nil => simp [maxAbs]
  | cons c cs ih =>
    rw [maxAbs, List.foldr_cons]
    exact max_le (h c (by simp)) (ih fun d hd => h d (by simp [hd]))

/-- A block among the first `s + 1` is bounded by the flattened prefix. -/
theorem maxAbs_getD_le_take {C : List (List ℤ)} {i s : ℕ} (hi : i ≤ s) :
    maxAbs (C.getD i []) ≤ maxAbs (C.take (s + 1)).flatten := by
  by_cases hc : i < C.length
  · have hmem : C.getD i [] ∈ C.take (s + 1) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]
      exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
    exact maxAbs_le_of_forall fun c hcm =>
      natAbs_le_maxAbs (List.mem_flatten.mpr ⟨_, hmem, hcm⟩)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hc)]
    simp [maxAbs]

theorem length_getD_le_take {C : List (List ℤ)} {i s L : ℕ} (hi : i ≤ s)
    (h : ((C.take (s + 1)).all fun x => decide (x.length ≤ L)) = true) :
    (C.getD i []).length ≤ L := by
  by_cases hc : i < C.length
  · have hmem : C.getD i [] ∈ C.take (s + 1) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some]
      exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
    simpa using List.all_eq_true.mp h _ hmem
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hc)]
    simp

theorem slotsBounded_shardConv {w L : ℕ} {A B : List (List ℤ)} {s : ℕ}
    (h : shardFits w L A B s = true) : SlotsBounded w (shardConv L A B s) := by
  simp only [shardFits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlA, hlB⟩, hfit⟩ := h
  set mA := maxAbs (A.take (s + 1)).flatten
  set mB := maxAbs (B.take (s + 1)).flatten
  intro c hc
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
  have hm' : m < 2 * L - 1 := by simpa [shardConv_length] using hm
  have hget : (shardConv L A B s)[m] = (shardConv L A B s).getD m 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  rw [hget, shardConv_getD hm']
  have hterm : ∀ i ∈ Finset.range (s + 1),
      |∑ a ∈ Finset.range (m + 1), (A.getD i []).getD a 0 * (B.getD (s - i) []).getD (m - a) 0| ≤
        (L : ℤ) * mA * mB := by
    intro i hi
    have hi' : i ≤ s := by simpa [Nat.lt_succ_iff] using hi
    refine (abs_conv_entry_le _ _ m).trans ?_
    have h1 : min (A.getD i []).length (B.getD (s - i) []).length ≤ L :=
      (min_le_left _ _).trans (length_getD_le_take hi' hlA)
    have h2 : (maxAbs (A.getD i []) : ℤ) ≤ mA := by exact_mod_cast maxAbs_getD_le_take hi'
    have h3 : (maxAbs (B.getD (s - i) []) : ℤ) ≤ mB := by
      exact_mod_cast maxAbs_getD_le_take (Nat.sub_le s i)
    have h1' : ((min (A.getD i []).length (B.getD (s - i) []).length : ℕ) : ℤ) ≤ L := by
      exact_mod_cast h1
    have h0 : (0 : ℤ) ≤ (maxAbs (A.getD i []) : ℤ) := by positivity
    have h0' : (0 : ℤ) ≤ (maxAbs (B.getD (s - i) []) : ℤ) := by positivity
    exact mul_le_mul (mul_le_mul h1' h2 h0 (by positivity)) h3 h0' (by positivity)
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hfit' : (2 * (s + 1) * L * mA * mB : ℤ) < 2 ^ w := by exact_mod_cast hfit
  push_cast at hsum
  nlinarith

/-- **Shard reconstruction (F12).** Premises are checkable guards only: block lengths, the exact
side fits (`shardFits`), the advice side fits (`reconFits`), the advice length and a passing slot
decode of the packed residual. Then the exact shard convolution is slotwise within `2^(logs i)`
of `2^scale · r` (both lists in the injective range, so `packSum_injective` applies). -/
theorem shard_reconstruct {w scale L : ℕ} {logs : ℕ → ℕ} {A B : List (List ℤ)} {s : ℕ}
    {r : List ℤ} (hA : ∀ x ∈ A, x.length = L) (hB : ∀ x ∈ B, x.length = L)
    (hfit : shardFits w L A B s = true) (hrec : reconFits w scale logs r = true)
    (hlen : r.length = 2 * L - 1)
    (hdec : intSlotsBound w (2 * L - 1) logs
      ((∑ i ∈ Finset.range (s + 1), packSum w (A.getD i []) * packSum w (B.getD (s - i) [])) -
        2 ^ scale * packSum w r) = true) :
    ∀ i < 2 * L - 1, |(shardConv L A B s).getD i 0 - 2 ^ scale * r.getD i 0| ≤ 2 ^ logs i := by
  obtain ⟨e, hel, heb, hX⟩ := intSlotsBound_sound hdec
  have hpack : packSum w (shardConv L A B s) = packSum w (reconSlots scale r e) := by
    rw [packSum_shardConv w L A B hA hB s, packSum_reconSlots w scale (by omega)]
    linarith
  have hrecb := slotsBounded_reconSlots hrec (by omega) fun i hi => heb i (by omega)
  have heq := packSum_injective (slotsBounded_shardConv hfit) hrecb
    (by simp [shardConv_length, reconSlots, hlen, hel]) hpack
  intro i hi
  rw [heq]
  have hir : i < r.length := by omega
  have hie : i < e.length := by omega
  simp only [reconSlots, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hie, Option.getD_some]
  have := heb i hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hie, Option.getD_some] at this
  simpa using this

/-! ### Blocks, windows and the overlap-add -/

/-- Slots per factor block (`blockRows` rows of the factor layout; a row is the outermost
stride, one slot in dimension zero). -/
def PackedAdvice.blockLen (adv : PackedAdvice) : ℕ := adv.la.blockRows * adv.la.stride.headD 1

/-- Cut a list into blocks of `L` slots, the last one zero-padded (`fuel` blocks at most). -/
def packCutAux (L : ℕ) : ℕ → List ℤ → List (List ℤ)
  | 0, _ => []
  | f + 1, d => if d.isEmpty then [] else
      (d.take L ++ List.replicate (L - (d.take L).length) 0) :: packCutAux L f (d.drop L)

/-- A dense factor cut into blocks of `blockLen` slots, the last one zero-padded. -/
def PackedAdvice.cut (adv : PackedAdvice) (d : List ℤ) : List (List ℤ) :=
  packCutAux adv.blockLen d.length d

theorem packCutAux_length (L : ℕ) : ∀ (f : ℕ) (d : List ℤ), ∀ x ∈ packCutAux L f d, x.length = L
  | 0, _ => by simp [packCutAux]
  | f + 1, d => by
    intro x hx
    rw [packCutAux] at hx
    split_ifs at hx
    · simp at hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp only [List.length_append, List.length_replicate, List.length_take]
        omega
      · exact packCutAux_length L f _ x hx

theorem PackedAdvice.cut_length {adv : PackedAdvice} {d : List ℤ} :
    ∀ x ∈ adv.cut d, x.length = adv.blockLen :=
  packCutAux_length _ _ _

theorem packCutAux_nil (L f : ℕ) : packCutAux L f [] = [] := by
  cases f <;> simp [packCutAux]

/-- Cutting only pads with zeros at the end. -/
theorem packCutAux_flatten {L : ℕ} (hL : 0 < L) : ∀ (f : ℕ) (d : List ℤ), d.length ≤ f * L →
    ∃ k, (packCutAux L f d).flatten = d ++ List.replicate k 0
  | 0, d, hd => ⟨0, by
      have : d = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
      simp [packCutAux, this]⟩
  | f + 1, d, hd => by
    rw [packCutAux]
    split_ifs with he
    · exact ⟨0, by simp [List.isEmpty_iff.mp he]⟩
    · obtain ⟨k, hk⟩ := packCutAux_flatten hL f (d.drop L) (by
        rw [List.length_drop]; rw [Nat.succ_mul] at hd; omega)
      rw [List.flatten_cons, hk]
      by_cases hdl : L ≤ d.length
      · refine ⟨k, ?_⟩
        rw [List.length_take, Nat.min_eq_left hdl, Nat.sub_self, List.replicate_zero,
          List.append_nil, ← List.append_assoc, List.take_append_drop]
      · have hdrop : d.drop L = [] := List.drop_eq_nil_of_le (by omega)
        refine ⟨L - d.length + k, ?_⟩
        rw [hdrop, List.nil_append, List.take_of_length_le (by omega), List.append_assoc,
          List.replicate_append_replicate]

theorem PackedAdvice.cut_flatten {adv : PackedAdvice} (hL : 0 < adv.blockLen) (d : List ℤ) :
    ∃ k, (adv.cut d).flatten = d ++ List.replicate k 0 :=
  packCutAux_flatten hL _ _ (Nat.le_mul_of_pos_right _ hL)

theorem listConv_length {a b : List ℤ} (ha : a ≠ []) (hb : b ≠ []) :
    (listConv a b).length = a.length + b.length - 1 := by
  have : (a.isEmpty || b.isEmpty) = false := by
    simp [ha, hb]
  simp [listConv, this]

/-- Exact product length: `la.denseLen + lb.denseLen - 1` (both factors nonempty under the
empty-factor policy of `checkPackedProduct`). -/
def PackedAdvice.prodLen (adv : PackedAdvice) : ℕ := adv.la.denseLen + adv.lb.denseLen - 1

/-- Mixed-radix window test: the digits of `i` for the strides `ss` lie in `[a_j, b_j)` on every
axis (natural-number arithmetic only; the kernel form of `PackedAdvice.inBox`). -/
def packDigitsIn : List ℕ → List ℕ → List ℕ → ℕ → Bool
  | s :: ss, a :: as, b :: bs, i =>
    decide (a ≤ i / s) && decide (i / s < b) && packDigitsIn ss as bs (i % s)
  | _, _, _, _ => true

/-- Lower digit bounds of the target box: `target.lo_j - lo_a_j - lo_b_j` (clamped at `0`). -/
def PackedAdvice.boxLow (adv : PackedAdvice) : List ℕ :=
  (List.range adv.la.dims.length).map fun j =>
    (adv.target.lo.getD j 0 - adv.la.lo.getD j 0 - adv.lb.lo.getD j 0).toNat

/-- Upper digit bounds of the target box: `target.lo_j + target.dims_j - lo_a_j - lo_b_j`. -/
def PackedAdvice.boxHigh (adv : PackedAdvice) : List ℕ :=
  (List.range adv.la.dims.length).map fun j =>
    (adv.target.lo.getD j 0 + (adv.target.dims.getD j 0 : ℤ) - adv.la.lo.getD j 0 -
      adv.lb.lo.getD j 0).toNat

/-- Whether product slot `i` lies in the target box: the key `lo_a + lo_b + digits(i)` of the slot
(`PackLayout.prodKey`) satisfies `target.lo ≤ key < target.lo + target.dims` on every axis
(`PackedAdvice.inBox_eq`). Computed on the digits with natural numbers only (it runs on every
slot of every shard). -/
def PackedAdvice.inBox (adv : PackedAdvice) (i : ℕ) : Bool :=
  adv.target.dims.length == adv.la.dims.length && adv.la.stride.length == adv.la.dims.length &&
    packDigitsIn adv.la.stride adv.boxLow adv.boxHigh i

/-- Per-slot log-bounds of shard `s`: `scale - 1` on target slots, `outLog` elsewhere. -/
def PackedAdvice.shardLogs (adv : PackedAdvice) (s : ℕ) : ℕ → ℕ :=
  fun i => if adv.inBox (s * adv.blockLen + i) then adv.scale - 1 else adv.outLog

/-- Slotwise sum with zero extension (the longer tail is kept). -/
def packAddZ : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: packAddZ xs ys

/-- Overlap-add of windows placed at offsets `0, L, 2L, …` (zero-extended). -/
def packOverlapAdd (L : ℕ) : List (List ℤ) → List ℤ
  | [] => []
  | x :: xs => packAddZ x (List.replicate L 0 ++ packOverlapAdd L xs)

/-- Overlap-add of the shard windows: the combined rounded result, one entry per product slot.
**Cropping (F14):** window `s` is added at offset `s · blockLen`; the sum is zero-extended and then
cut by `take prodLen`, so it has EXACTLY `prodLen` entries (the cropped tail is zero advice by
`shapeOK`: beyond the product window). -/
def PackedAdvice.combined (adv : PackedAdvice) : List ℤ :=
  (packOverlapAdd adv.blockLen adv.rounded ++ List.replicate adv.prodLen 0).take adv.prodLen

theorem PackedAdvice.combined_length (adv : PackedAdvice) :
    adv.combined.length = adv.prodLen := by
  simp [PackedAdvice.combined]

theorem packDigitsIn_iff : ∀ (ss as bs : List ℕ) (i : ℕ), as.length = ss.length →
    bs.length = ss.length → (packDigitsIn ss as bs i = true ↔
      ∀ j < ss.length, as.getD j 0 ≤ (packDigits ss i).getD j 0 ∧
        (packDigits ss i).getD j 0 < bs.getD j 0)
  | [], _, _, _, _, _ => by simp [packDigitsIn]
  | s :: ss, a :: as, b :: bs, i, ha, hb => by
    have ih := packDigitsIn_iff ss as bs (i % s) (by simpa using ha) (by simpa using hb)
    simp only [packDigitsIn, packDigits, Bool.and_eq_true, decide_eq_true_eq, ih,
      List.length_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩ j hj
      cases j with
      | zero => exact ⟨h1, h2⟩
      | succ j => simpa using h3 j (by omega)
    · intro h
      refine ⟨⟨by simpa using (h 0 (by omega)).1, by simpa using (h 0 (by omega)).2⟩,
        fun j hj => by simpa using h (j + 1) (by omega)⟩
  | s :: ss, [], _, _, ha, _ => by simp at ha
  | s :: ss, _ :: _, [], _, _, hb => by simp at hb

/-- `inBox` is the target-box test of the slot's product key. -/
theorem PackedAdvice.inBox_eq (adv : PackedAdvice) (hs : adv.la.stride.length = adv.la.dims.length)
    (i : ℕ) : adv.inBox i = (adv.target.slot (adv.la.prodKey adv.lb i)).isSome := by
  have hslot : (adv.target.slot (adv.la.prodKey adv.lb i)).isSome =
      adv.target.keyInBox (adv.la.prodKey adv.lb i) := by
    unfold PackLayout.slot
    split_ifs with h <;> simp [h]
  rw [hslot]
  have hk : (adv.la.prodKey adv.lb i).length = adv.la.dims.length := by
    simp [PackLayout.prodKey]
  have hD := packDigitsIn_iff adv.la.stride adv.boxLow adv.boxHigh i
    (by simp [PackedAdvice.boxLow, hs]) (by simp [PackedAdvice.boxHigh, hs])
  rw [hs] at hD
  have hlow : ∀ j < adv.la.dims.length, adv.boxLow.getD j 0 =
      (adv.target.lo.getD j 0 - adv.la.lo.getD j 0 - adv.lb.lo.getD j 0).toNat := by
    intro j hj
    simp [PackedAdvice.boxLow, List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hhigh : ∀ j < adv.la.dims.length, adv.boxHigh.getD j 0 =
      (adv.target.lo.getD j 0 + (adv.target.dims.getD j 0 : ℤ) - adv.la.lo.getD j 0 -
        adv.lb.lo.getD j 0).toNat := by
    intro j hj
    simp [PackedAdvice.boxHigh, List.getD_eq_getElem?_getD, List.getElem?_range hj]
  have hkey : ∀ j < adv.la.dims.length, (adv.la.prodKey adv.lb i).getD j 0 =
      adv.la.lo.getD j 0 + adv.lb.lo.getD j 0 + ((packDigits adv.la.stride i).getD j 0 : ℤ) := by
    intro j hj
    simp [PackLayout.prodKey, List.getD_eq_getElem?_getD, List.getElem?_range hj]
  apply Bool.eq_iff_iff.mpr
  rw [PackedAdvice.inBox, PackLayout.keyInBox]
  simp only [Bool.and_eq_true, beq_iff_eq, hs, and_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, hD, hk]
  constructor
  · rintro ⟨htn, h⟩
    refine ⟨htn.symm, fun j hj => ?_⟩
    have hj' : j < adv.la.dims.length := htn ▸ hj
    obtain ⟨h1, h2⟩ := h j hj'
    rw [hlow j hj'] at h1
    rw [hhigh j hj'] at h2
    rw [hkey j hj']
    constructor <;> omega
  · rintro ⟨htn, h⟩
    refine ⟨htn.symm, fun j hj => ?_⟩
    have hj' : j < adv.target.dims.length := htn ▸ hj
    obtain ⟨h1, h2⟩ := h j hj'
    rw [hkey j hj] at h1 h2
    rw [hlow j hj, hhigh j hj]
    constructor <;> omega

/-! ### Structural guards and the checks -/

/-- Zero advice off the target box and beyond the product window, slot by slot from `i`. -/
def PackedAdvice.windowZeroOK (adv : PackedAdvice) : ℕ → List ℤ → Bool
  | _, [] => true
  | i, c :: cs => (c == 0 || (adv.inBox i && decide (i < adv.prodLen))) &&
      adv.windowZeroOK (i + 1) cs

/-- `windowZeroOK` on every advice window `s ≥ s₀`, window `s` at offset `s · blockLen`. -/
def PackedAdvice.adviceZeroOK (adv : PackedAdvice) : ℕ → List (List ℤ) → Bool
  | _, [] => true
  | s, r :: rs => adv.windowZeroOK (s * adv.blockLen) r && adv.adviceZeroOK (s + 1) rs

/-- The target box is a sub-box of the product window (`la.dims.length` axes, each target range
inside `lo_a + lo_b + [0, dims_a + dims_b - 1)`). -/
def PackedAdvice.targetSubBox (adv : PackedAdvice) : Bool :=
  adv.target.dims.length == adv.la.dims.length &&
    (List.range adv.la.dims.length).all fun j =>
      decide (adv.la.lo.getD j 0 + adv.lb.lo.getD j 0 ≤ adv.target.lo.getD j 0) &&
      decide (adv.target.lo.getD j 0 + (adv.target.dims.getD j 0 : ℤ) ≤
        adv.la.lo.getD j 0 + adv.lb.lo.getD j 0 +
          ((adv.la.dims.getD j 0 + adv.lb.dims.getD j 0 - 1 : ℕ) : ℤ))

/-- **Structural guards (F12, F13)**, decidable: `1 ≤ scale`; positive `width` and `blockRows`;
`compat` at `la.dims.length` with equal widths for `la`, `lb`, `target`; `target` a sub-box of
the product window; `blockLen` divides the row layout; every advice window `rounded[s]` has
length `2·blockLen - 1`; advice is ZERO on every slot outside the target box and beyond the
product window (no unchecked high slots). (`blockLen` is `blockRows` whole rows by definition,
and is checked positive.) -/
def PackedAdvice.shapeOK (adv : PackedAdvice) : Bool :=
  decide (1 ≤ adv.scale) && decide (0 < adv.la.width) && decide (0 < adv.la.blockRows) &&
    decide (0 < adv.blockLen) && PackLayout.compat adv.la.dims.length adv.la adv.lb &&
    adv.lb.width == adv.la.width && adv.target.width == adv.la.width && adv.targetSubBox &&
    (adv.rounded.all fun r => r.length == 2 * adv.blockLen - 1) &&
    adv.adviceZeroOK 0 adv.rounded

/-- The packed shard sum `Σ_{i+j=s} packShift(A_i) · packShift(B_j)` (kernel form). -/
def shardPacked (w : ℕ) (A B : List (List ℤ)) (s : ℕ) : ℤ :=
  ((List.range (s + 1)).map fun i =>
    packShift w (A.getD i []) * packShift w (B.getD (s - i) [])).sum

/-- One shard `s`, all guards inside: the blocks of `A`, `B` have length `blockLen`, the advice
window has length `2·blockLen - 1`, `shardFits`, `reconFits` with `shardLogs s`, and
`Σ_{i+j=s} packShift(A_i)·packShift(B_j) - 2^scale · packShift(r_s)` passes `intSlotsBound`
with `shardLogs s`. (`reconFits` runs in its one-pass natural-number form `reconFitsAux`, and
`2^scale` is a natural-number power, both kernel-accelerated.) -/
def checkShard (adv : PackedAdvice) (A B : List (List ℤ)) (s : ℕ) : Bool :=
  (A.all fun x => x.length == adv.blockLen) && (B.all fun x => x.length == adv.blockLen) &&
    (adv.rounded.getD s []).length == 2 * adv.blockLen - 1 &&
    shardFits adv.la.width adv.blockLen A B s &&
    reconFitsAux adv.la.width adv.scale (adv.shardLogs s) 0 (adv.rounded.getD s []) &&
    intSlotsBound adv.la.width (2 * adv.blockLen - 1) (adv.shardLogs s)
      (shardPacked adv.la.width A B s -
        ((2 ^ adv.scale : ℕ) : ℤ) * packShift adv.la.width (adv.rounded.getD s []))

theorem shardPacked_eq (w : ℕ) (A B : List (List ℤ)) (s : ℕ) :
    shardPacked w A B s =
      ∑ i ∈ Finset.range (s + 1), packSum w (A.getD i []) * packSum w (B.getD (s - i) []) := by
  rw [shardPacked, sum_map_range_eq]
  simp only [packShift_eq]

/-- **Shard soundness** (premise: the check only). -/
theorem checkShard_sound {adv : PackedAdvice} {A B : List (List ℤ)} {s : ℕ}
    (h : checkShard adv A B s = true) :
    (adv.rounded.getD s []).length = 2 * adv.blockLen - 1 ∧
      ∀ i < 2 * adv.blockLen - 1,
        |(shardConv adv.blockLen A B s).getD i 0 - 2 ^ adv.scale * (adv.rounded.getD s []).getD i 0|
          ≤ 2 ^ adv.shardLogs s i := by
  simp only [checkShard, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hlen⟩, hfit⟩, hrec⟩, hdec⟩ := h
  rw [reconFitsAux_eq] at hrec
  rw [shardPacked_eq, packShift_eq, Nat.cast_pow, Nat.cast_ofNat] at hdec
  exact ⟨hlen, shard_reconstruct hA hB hfit hrec hlen hdec⟩

/-- The whole product: `shapeOK` (with `1 ≤ scale`); **raw shapes (F14)** `da.length =
la.denseLen`, `db.length = lb.denseLen`, both positive (empty-factor policy: an empty raw factor
or an empty layout box is REJECTED; a zero factor is sent as zeros on a nonempty box, or by the
direct route); the dense factors cut by `cut`; and `checkShard` on every shard
`s < (cut da).length + (cut db).length - 1`. -/
def checkPackedProduct (adv : PackedAdvice) (da db : List ℤ) : Bool :=
  adv.shapeOK && da.length == adv.la.denseLen && db.length == adv.lb.denseLen &&
    decide (0 < da.length) && decide (0 < db.length) &&
    adv.rounded.length == (adv.cut da).length + (adv.cut db).length - 1 &&
    (List.range ((adv.cut da).length + (adv.cut db).length - 1)).all fun s =>
      checkShard adv (adv.cut da) (adv.cut db) s

/-- The whole check is exactly its guards and its shards (the assembly of separately decided
shard declarations). -/
theorem checkPackedProduct_eq_true_iff {adv : PackedAdvice} {da db : List ℤ} :
    checkPackedProduct adv da db = true ↔
      adv.shapeOK = true ∧ da.length = adv.la.denseLen ∧ db.length = adv.lb.denseLen ∧
        0 < da.length ∧ 0 < db.length ∧
        adv.rounded.length = (adv.cut da).length + (adv.cut db).length - 1 ∧
        ∀ s < (adv.cut da).length + (adv.cut db).length - 1,
          checkShard adv (adv.cut da) (adv.cut db) s = true := by
  simp only [checkPackedProduct, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  tauto

theorem PackedAdvice.shapeOK_scale {adv : PackedAdvice} (h : adv.shapeOK = true) :
    1 ≤ adv.scale ∧ 0 < adv.blockLen := by
  simp only [PackedAdvice.shapeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2⟩

/-- **Guards exported from success** (F12, F13): no premise but the check. -/
theorem checkPackedProduct_guards {adv : PackedAdvice} {da db : List ℤ}
    (h : checkPackedProduct adv da db = true) :
    1 ≤ adv.scale ∧ adv.shapeOK = true ∧ 0 < adv.blockLen ∧
      da.length = adv.la.denseLen ∧ db.length = adv.lb.denseLen ∧ 0 < da.length ∧ 0 < db.length ∧
      adv.rounded.length = (adv.cut da).length + (adv.cut db).length - 1 ∧
      ∀ s < (adv.cut da).length + (adv.cut db).length - 1,
        checkShard adv (adv.cut da) (adv.cut db) s = true := by
  obtain ⟨hs, h1, h2, h3, h4, h5, h6⟩ := checkPackedProduct_eq_true_iff.mp h
  obtain ⟨hsc, hbl⟩ := PackedAdvice.shapeOK_scale hs
  exact ⟨hsc, hs, hbl, h1, h2, h3, h4, h5, h6⟩

/-- F13 negative contract: scale zero is rejected (whatever the data). -/
theorem checkPackedProduct_scale_zero {adv : PackedAdvice} (h0 : adv.scale = 0)
    (da db : List ℤ) : checkPackedProduct adv da db = false := by
  by_contra h
  have := (checkPackedProduct_guards (Bool.not_eq_false _ ▸ h)).1
  omega

/-- F14 negative contract: a raw factor whose length is not its layout's dense length is rejected
(this excludes the padding alias `[0]` versus `[0, 0]`, which `cut` maps to the same blocks). -/
theorem checkPackedProduct_raw_length {adv : PackedAdvice} {da db : List ℤ}
    (h : da.length ≠ adv.la.denseLen ∨ db.length ≠ adv.lb.denseLen) :
    checkPackedProduct adv da db = false := by
  by_contra hc
  have g := checkPackedProduct_guards (Bool.not_eq_false _ ▸ hc)
  rcases h with h | h
  · exact h g.2.2.2.1
  · exact h g.2.2.2.2.1

/-- §8 negative test (audit 5, F12): the carry-cancelling advice `[16, -1, 0]` packs to `0` at
`w = 4` but fails the anti-carry guard (decided now; the guard body is concrete). -/
theorem packSum_audit5_cancel : packSum 4 [16, -1, 0] = 0 := by decide

theorem reconFits_audit5_rejects : reconFits 4 1 (fun _ => 0) [16, -1, 0] = false := by decide

end KAM.Certificate
