/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Mantissa
public import KAM.Certificate.Poly.Basic
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Kronecker packing of integer slot lists

Signed integer slots `c_i` are packed into one big integer `Σ c_i 2^{w i}` (`packSum`); the
kernel packing `packShift` packs leaf chunks with `Nat.shiftLeft` and merges them in a balanced
tree (no linear accumulator of big integers). Under the slot bound the packing is injective
(`packSum_injective`), packing turns convolution into one product (`packSum_listConv`), the
packed product of block-cut factors is a shifted sum of shard sums
(`packSum_flatten_mul_shards`), and `intSlotsBound` decodes slots of a big integer by bounds, on
an offset natural number split in balanced halves by mask and shift.
-/

@[expose] public section

namespace KAM.Certificate

/-- The mathematical Kronecker packing `Σ_i c_i 2^{w i}` of signed slots. -/
def packSum (w : ℕ) (cs : List ℤ) : ℤ :=
  ((List.range cs.length).map fun i => cs.getD i 0 * 2 ^ (w * i)).sum

theorem packSum_nil (w : ℕ) : packSum w [] = 0 := rfl

theorem sum_map_range_eq (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem packSum_cons (w : ℕ) (c : ℤ) (cs : List ℤ) :
    packSum w (c :: cs) = c + 2 ^ w * packSum w cs := by
  unfold packSum
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
  simp only [Function.comp_def, List.getD_cons_zero, List.getD_cons_succ, mul_zero, pow_zero,
    mul_one]
  rw [← List.sum_map_mul_left]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  rw [Nat.succ_eq_add_one, show w * (i + 1) = w * i + w by ring, pow_add]
  ring

theorem packSum_append (w : ℕ) (x y : List ℤ) :
    packSum w (x ++ y) = packSum w x + 2 ^ (w * x.length) * packSum w y := by
  induction x with
  | nil => simp [packSum_nil]
  | cons c x ih =>
    rw [List.cons_append, packSum_cons, packSum_cons, ih, List.length_cons]
    rw [show w * (x.length + 1) = w * x.length + w by ring, pow_add]
    ring

/-- The packing as a finite sum with a geometric weight. -/
theorem packSum_eq_sum (w : ℕ) (cs : List ℤ) :
    packSum w cs = ∑ i ∈ Finset.range cs.length, cs.getD i 0 * (2 ^ w) ^ i := by
  induction cs with
  | nil => simp [packSum_nil]
  | cons c cs ih =>
    rw [packSum_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

/-! ### The kernel packing

`packShift` packs in two stages, so that the kernel never builds a long chain of big
intermediate integers (a linear accumulator costs memory quadratic in the packed bits):
the slots are packed in leaf chunks of `16` slots (`packLeavesAux`), each a pair of natural
numbers (positive and negative parts, accumulated with `Nat.shiftLeft`), and the chunks are then
merged pairwise, level by level, with doubled widths (`packMerge`, `packTree`), a balanced
divide-and-conquer. Every arithmetic step is a kernel-accelerated natural-number operation. -/

/-- The signed value `Σ_i (p_i - n_i) 2^{W i}` of a list of chunk pairs. -/
def pairVal (W : ℕ) : List (ℕ × ℕ) → ℤ
  | [] => 0
  | x :: xs => ((x.1 : ℤ) - x.2) + 2 ^ W * pairVal W xs

/-- Leaf chunks: the current chunk `(p, n)` has room for `j` more slots, the next one at shift
`s`; a full chunk is emitted and a new one (of `k` slots) started. -/
def packLeavesAux (w k : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℤ → List (ℕ × ℕ)
  | _, _, p, n, [] => [(p, n)]
  | j + 1, s, p, n, c :: cs =>
    if 0 ≤ c then packLeavesAux w k j (s + w) (p + (c.toNat <<< s)) n cs
    else packLeavesAux w k j (s + w) p (n + ((-c).toNat <<< s)) cs
  | 0, _, p, n, c :: cs =>
    (p, n) :: if 0 ≤ c then packLeavesAux w k (k - 1) w c.toNat 0 cs
      else packLeavesAux w k (k - 1) w 0 (-c).toNat cs

/-- One merge level: adjacent chunks of width `W` combine into chunks of width `2W`. -/
def packMerge (W : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | x :: y :: xs => (x.1 + (y.1 <<< W), x.2 + (y.2 <<< W)) :: packMerge W xs
  | xs => xs

/-- Linear combination of the chunks (the fallback when the level budget is exhausted). -/
def packFold (W : ℕ) : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0, 0)
  | x :: xs => let r := packFold W xs; (x.1 + (r.1 <<< W), x.2 + (r.2 <<< W))

/-- Balanced merging: `fuel` levels of `packMerge`, the width doubling at each level. -/
def packTree : ℕ → ℕ → List (ℕ × ℕ) → ℕ × ℕ
  | _, _, [] => (0, 0)
  | _, _, [x] => x
  | 0, W, xs => packFold W xs
  | f + 1, W, x :: y :: xs => packTree f (2 * W) (packMerge W (x :: y :: xs))

/-- The linear packing loop (the original `packShift` body), kept as a public helper: the shift `s`
advances by `w` per slot. `packShift` now packs by a balanced tree (`packTree`). -/
def packShiftAux (w : ℕ) : ℕ → List ℤ → ℕ → ℕ → ℤ
  | _, [], p, n => (p : ℤ) - (n : ℤ)
  | s, c :: cs, p, n =>
    if 0 ≤ c then packShiftAux w (s + w) cs (p + (c.toNat <<< s)) n
    else packShiftAux w (s + w) cs p (n + ((-c).toNat <<< s))

theorem packShiftAux_eq (w : ℕ) (cs : List ℤ) :
    ∀ (s p n : ℕ), packShiftAux w s cs p n = (p : ℤ) - n + 2 ^ s * packSum w cs := by
  induction cs with
  | nil => intro s p n; simp [packShiftAux, packSum_nil]
  | cons c cs ih =>
    intro s p n
    rw [packShiftAux, packSum_cons]
    split_ifs with h
    · rw [ih, Nat.shiftLeft_eq]
      have : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg h
      push_cast
      rw [this, pow_add]
      ring
    · rw [ih, Nat.shiftLeft_eq]
      have : (((-c).toNat : ℕ) : ℤ) = -c := Int.toNat_of_nonneg (by omega)
      push_cast
      rw [this, pow_add]
      ring

/-- The kernel packing: leaf chunks of `16` slots, merged by `packTree` (`64` levels suffice for
any list; the fallback keeps the value exact regardless). -/
def packShift (w : ℕ) (cs : List ℤ) : ℤ :=
  let r := packTree 64 (w * 16) (packLeavesAux w 16 16 0 0 0 cs)
  (r.1 : ℤ) - r.2

theorem pairVal_packMerge (W : ℕ) : ∀ xs : List (ℕ × ℕ),
    pairVal (2 * W) (packMerge W xs) = pairVal W xs
  | x :: y :: xs => by
    rw [packMerge, pairVal, pairVal_packMerge W xs, pairVal, pairVal, Nat.shiftLeft_eq,
      Nat.shiftLeft_eq]
    push_cast
    rw [two_mul, pow_add]
    ring
  | [] => by simp [packMerge, pairVal]
  | [x] => by simp [packMerge, pairVal]

theorem packFold_eq (W : ℕ) : ∀ xs : List (ℕ × ℕ),
    ((packFold W xs).1 : ℤ) - (packFold W xs).2 = pairVal W xs
  | [] => by simp [packFold, pairVal]
  | x :: xs => by
    have ih := packFold_eq W xs
    simp only [packFold, pairVal, Nat.shiftLeft_eq]
    push_cast
    rw [← ih]
    ring

theorem packTree_eq : ∀ (f W : ℕ) (xs : List (ℕ × ℕ)),
    ((packTree f W xs).1 : ℤ) - (packTree f W xs).2 = pairVal W xs
  | _, _, [] => by simp [packTree, pairVal]
  | f, W, [x] => by cases f <;> simp [packTree, pairVal]
  | 0, W, x :: y :: xs => packFold_eq W (x :: y :: xs)
  | f + 1, W, x :: y :: xs =>
    (packTree_eq f (2 * W) _).trans (pairVal_packMerge W (x :: y :: xs))

theorem packLeavesAux_eq (w k : ℕ) (hk : 0 < k) : ∀ (cs : List ℤ) (j s p n : ℕ),
    s + w * j = w * k →
      pairVal (w * k) (packLeavesAux w k j s p n cs) = (p : ℤ) - n + 2 ^ s * packSum w cs
  | [], j, s, p, n, _ => by simp [packLeavesAux, pairVal, packSum_nil]
  | c :: cs, j + 1, s, p, n, hs => by
    have hs' : s + w + w * j = w * k := by rw [← hs]; ring
    rw [packLeavesAux, packSum_cons]
    split_ifs with h
    · rw [packLeavesAux_eq w k hk cs j (s + w) _ _ hs', Nat.shiftLeft_eq]
      have : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg h
      push_cast
      rw [this, pow_add]
      ring
    · rw [packLeavesAux_eq w k hk cs j (s + w) _ _ hs', Nat.shiftLeft_eq]
      have : (((-c).toNat : ℕ) : ℤ) = -c := Int.toNat_of_nonneg (by omega)
      push_cast
      rw [this, pow_add]
      ring
  | c :: cs, 0, s, p, n, hs => by
    have hs' : w + w * (k - 1) = w * k := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    simp only [Nat.mul_zero, Nat.add_zero] at hs
    rw [packLeavesAux, packSum_cons, pairVal]
    split_ifs with h
    · rw [packLeavesAux_eq w k hk cs (k - 1) w _ _ hs', hs]
      have : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg h
      push_cast
      rw [this]
      ring
    · rw [packLeavesAux_eq w k hk cs (k - 1) w _ _ hs', hs]
      have : (((-c).toNat : ℕ) : ℤ) = -c := Int.toNat_of_nonneg (by omega)
      push_cast
      rw [this]
      ring

/-- **Packing correctness.** -/
theorem packShift_eq (w : ℕ) (cs : List ℤ) : packShift w cs = packSum w cs := by
  rw [packShift, packTree_eq, packLeavesAux_eq w 16 (by norm_num) cs 16 0 0 0 (by ring)]
  simp

/-- Every slot fits a signed `w`-bit slot. -/
def SlotsBounded (w : ℕ) (cs : List ℤ) : Prop := ∀ c ∈ cs, 2 * |c| < 2 ^ w

/-- **Injectivity under the slot bound** (borrows between signed slots are harmless). -/
theorem packSum_injective {w : ℕ} {cs ds : List ℤ} (hc : SlotsBounded w cs)
    (hd : SlotsBounded w ds) (hl : cs.length = ds.length) (h : packSum w cs = packSum w ds) :
    cs = ds := by
  induction cs generalizing ds with
  | nil => exact (List.length_eq_zero_iff.mp hl.symm).symm
  | cons c cs ih =>
    cases ds with
    | nil => simp at hl
    | cons d ds =>
      rw [packSum_cons, packSum_cons] at h
      have h1 := hc c (by simp)
      have h2 := hd d (by simp)
      have hw : (0 : ℤ) < 2 ^ w := by positivity
      have hcd : c - d = 2 ^ w * (packSum w ds - packSum w cs) := by linarith
      have hz : packSum w ds - packSum w cs = 0 := by
        by_contra hne
        have : (1 : ℤ) ≤ |packSum w ds - packSum w cs| := Int.one_le_abs hne
        have h3 : |c - d| = 2 ^ w * |packSum w ds - packSum w cs| := by
          rw [hcd, abs_mul, abs_of_pos hw]
        have h4 : |c - d| ≤ |c| + |d| := abs_sub _ _
        nlinarith
      have hcd0 : c = d := by rw [hz] at hcd; linarith
      subst hcd0
      have hX : packSum w cs = packSum w ds := by linarith
      rw [ih (fun x hx => hc x (by simp [hx])) (fun x hx => hd x (by simp [hx]))
        (by simpa using hl) hX]

/-- One-dimensional convolution, length `|a| + |b| - 1` (empty if a factor is empty). -/
def listConv (a b : List ℤ) : List ℤ :=
  if a.isEmpty || b.isEmpty then []
  else (List.range (a.length + b.length - 1)).map fun k =>
    ((List.range (k + 1)).map fun i => a.getD i 0 * b.getD (k - i) 0).sum

/-- The product of two truncated geometric sums with vanishing tails, regrouped by total index
(Cauchy product; via polynomial evaluation). -/
theorem sum_mul_sum_range_cauchy (f g : ℕ → ℤ) (m n : ℕ) (hf : ∀ i, m ≤ i → f i = 0)
    (hg : ∀ j, n ≤ j → g j = 0) (Y : ℤ) :
    (∑ i ∈ Finset.range m, f i * Y ^ i) * (∑ j ∈ Finset.range n, g j * Y ^ j) =
      ∑ s ∈ Finset.range (m + n - 1), (∑ i ∈ Finset.range (s + 1), f i * g (s - i)) * Y ^ s := by
  open Polynomial in
  by_cases hm : m = 0
  · subst hm
    simp only [Finset.range_zero, Finset.sum_empty, zero_mul]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    rw [Finset.sum_eq_zero fun i _ => by rw [hf i (Nat.zero_le _)]; simp]
    simp
  by_cases hn : n = 0
  · subst hn
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    rw [Finset.sum_eq_zero fun i _ => by rw [hg _ (Nat.zero_le _)]; simp]
    simp
  open Polynomial in
  set F : ℤ[X] := ∑ i ∈ Finset.range m, C (f i) * X ^ i with hF
  open Polynomial in
  set G : ℤ[X] := ∑ i ∈ Finset.range n, C (g i) * X ^ i with hG
  have cF : ∀ i, F.coeff i = f i := by
    intro i
    rw [hF, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    by_cases hi : i < m
    · simp [Finset.sum_ite_eq, hi]
    · simp [hi, hf i (not_lt.mp hi)]
  have cG : ∀ i, G.coeff i = g i := by
    intro i
    rw [hG, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    by_cases hi : i < n
    · simp [Finset.sum_ite_eq, hi]
    · simp [hi, hg i (not_lt.mp hi)]
  have eF : F.eval Y = ∑ i ∈ Finset.range m, f i * Y ^ i := by
    rw [hF, Polynomial.eval_finsetSum]; simp
  have eG : G.eval Y = ∑ i ∈ Finset.range n, g i * Y ^ i := by
    rw [hG, Polynomial.eval_finsetSum]; simp
  have cFG : ∀ s, (F * G).coeff s = ∑ i ∈ Finset.range (s + 1), f i * g (s - i) := by
    intro s
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [cF, cG]
  have hdeg : (F * G).natDegree < m + n - 1 := by
    have : (F * G).natDegree ≤ m + n - 2 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [cFG]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_range] at hi
      by_cases h1 : m ≤ i
      · rw [hf i h1]; simp
      · rw [hg (N - i) (by omega)]; simp
    omega
  rw [← eF, ← eG, ← Polynomial.eval_mul, Polynomial.eval_eq_sum_range' hdeg]
  exact Finset.sum_congr rfl fun s _ => by rw [cFG]

/-- **Kronecker substitution**: packing turns convolution into ONE integer product (it is
polynomial evaluation at `2^w`; no bound is needed). -/
theorem packSum_listConv (w : ℕ) (a b : List ℤ) :
    packSum w (listConv a b) = packSum w a * packSum w b := by
  by_cases hab : a.isEmpty || b.isEmpty
  · have : listConv a b = [] := by simp [listConv, hab]
    rw [this, packSum_nil]
    rcases Bool.or_eq_true_iff.mp hab with h | h
    · rw [List.isEmpty_iff.mp h, packSum_nil, zero_mul]
    · rw [List.isEmpty_iff.mp h, packSum_nil, mul_zero]
  · have hl : listConv a b = (List.range (a.length + b.length - 1)).map fun k =>
        ((List.range (k + 1)).map fun i => a.getD i 0 * b.getD (k - i) 0).sum := by
      simp [listConv, hab]
    rw [packSum_eq_sum, packSum_eq_sum, packSum_eq_sum,
      sum_mul_sum_range_cauchy (fun i => a.getD i 0) (fun j => b.getD j 0) a.length b.length
        (fun i hi => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi])
        (fun j hj => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]), hl]
    simp only [List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    have : ((List.range (a.length + b.length - 1)).map fun k =>
        ((List.range (k + 1)).map fun i => a.getD i 0 * b.getD (k - i) 0).sum).getD s 0 =
        ((List.range (s + 1)).map fun i => a.getD i 0 * b.getD (s - i) 0).sum := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hs)]
      simp
    rw [this, sum_map_range_eq]

/-- The largest absolute value of a slot. -/
def maxAbs (cs : List ℤ) : ℕ := cs.foldr (fun c m => max c.natAbs m) 0

theorem natAbs_le_maxAbs {cs : List ℤ} {c : ℤ} (h : c ∈ cs) : c.natAbs ≤ maxAbs cs := by
  induction cs with
  | nil => simp at h
  | cons d cs ih =>
    rw [maxAbs, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem abs_getD_le (cs : List ℤ) (i : ℕ) : |cs.getD i 0| ≤ (maxAbs cs : ℤ) := by
  by_cases hi : i < cs.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      Int.abs_eq_natAbs]
    exact_mod_cast natAbs_le_maxAbs (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]
    simp

/-- Cheap sufficient test that the exact convolution fits the slots:
`2 · min(|a|, |b|) · max|a_i| · max|b_j| < 2^w`. -/
def convFits (w : ℕ) (a b : List ℤ) : Bool :=
  decide (2 * min a.length b.length * maxAbs a * maxAbs b < 2 ^ w)

/-- One convolution entry is at most `min(|a|,|b|) · max|a| · max|b|` in absolute value. -/
theorem abs_conv_entry_le (a b : List ℤ) (k : ℕ) :
    |∑ i ∈ Finset.range (k + 1), a.getD i 0 * b.getD (k - i) 0| ≤
      (min a.length b.length : ℕ) * (maxAbs a : ℤ) * (maxAbs b : ℤ) := by
  set S := (Finset.range (k + 1)).filter fun i => i < a.length ∧ k - i < b.length with hS
  have hz : ∀ i ∈ Finset.range (k + 1), i ∉ S → a.getD i 0 * b.getD (k - i) 0 = 0 := by
    intro i hik hi
    rw [hS, Finset.mem_filter] at hi
    by_cases h1 : i < a.length
    · have h2 : ¬ k - i < b.length := fun h2 => hi ⟨hik, h1, h2⟩
      rw [List.getD_eq_getElem?_getD (l := b), List.getElem?_eq_none (not_lt.mp h2)]
      simp
    · rw [List.getD_eq_getElem?_getD (l := a), List.getElem?_eq_none (not_lt.mp h1)]
      simp
  have hcard : S.card ≤ min a.length b.length := by
    refine le_min ?_ ?_
    · calc S.card ≤ (Finset.range a.length).card :=
            Finset.card_le_card fun i hi => by
              rw [hS, Finset.mem_filter] at hi
              exact Finset.mem_range.mpr hi.2.1
        _ = a.length := Finset.card_range _
    · calc S.card ≤ (Finset.range b.length).card :=
            Finset.card_le_card_of_injOn (fun i => k - i)
              (fun i hi => by
                rw [Finset.mem_coe, hS, Finset.mem_filter] at hi
                exact Finset.mem_range.mpr hi.2.2)
              (fun i hi j hj hij => by
                rw [Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_range] at hi hj
                simp only at hij
                omega)
        _ = b.length := Finset.card_range _
  calc |∑ i ∈ Finset.range (k + 1), a.getD i 0 * b.getD (k - i) 0|
      ≤ ∑ i ∈ Finset.range (k + 1), |a.getD i 0 * b.getD (k - i) 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S, |a.getD i 0 * b.getD (k - i) 0| := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hn => ?_
        rw [hz i hi hn]; simp
    _ ≤ ∑ _i ∈ S, ((maxAbs a : ℤ) * (maxAbs b : ℤ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_getD_le a i) (abs_getD_le b _) (abs_nonneg _) (by positivity)
    _ = S.card * ((maxAbs a : ℤ) * (maxAbs b : ℤ)) := by simp
    _ ≤ (min a.length b.length : ℕ) * (maxAbs a : ℤ) * (maxAbs b : ℤ) := by
        have hc' : (S.card : ℤ) ≤ ((min a.length b.length : ℕ) : ℤ) := by exact_mod_cast hcard
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc' (by positivity))
          (by positivity)

theorem slotsBounded_listConv {w : ℕ} {a b : List ℤ} (h : convFits w a b = true) :
    SlotsBounded w (listConv a b) := by
  intro c hc
  have hf : 2 * min a.length b.length * maxAbs a * maxAbs b < 2 ^ w := by
    simpa [convFits] using h
  unfold listConv at hc
  split_ifs at hc with he
  · simp at hc
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hc
  rw [sum_map_range_eq]
  have h1 := abs_conv_entry_le a b k
  have h2 : (2 * min a.length b.length * maxAbs a * maxAbs b : ℕ) < 2 ^ w := hf
  have h3 : 2 * ((min a.length b.length : ℕ) : ℤ) * (maxAbs a : ℤ) * (maxAbs b : ℤ) < 2 ^ w := by
    exact_mod_cast h2
  linarith

/-- The packing of a block-flattened list as a sum over blocks. -/
theorem packSum_flatten (w L : ℕ) (A : List (List ℤ)) (hA : ∀ x ∈ A, x.length = L) :
    packSum w A.flatten =
      ∑ i ∈ Finset.range A.length, packSum w (A.getD i []) * (2 ^ (w * L)) ^ i := by
  induction A with
  | nil => simp [packSum_nil]
  | cons x A ih =>
    have hx : x.length = L := hA x (by simp)
    rw [List.flatten_cons, packSum_append, hx, ih (fun y hy => hA y (by simp [hy])),
      List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

/-- **Shard decomposition**: with both factors cut into blocks of `L` slots, the packed product
is the shifted sum of the shard sums `Σ_{i+j=s} pack(A_i)·pack(B_j)`. -/
theorem packSum_flatten_mul_shards (w L : ℕ) (A B : List (List ℤ))
    (hA : ∀ x ∈ A, x.length = L) (hB : ∀ x ∈ B, x.length = L) :
    packSum w A.flatten * packSum w B.flatten =
      ∑ s ∈ Finset.range (A.length + B.length - 1), 2 ^ (w * L * s) *
        ∑ i ∈ Finset.range (s + 1), packSum w (A.getD i []) * packSum w (B.getD (s - i) []) := by
  rw [packSum_flatten w L A hA, packSum_flatten w L B hB,
    sum_mul_sum_range_cauchy (fun i => packSum w (A.getD i [])) (fun j => packSum w (B.getD j []))
      A.length B.length
      (fun i hi => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, packSum_nil])
      (fun j hj => by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj, packSum_nil])]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [pow_mul 2 (w * L) s, mul_comm]

/-- The signed slot read off the residue `r` of a width-`w` slot (`m = 2^w`). -/
def slotRep (m r : ℤ) : ℤ := if 2 * r < m then r else r - m

/-- Slot decoding loop: peel `len` slots from `X`, testing slot `i + j` against `logs (i + j)`. -/
def intSlotsBoundAux (w : ℕ) (logs : ℕ → ℕ) : ℕ → ℕ → ℤ → Bool
  | 0, _, X => decide (X = 0)
  | len + 1, i, X =>
    let m : ℤ := ((2 ^ w : ℕ) : ℤ)
    let e := slotRep m (X % m)
    decide (e.natAbs ≤ 2 ^ logs i) && intSlotsBoundAux w logs len (i + 1) ((X - e) / m)


theorem intSlotsBoundAux_sound {w : ℕ} {logs : ℕ → ℕ} (len : ℕ) :
    ∀ (i : ℕ) (X : ℤ), intSlotsBoundAux w logs len i X = true →
      ∃ e : List ℤ, e.length = len ∧ (∀ j < len, |e.getD j 0| ≤ 2 ^ logs (i + j)) ∧
        X = packSum w e := by
  induction len with
  | zero =>
    intro i X h
    refine ⟨[], rfl, fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
    simpa [intSlotsBoundAux, packSum_nil] using h
  | succ len ih =>
    intro i X h
    simp only [intSlotsBoundAux, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, hrest⟩ := h
    obtain ⟨e', hl, hbd, hX'⟩ := ih _ _ hrest
    set m : ℤ := ((2 ^ w : ℕ) : ℤ) with hm
    have hmpos : 0 < m := by rw [hm]; positivity
    set e0 := slotRep m (X % m) with he0
    have hdvd : m ∣ X - e0 := by
      have h1 : m ∣ X - X % m := ⟨X / m, by
        have := Int.mul_ediv_add_emod X m; linarith⟩
      unfold slotRep at he0
      split_ifs at he0
      · rw [he0]; exact h1
      · rw [he0]
        have : X - (X % m - m) = (X - X % m) + m := by ring
        rw [this]; exact dvd_add h1 dvd_rfl
    have hXe : X = e0 + m * ((X - e0) / m) := by
      rw [Int.mul_ediv_cancel' hdvd]; ring
    refine ⟨e0 :: e', by simp [hl], ?_, ?_⟩
    · intro j hj
      cases j with
      | zero =>
        simp only [List.getD_cons_zero, add_zero]
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hb
      | succ j =>
        simp only [List.getD_cons_succ]
        have := hbd j (by omega)
        rwa [show i + (j + 1) = i + 1 + j by ring]
    · rw [packSum_cons, ← hX']
      simpa [hm] using hXe

/-! ### Slot decoding on an offset natural number

Adding the offset `Σ_j 2^(w-1) 2^(w j)` turns `len` signed slots in `(-2^(w-1), 2^(w-1))` into
the base-`2^w` digits of a natural number. `natSlotsSh` splits that number in balanced halves by
mask and shift (`&&&`, `>>>`, kernel-accelerated, no division), down to blocks of `16` slots read
digit by digit (`natSlotsAux`). -/

/-- Digit-by-digit reading: `len` digits of `N` from slot `i`, digit `d` within
`2^(logs i)` of `2^(w-1)`, and nothing left over. -/
def natSlotsAux (w : ℕ) (logs : ℕ → ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, N => N == 0
  | len + 1, i, N =>
    decide (N &&& (2 ^ w - 1) ≤ 2 ^ (w - 1) + 2 ^ logs i) &&
      decide (2 ^ (w - 1) ≤ (N &&& (2 ^ w - 1)) + 2 ^ logs i) &&
      natSlotsAux w logs len (i + 1) (N >>> w)

/-- Balanced reading: the low `len / 2` digits by mask, the rest by shift (`fuel` levels). -/
def natSlotsSh (w : ℕ) (logs : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, len, i, N => natSlotsAux w logs len i N
  | f + 1, len, i, N =>
    if len ≤ 16 then natSlotsAux w logs len i N else
      natSlotsSh w logs f (len / 2) i (N &&& (2 ^ (w * (len / 2)) - 1)) &&
        natSlotsSh w logs f (len - len / 2) (i + len / 2) (N >>> (w * (len / 2)))

/-- The offset `Σ_{j < len} 2^(w-1) 2^(w j)`, in closed form. -/
def slotOffset (w len : ℕ) : ℕ := 2 ^ (w - 1) * ((2 ^ (w * len) - 1) / (2 ^ w - 1))

/-- Slot decoding by bounds: decode `len` signed slots of `X` (width `w`) and test
`|e_i| ≤ 2^(logs i)` and that nothing is left over (on the offset natural number `X + offset`,
by `natSlotsSh`; `64` levels suffice for any length, and the digit-by-digit fallback keeps the
test exact regardless). -/
def intSlotsBound (w len : ℕ) (logs : ℕ → ℕ) (X : ℤ) : Bool :=
  decide (0 < w) && decide (0 ≤ X + slotOffset w len) &&
    natSlotsSh w logs 64 len 0 (X + slotOffset w len).toNat

/-- What a passing reading certifies about `N`. -/
def NatSlotsSpec (w : ℕ) (logs : ℕ → ℕ) (len i N : ℕ) : Prop :=
  ∃ ds : List ℕ, ds.length = len ∧
    (∀ j < len, |(ds.getD j 0 : ℤ) - 2 ^ (w - 1)| ≤ 2 ^ logs (i + j)) ∧
      (N : ℤ) = packSum w (ds.map Nat.cast)

theorem natSlotsAux_sound {w : ℕ} {logs : ℕ → ℕ} : ∀ (len i N : ℕ),
    natSlotsAux w logs len i N = true → NatSlotsSpec w logs len i N
  | 0, i, N, h => ⟨[], rfl, fun j hj => absurd hj (Nat.not_lt_zero _), by
      simp only [natSlotsAux, beq_iff_eq] at h; simp [h, packSum_nil]⟩
  | len + 1, i, N, h => by
    simp only [natSlotsAux, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ds, hl, hb, hN⟩ := natSlotsAux_sound len (i + 1) _ h3
    rw [Nat.and_two_pow_sub_one_eq_mod] at h1 h2
    refine ⟨N % 2 ^ w :: ds, by simp [hl], fun j hj => ?_, ?_⟩
    · cases j with
      | zero =>
        simp only [List.getD_cons_zero, Nat.add_zero]
        have e1 : ((N % 2 ^ w : ℕ) : ℤ) ≤ 2 ^ (w - 1) + 2 ^ logs i := by exact_mod_cast h1
        have e2 : (2 : ℤ) ^ (w - 1) ≤ ((N % 2 ^ w : ℕ) : ℤ) + 2 ^ logs i := by exact_mod_cast h2
        rw [abs_le]
        constructor <;> linarith
      | succ j =>
        simp only [List.getD_cons_succ]
        have := hb j (by omega)
        rwa [show i + 1 + j = i + (j + 1) by omega] at this
    · rw [List.map_cons, packSum_cons, ← hN, Nat.shiftRight_eq_div_pow]
      have := Nat.mod_add_div N (2 ^ w)
      exact_mod_cast this.symm

theorem natSlotsSh_sound {w : ℕ} {logs : ℕ → ℕ} : ∀ (f len i N : ℕ),
    natSlotsSh w logs f len i N = true → NatSlotsSpec w logs len i N
  | 0, len, i, N, h => natSlotsAux_sound len i N h
  | f + 1, len, i, N, h => by
    rw [natSlotsSh] at h
    split_ifs at h with hl
    · exact natSlotsAux_sound len i N h
    simp only [Bool.and_eq_true] at h
    obtain ⟨d1, hl1, hb1, hN1⟩ := natSlotsSh_sound f _ _ _ h.1
    obtain ⟨d2, hl2, hb2, hN2⟩ := natSlotsSh_sound f _ _ _ h.2
    refine ⟨d1 ++ d2, by simp [hl1, hl2]; omega, fun j hj => ?_, ?_⟩
    · by_cases hj1 : j < len / 2
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
        exact hb1 j hj1
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl1,
          ← List.getD_eq_getElem?_getD]
        have := hb2 (j - len / 2) (by omega)
        rwa [show i + len / 2 + (j - len / 2) = i + j by omega] at this
    · rw [List.map_append, packSum_append, List.length_map, hl1, ← hN1, ← hN2,
        Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
      have := Nat.mod_add_div N (2 ^ (w * (len / 2)))
      exact_mod_cast this.symm

theorem packSum_replicate (w len : ℕ) (c : ℤ) :
    packSum w (List.replicate len c) = c * ∑ j ∈ Finset.range len, (2 ^ w : ℤ) ^ j := by
  rw [packSum_eq_sum, List.length_replicate, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt (Finset.mem_range.mp hj)]
  rfl

theorem slotOffset_eq {w : ℕ} (hw : 0 < w) (len : ℕ) :
    (slotOffset w len : ℤ) = packSum w (List.replicate len (2 ^ (w - 1))) := by
  rw [packSum_replicate, slotOffset, pow_mul, ← Nat.geomSum_eq (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw)]
  push_cast
  ring

theorem packSum_map_sub (w : ℕ) (c : ℤ) : ∀ ds : List ℤ,
    packSum w (ds.map fun d => d - c) = packSum w ds - packSum w (List.replicate ds.length c)
  | [] => by simp [packSum_nil]
  | d :: ds => by
    rw [List.map_cons, List.length_cons, List.replicate_succ, packSum_cons, packSum_cons,
      packSum_cons, packSum_map_sub w c ds]
    ring

theorem intSlotsBound_sound {w len : ℕ} {logs : ℕ → ℕ} {X : ℤ}
    (h : intSlotsBound w len logs X = true) :
    ∃ e : List ℤ, e.length = len ∧ (∀ i < len, |e.getD i 0| ≤ 2 ^ logs i) ∧ X = packSum w e := by
  simp only [intSlotsBound, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hw, h0⟩, hs⟩ := h
  obtain ⟨ds, hl, hb, hN⟩ := natSlotsSh_sound 64 len 0 _ hs
  refine ⟨(ds.map Nat.cast).map fun d => d - 2 ^ (w - 1), by simp [hl], fun i hi => ?_, ?_⟩
  · have := hb i hi
    rw [Nat.zero_add] at this
    have hi' : i < ds.length := by omega
    simpa [List.getD_eq_getElem?_getD, hi'] using this
  · rw [packSum_map_sub, ← hN, List.length_map, hl, ← slotOffset_eq hw, Int.toNat_of_nonneg h0]
    ring

-- Kernel sanity checks: packing and slot decoding reduce by `decide +kernel`.
example : packShift 8 [3, -1, 2] = 3 - 256 + 2 * 65536 := by decide +kernel
example : intSlotsBound 8 3 (fun _ => 0) (packShift 8 [3, -1, 2]) = false := by decide +kernel
example : intSlotsBound 8 3 (fun i => if i = 2 then 1 else 2) (packShift 8 [3, -1, 2]) = true := by
  decide +kernel

end KAM.Certificate
