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
kernel packing `packShift` accumulates the positive and negative parts separately with
`Nat.shiftLeft` and subtracts once. Under the slot bound the packing is injective
(`packSum_injective`), packing turns convolution into one product (`packSum_listConv`), the
packed product of block-cut factors is a shifted sum of shard sums
(`packSum_flatten_mul_shards`), and `intSlotsBound` decodes slots of a big integer by bounds.
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
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

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

/-- The kernel packing loop: the shift `s` advances by `w` per slot. -/
def packShiftAux (w : ℕ) : ℕ → List ℤ → ℕ → ℕ → ℤ
  | _, [], p, n => (p : ℤ) - (n : ℤ)
  | s, c :: cs, p, n =>
    if 0 ≤ c then packShiftAux w (s + w) cs (p + (c.toNat <<< s)) n
    else packShiftAux w (s + w) cs p (n + ((-c).toNat <<< s))

/-- The kernel packing (SO-REPLAY2 `soShLoop`): positive and negative parts accumulated
separately as `Nat`s with `Nat.shiftLeft`, one subtraction at the end. -/
def packShift (w : ℕ) (cs : List ℤ) : ℤ := packShiftAux w 0 cs 0 0

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

/-- **Packing correctness.** -/
theorem packShift_eq (w : ℕ) (cs : List ℤ) : packShift w cs = packSum w cs := by
  rw [packShift, packShiftAux_eq]
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

end KAM.Certificate
