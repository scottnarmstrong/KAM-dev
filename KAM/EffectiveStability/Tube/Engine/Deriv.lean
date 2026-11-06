/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Block

/-!
# The packed angle derivative (T2-CONF, N7)

`∂_a (evalK (Layout.key C S) p d) = evalK … (!p) (dlist … a p d)` multiplies slot `i` by
`psgn p · k_a(i)` (`k_0 = column - C`, `k_1 = row - C`). On the packed value this is not one
GMP operation; `derivZ` does it with `2C+1` masked parts: the offset form `Y = Z + Σ 2^l 2^(w i)`
is cut by one column (or row) mask at a time, each part is weighted by its index, and the
offsets are removed (`packSum_dlist`: `derivZ = packSum w (dlist …)`).

* `natPack_land_zip`: digitwise `AND` of two packings;
* `colMask`, `rowMask` (closed forms), `colPart`, `rowPart`, `derivZ`, `packSum_dlist`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- **Digitwise `AND`** of two packings with digits below `2^w`. -/
theorem natPack_land_zip {w : ℕ} : ∀ (es ms : List ℕ), es.length = ms.length →
    (∀ e ∈ es, e < 2 ^ w) → (∀ m ∈ ms, m < 2 ^ w) →
    natPack w es &&& natPack w ms = natPack w (List.zipWith (· &&& ·) es ms)
  | [], [], _, _, _ => by simp [natPack_nil]
  | e :: es, m :: ms, hl, he, hm => by
    simp only [List.zipWith_cons_cons, natPack_cons]
    rw [land_split (he e (by simp)) (hm m (by simp)),
      natPack_land_zip es ms (by simpa using hl) (fun x hx => he x (by simp [hx]))
        (fun x hx => hm x (by simp [hx]))]
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

theorem natPack_range_land {w N : ℕ} (y m : ℕ → ℕ) (hy : ∀ i < N, y i < 2 ^ w)
    (hm : ∀ i < N, m i < 2 ^ w) :
    natPack w ((List.range N).map y) &&& natPack w ((List.range N).map m) =
      natPack w ((List.range N).map fun i => y i &&& m i) := by
  rw [natPack_land_zip _ _ (by simp) (fun e he => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he; exact hy i (List.mem_range.mp hi))
    (fun e he => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he; exact hm i (List.mem_range.mp hi))]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- Sums over the slots of column `c` of the square layout. -/
theorem sum_col {M : Type*} [AddCommMonoid M] {C S c : ℕ} (hKS : 2 * C + 1 ≤ S) (hc : c ≤ 2 * C)
    (f : ℕ → M) :
    ∑ i ∈ range (Layout.len C S), (if i % S = c then f i else 0) =
      ∑ r ∈ range (2 * C + 1), f (c + S * r) := by
  set K := 2 * C + 1 with hK
  have hlen : Layout.len C S ≤ S * K := by unfold Layout.len; rw [hK]; nlinarith
  rw [sum_subset (range_subset_range.mpr hlen) (fun i hi hn => by
    rw [mem_range, not_lt] at hn
    split_ifs with h
    · exfalso
      have h1 := Nat.mod_add_div i S
      have h2 : i / S < K := by
        have := mem_range.mp hi
        rw [Nat.div_lt_iff_lt_mul (by omega)]; nlinarith
      have : S * (i / S) ≤ S * (2 * C) := Nat.mul_le_mul_left _ (by omega)
      unfold Layout.len at hn
      nlinarith
    · rfl), sum_range_mul_regroup S _ K]
  refine sum_congr rfl fun r hr => ?_
  rw [sum_eq_single c]
  · rw [if_pos (mod_div_of_lt (by omega)).1]
  · intro c' _ hne
    rw [if_neg (by rw [(mod_div_of_lt (mem_range.mp ‹_›)).1]; exact hne)]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- Sums over the valid slots of row `r` of the square layout. -/
theorem sum_row {M : Type*} [AddCommMonoid M] {C S r : ℕ} (hKS : 2 * C + 1 ≤ S) (hr : r ≤ 2 * C)
    (f : ℕ → M) :
    ∑ i ∈ range (Layout.len C S), (if i / S = r ∧ i % S < 2 * C + 1 then f i else 0) =
      ∑ c ∈ range (2 * C + 1), f (c + S * r) := by
  set K := 2 * C + 1 with hK
  have hlen : Layout.len C S ≤ S * K := by unfold Layout.len; rw [hK]; nlinarith
  rw [sum_subset (range_subset_range.mpr hlen) (fun i hi hn => by
    rw [mem_range, not_lt] at hn
    split_ifs with h
    · exfalso
      have h1 := Nat.mod_add_div i S
      rw [h.1] at h1
      have : S * r ≤ S * (2 * C) := Nat.mul_le_mul_left _ hr
      have e : 2 * C * S = S * (2 * C) := by ring
      unfold Layout.len at hn
      omega
    · rfl), sum_range_mul_regroup S _ K]
  rw [sum_eq_single r]
  · rw [← sum_subset (range_subset_range.mpr hKS) (fun c hc hn => by
      rw [mem_range, not_lt] at hn
      rw [if_neg (by rw [(mod_div_of_lt (mem_range.mp hc)).1]; omega)])]
    refine sum_congr rfl fun c hc => ?_
    have hc' := mem_range.mp hc
    rw [if_pos ⟨(mod_div_of_lt (by omega)).2, by rw [(mod_div_of_lt (by omega)).1]; exact hc'⟩]
  · intro r' _ hne
    refine sum_eq_zero fun c hc => ?_
    rw [if_neg (by rw [(mod_div_of_lt (mem_range.mp hc)).2]; exact fun h => hne h.1)]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- The mask of column `c`: digit `2^w - 1` on the slots `c + S r`, `r ≤ 2C`. -/
def colMask (w S C c : ℕ) : ℕ := (2 ^ w - 1) * 2 ^ (w * c) * periodic (S * w) (2 * C + 1) 1

/-- The mask of row `r`: digit `2^w - 1` on the valid slots `c + S r`, `c ≤ 2C`. -/
def rowMask (w S C r : ℕ) : ℕ := (2 ^ (w * (2 * C + 1)) - 1) * 2 ^ (S * w * r)

/-- The offset `Σ_{i<N} 2^l 2^(w i)` of the layout. -/
def offP (w S C l : ℕ) : ℕ := periodic w (Layout.len C S) (2 ^ l)

/-- The offset form of a packed value. -/
def yOf (w S C l : ℕ) (Z : ℤ) : ℕ := (Z + offP w S C l).toNat

/-- The part of column `c` (signed). -/
def colPart (w S C l c : ℕ) (Z : ℤ) : ℤ :=
  ((yOf w S C l Z &&& colMask w S C c : ℕ) : ℤ) - ((offP w S C l &&& colMask w S C c : ℕ) : ℤ)

/-- The part of row `r` (signed). -/
def rowPart (w S C l r : ℕ) (Z : ℤ) : ℤ :=
  ((yOf w S C l Z &&& rowMask w S C r : ℕ) : ℤ) - ((offP w S C l &&& rowMask w S C r : ℕ) : ℤ)

/-- **The packed angle derivative** (kernel): `psgn p · Σ_c (c - C) · part_c` (`a = 0`) or the
same over the rows (`a = 1`). -/
def derivZ (w S C l : ℕ) (a : Fin 2) (p : Bool) (Z : ℤ) : ℤ :=
  psgn p * (if a = 0 then ((List.range (2 * C + 1)).map fun (c : ℕ) => ((c : ℤ) - C) * colPart w S C l c Z).sum
    else ((List.range (2 * C + 1)).map fun (r : ℕ) => ((r : ℤ) - C) * rowPart w S C l r Z).sum)

theorem geom_sub_one (w K : ℕ) : ∑ c ∈ range K, (2 ^ w - 1) * 2 ^ (w * c) = 2 ^ (w * K) - 1 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, Nat.mul_succ, pow_add]
    have h1 : 1 ≤ 2 ^ (w * K) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    zify [h1, h2, Nat.one_le_two_pow (n := w * K + w)]
    rw [Nat.cast_sub (by nlinarith [Nat.one_le_two_pow (n := w * K) , Nat.one_le_two_pow (n := w)])]
    push_cast
    ring

/-- **The packed angle derivative is the packing of the derivative list.** -/
theorem packSum_dlist {w S C l : ℕ} (hKS : 2 * C + 1 ≤ S) (hlw : l + 1 ≤ w) {d : List ℤ} {Z : ℤ}
    (hZ : packSum w d = Z) (hc : colsOk C S d = true) (hlen : d.length ≤ Layout.len C S)
    (hb : ∀ x ∈ d, -2 ^ l ≤ x ∧ x < 2 ^ l) (a : Fin 2) (p : Bool) :
    derivZ w S C l a p Z = packSum w (dlist (Layout.key C S) a p d) := by
  set N := Layout.len C S with hN
  set K := 2 * C + 1 with hK
  have hw : 0 < w := by omega
  have hS0 : 0 < S := by omega
  set D : ℕ → ℤ := fun i => d.getD i 0 with hDdef
  have hD : ∀ i, -2 ^ l ≤ D i ∧ D i < 2 ^ l := fun i => by
    by_cases hi : i < d.length
    · simp only [hDdef, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact hb _ (List.getElem_mem hi)
    · simp only [hDdef, List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi),
        Option.getD_none]
      constructor <;> [exact neg_nonpos.mpr (by positivity); positivity]
  have hD0 : ∀ i, 2 * C < i % S → D i = 0 := fun i hi => getD_eq_zero_of_colsOk hc hi
  set yf : ℕ → ℕ := fun i => (D i + 2 ^ l).toNat with hyf
  have hyfZ : ∀ i, (yf i : ℤ) = D i + 2 ^ l := fun i => Int.toNat_of_nonneg (by linarith [hD i])
  have hpl : (2 : ℕ) ^ (l + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hlw
  have hyflt : ∀ i, yf i < 2 ^ w := fun i => by
    have : (yf i : ℤ) < ((2 ^ (l + 1) : ℕ) : ℤ) := by rw [hyfZ]; push_cast; rw [pow_succ]; linarith [hD i]
    exact (by exact_mod_cast this : yf i < 2 ^ (l + 1)).trans_le hpl
  have hplw : (2 : ℕ) ^ l < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hmlt : 2 ^ w - 1 < 2 ^ w := Nat.sub_lt (Nat.two_pow_pos w) (by norm_num)
  -- the packed value, the offset and the offset form as digit sums
  have hZs : Z = ∑ i ∈ range N, D i * (2 ^ w) ^ i := by rw [← hZ, packSum_eq_sum_of_le w d hlen]
  have hoffN : offP w S C l = natPack w ((List.range N).map fun _ => 2 ^ l) := by
    rw [offP, periodic_eq_natPack hw, ← hN]
    congr 1
    simp [List.map_const']
  have hY : yOf w S C l Z = natPack w ((List.range N).map yf) := by
    have h1 : ((natPack w ((List.range N).map yf) : ℕ) : ℤ) = Z + (offP w S C l : ℤ) := by
      rw [natPack_range, hoffN, natPack_range, hZs]
      push_cast
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [hyfZ, pow_mul]; ring
    rw [yOf, ← h1, Int.toNat_natCast]
  have hdl : packSum w (dlist (Layout.key C S) a p d) =
      ∑ i ∈ range N, (psgn p * kc (Layout.key C S i) a * D i) * (2 ^ w) ^ i := by
    rw [packSum_eq_sum_of_le (n := N) w _ ((length_dlist _ _ _ _).le.trans hlen)]
    exact sum_congr rfl fun i _ => by rw [getD_dlist]
  -- a masked part as a digit sum
  have hpart : ∀ (P : ℕ → Prop) [DecidablePred P] (Mk : ℕ),
      Mk = natPack w ((List.range N).map fun i => if P i then 2 ^ w - 1 else 0) →
      ((yOf w S C l Z &&& Mk : ℕ) : ℤ) - ((offP w S C l &&& Mk : ℕ) : ℤ) =
        ∑ i ∈ range N, (if P i then D i else 0) * (2 ^ w) ^ i := by
    intro P _ Mk hMk
    have hm : ∀ i < N, (if P i then 2 ^ w - 1 else 0) < 2 ^ w := fun i _ => by
      split_ifs
      · exact hmlt
      · exact Nat.two_pow_pos w
    rw [hY, hMk, natPack_range_land _ _ (fun i _ => hyflt i) hm, hoffN,
      natPack_range_land _ _ (fun i _ => hplw) hm, natPack_range, natPack_range]
    push_cast
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with hP
    · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hyflt i), Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt hplw, hyfZ, pow_mul]
      push_cast
      ring
    · simp
  unfold derivZ
  rw [hdl]
  split_ifs with ha
  · -- columns
    have hcol : ∀ c ∈ range K, colPart w S C l c Z =
        ∑ i ∈ range N, (if i % S = c then D i else 0) * (2 ^ w) ^ i := by
      intro c hc
      have hc' := mem_range.mp hc
      refine hpart (fun i => i % S = c) _ ?_
      rw [colMask, natPack_range, periodic_one_eq_sum (Nat.mul_pos hS0 hw), mul_sum]
      have hite : ∀ i, (if i % S = c then 2 ^ w - 1 else 0) * 2 ^ (w * i) =
          if i % S = c then (2 ^ w - 1) * 2 ^ (w * i) else 0 := fun i => by split_ifs <;> simp
      rw [sum_congr rfl (fun i _ => hite i),
        sum_col (C := C) (S := S) (c := c) hKS (by omega) (fun i => (2 ^ w - 1) * 2 ^ (w * i))]
      refine sum_congr rfl fun r _ => ?_
      rw [mul_assoc, ← pow_add]
      congr 2
      ring
    subst ha
    rw [sum_map_range_g (fun c => ((c : ℤ) - C) * colPart w S C l c Z) K,
      sum_congr rfl (fun c hc => by rw [hcol c hc])]
    have hR : ∑ i ∈ range N, (psgn p * kc (Layout.key C S i) 0 * D i) * (2 ^ w : ℤ) ^ i =
        psgn p * ∑ i ∈ range N, (kc (Layout.key C S i) 0 * D i) * (2 ^ w : ℤ) ^ i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [hR]
    congr 1
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    by_cases hcK : i % S < K
    · rw [sum_eq_single (i % S)]
      · rw [if_pos rfl]; simp [kc, Layout.key]; ring
      · intro c _ hne; rw [if_neg (Ne.symm hne)]; ring
      · intro h; exact absurd (mem_range.mpr hcK) h
    · rw [sum_eq_zero fun c hc => by rw [if_neg (by have := mem_range.mp hc; omega)]; ring,
        hD0 i (by omega)]
      ring
  · -- rows
    have ha1 : a = 1 := by omega
    subst ha1
    have hrow : ∀ r ∈ range K, rowPart w S C l r Z =
        ∑ i ∈ range N, (if i / S = r ∧ i % S < K then D i else 0) * (2 ^ w) ^ i := by
      intro r hr
      have hr' := mem_range.mp hr
      refine hpart (fun i => i / S = r ∧ i % S < K) _ ?_
      have hite : ∀ i, (if i / S = r ∧ i % S < K then 2 ^ w - 1 else 0) * 2 ^ (w * i) =
          if i / S = r ∧ i % S < K then (2 ^ w - 1) * 2 ^ (w * i) else 0 := fun i => by
        split_ifs <;> simp
      rw [rowMask, natPack_range, sum_congr rfl (fun i _ => hite i),
        sum_row (C := C) (S := S) (r := r) hKS (by omega) (fun i => (2 ^ w - 1) * 2 ^ (w * i)),
        ← geom_sub_one w K, sum_mul]
      refine sum_congr rfl fun c _ => ?_
      rw [mul_assoc, ← pow_add]
      congr 2
      ring
    rw [sum_map_range_g (fun r => ((r : ℤ) - C) * rowPart w S C l r Z) K,
      sum_congr rfl (fun r hr => by rw [hrow r hr])]
    have hR : ∑ i ∈ range N, (psgn p * kc (Layout.key C S i) 1 * D i) * (2 ^ w : ℤ) ^ i =
        psgn p * ∑ i ∈ range N, (kc (Layout.key C S i) 1 * D i) * (2 ^ w : ℤ) ^ i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    rw [hR]
    congr 1
    simp_rw [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    have hrowK : i / S < K := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have h1 : i < 2 * C * S + 2 * C + 1 := hi'
      have h2 : 2 * C * S + 2 * C + 1 ≤ K * S := by rw [hK]; nlinarith
      omega
    by_cases hcK : i % S < K
    · rw [sum_eq_single (i / S)]
      · rw [if_pos ⟨rfl, hcK⟩]; simp only [kc, Layout.key]; simp; ring
      · intro r _ hne; rw [if_neg (fun h => hne h.1.symm)]; ring
      · intro h; exact absurd (mem_range.mpr hrowK) h
    · rw [sum_eq_zero fun r hr => by rw [if_neg (fun h => hcK h.2)]; ring, hD0 i (by omega)]
      ring

end KAM.EffectiveStability.Tube

end
