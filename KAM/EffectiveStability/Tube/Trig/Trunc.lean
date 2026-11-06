/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Trig.Product
public import KAM.CertificateSharp.Packed.Round

/-!
# Truncation and rounding of trigonometric polynomials (T2-CONF, N3)

All square layouts of one computation share the row stride `S`. The layout of half-width `C'` then
sits inside the layout of half-width `C ≥ C'` as a contiguous slice: slot `i'` of the small layout
is slot `(C - C') (S + 1) + i'` of the large one (`Layout.key_shift`, when `C + C' < S`). So
truncating a product to a smaller box and rounding it to a coarser scale is one linear pass
(`truncRound`), and comparing the result with the product is a slotwise difference.

Main results:
* `evalK_embed`: a polynomial on the small layout, padded in front by zeros, has the same value on
  the large layout;
* `c1Close_sub`: **the general comparison** of `c` on the large layout with `m · t` on the small
  one: `C1Close` with errors `l1 (lsub c (embed (m t)))` and the weighted norms of the same
  difference (both computable, linear in the length);
* `truncRound` (hexagon mask `keepHex K`, sign-symmetric round-to-nearest `rndS`) and
  `c1Close_truncRound`, its `C1Close` statement with the exact computed errors;
* `abs_sub_rndS_le`: half an ulp per kept slot; `truncRound_err_le`: the a-priori slot bound
  (kept: `2^(s-1)`, dropped: `|c_i|`), summed in `l1_truncRound_le` and weighted in
  `wl1_truncRound_le`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-! ### The hexagon -/

/-- The hexagonal norm `|k₁| + |k₂| + |k₁ + k₂|`. -/
def hexN (k : ℤ × ℤ) : ℕ := k.1.natAbs + k.2.natAbs + (k.1 + k.2).natAbs

/-- The hexagon `hexN k ≤ K` as a mask. -/
def keepHex (K : ℕ) (k : ℤ × ℤ) : Bool := decide (hexN k ≤ K)

theorem hexN_neg (k : ℤ × ℤ) : hexN (-k) = hexN k := by
  simp only [hexN, Prod.fst_neg, Prod.snd_neg, Int.natAbs_neg]
  rw [show -k.1 + -k.2 = -(k.1 + k.2) by ring, Int.natAbs_neg]

/-- The hexagon of order `K` lies in the square box of half-width `K / 2`. -/
theorem natAbs_le_of_hexN_le {k : ℤ × ℤ} {K : ℕ} (h : hexN k ≤ K) :
    k.1.natAbs ≤ K / 2 ∧ k.2.natAbs ≤ K / 2 := by
  unfold hexN at h
  omega

/-! ### Sub-layouts -/

/-- The slot offset of the layout of half-width `C'` inside the one of half-width `C`. -/
def Layout.shift (C C' S : ℕ) : ℕ := (C - C') * (S + 1)

theorem Layout.key_shift {C C' S i : ℕ} (hC : C' ≤ C) (hS : C + C' < S) (hi : i % S ≤ 2 * C') :
    Layout.key C S (Layout.shift C C' S + i) = Layout.key C' S i := by
  have hS0 : 0 < S := by omega
  have hsplit : Layout.shift C C' S + i = ((C - C') + i % S) + S * ((C - C') + i / S) := by
    have := Nat.mod_add_div i S
    unfold Layout.shift
    conv_lhs => rw [← this]
    ring
  have hm : (Layout.shift C C' S + i) % S = (C - C') + i % S := by
    rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hd : (Layout.shift C C' S + i) / S = (C - C') + i / S := by
    rw [hsplit, Nat.add_mul_div_left _ _ hS0, Nat.div_eq_of_lt (by omega), zero_add]
  refine Prod.ext ?_ ?_
  · simp only [Layout.key, hm]; omega
  · simp only [Layout.key, hd]; omega

/-- Pad a small-layout list in front by zeros: the same polynomial on the large layout. -/
def embed (C C' S : ℕ) (d : List ℤ) : List ℤ := List.replicate (Layout.shift C C' S) 0 ++ d

theorem getD_replicate_append (n : ℕ) (d : List ℤ) (i : ℕ) :
    (List.replicate n 0 ++ d).getD i 0 = if i < n then 0 else d.getD (i - n) 0 := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih]
      by_cases h : i < n
      · simp [h]
      · simp [h, show ¬ i + 1 < n + 1 by omega]

theorem evalK_embed {C C' S : ℕ} (hC : C' ≤ C) (hS : C + C' < S) {d : List ℤ}
    (hd : colsOk C' S d = true) (p : Bool) (φ : Fin 2 → ℝ) :
    evalK (Layout.key C S) p (embed C C' S d) φ = evalK (Layout.key C' S) p d φ := by
  rw [evalK, embed, List.length_append, List.length_replicate, sum_range_add]
  rw [sum_eq_zero fun i hi => by
    rw [getD_replicate_append, if_pos (mem_range.mp hi)]; simp, zero_add, evalK]
  refine sum_congr rfl fun i _ => ?_
  rw [getD_replicate_append, if_neg (by omega), Nat.add_sub_cancel_left]
  by_cases h0 : d.getD i 0 = 0
  · rw [h0]; simp
  · rw [Layout.key_shift hC hS (colsOk_spec hd i h0)]

theorem evalK_map_mul (κ : ℕ → ℤ × ℤ) (p : Bool) (m : ℤ) (d : List ℤ) (φ : Fin 2 → ℝ) :
    evalK κ p (d.map (m * ·)) φ = (m : ℝ) * evalK κ p d φ := by
  rw [evalK, evalK, List.length_map, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases d[i]? <;> simp [mul_assoc]

theorem colsOk_map_mul {C S : ℕ} {d : List ℤ} (hd : colsOk C S d = true) (m : ℤ) :
    colsOk C S (d.map (m * ·)) = true := by
  have key : ∀ (i₀ : ℕ) (l : List ℤ), colsOkAux C S i₀ l = true →
      colsOkAux C S i₀ (l.map (m * ·)) = true := by
    intro i₀ l
    induction l generalizing i₀ with
    | nil => simp [colsOkAux]
    | cons c l ih =>
      intro h
      simp only [colsOkAux, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq, List.map_cons] at h ⊢
      refine ⟨?_, ih _ h.2⟩
      rcases h.1 with h0 | h0
      · left; simp [h0]
      · right; exact h0
  exact key 0 d hd

/-- **The general comparison.** A polynomial `c` on the large layout and `m · t` (`t` on the small
layout, zero padding) are `C¹`-close with the computable `ℓ¹` and weighted norms of the slotwise
difference `c - embed (m t)`. Truncation and rounding are special cases. -/
theorem c1Close_sub {C C' S : ℕ} (hC : C' ≤ C) (hS : C + C' < S) (p : Bool) (c t : List ℤ)
    (ht : colsOk C' S t = true) (m : ℤ) {e₁ : ℝ}
    (h₁ : ∀ a, (wl1 (Layout.key C S) a (lsub c (embed C C' S (t.map (m * ·)))) : ℝ) ≤ e₁) :
    C1Close (evalK (Layout.key C S) p c) (fun φ => (m : ℝ) * evalK (Layout.key C' S) p t φ)
      (l1 (lsub c (embed C C' S (t.map (m * ·))))) e₁ := by
  have h := c1Close_evalK (Layout.key C S) p c (embed C C' S (t.map (m * ·))) h₁
  have he : evalK (Layout.key C S) p (embed C C' S (t.map (m * ·))) =
      fun φ => (m : ℝ) * evalK (Layout.key C' S) p t φ := by
    funext φ
    rw [evalK_embed hC hS (colsOk_map_mul ht m), evalK_map_mul]
  rwa [he] at h

/-! ### Sign-symmetric rounding -/

/-- Round to the nearest multiple of `2^s`, ties away from zero (`rndS s (-d) = -rndS s d`):
the mantissa at the coarser scale. `rndS 0 = id`. -/
def rndS (s : ℕ) (d : ℤ) : ℤ :=
  if s = 0 then d else if d < 0 then -roundSlot s (-d) else roundSlot s d

/-- Half an ulp: `|d - 2^s rndS s d| ≤ 2^(s-1)` for `s ≥ 1`, and exact for `s = 0`. -/
theorem abs_sub_rndS_le (s : ℕ) (d : ℤ) :
    |d - 2 ^ s * rndS s d| ≤ (if s = 0 then 0 else 2 ^ (s - 1)) := by
  unfold rndS
  split_ifs with h0 hd
  · subst h0; simp
  · have := round_err (Nat.one_le_iff_ne_zero.mpr h0) (-d)
    rw [show d - 2 ^ s * -roundSlot s (-d) = -(-d - 2 ^ s * roundSlot s (-d)) by ring, abs_neg]
    exact this
  · exact round_err (Nat.one_le_iff_ne_zero.mpr h0) d

theorem rndS_neg (s : ℕ) (d : ℤ) (hd : d ≠ 0) : rndS s (-d) = -rndS s d := by
  unfold rndS
  by_cases h0 : s = 0
  · simp [h0]
  rcases lt_or_gt_of_ne hd with h | h
  · rw [if_neg h0, if_neg h0, if_neg (by omega), if_pos h, neg_neg]
  · rw [if_neg h0, if_neg h0, if_pos (by omega), if_neg (by omega), neg_neg]

theorem rndS_zero (s : ℕ) : rndS s 0 = 0 := by
  unfold rndS roundSlot
  split_ifs with h h'
  · rfl
  · exact (lt_irrefl 0 h').elim
  · rw [zero_add]
    exact Int.ediv_eq_zero_of_lt (by positivity)
      (pow_lt_pow_right₀ (by norm_num) (by omega))

/-- The half-ulp as an integer (`0` for `s = 0`). -/
def ulpHalf (s : ℕ) : ℤ := if s = 0 then 0 else 2 ^ (s - 1)

/-! ### Truncation and rounding in one pass -/

/-- Slot `i` of the small layout kept: its column is valid and its mode is in the mask. -/
def keptAt (C' S : ℕ) (keep : ℤ × ℤ → Bool) (i : ℕ) : Bool :=
  keep (Layout.key C' S i) && decide (i % S ≤ 2 * C')

/-- **Truncate and round**: the slice of the large-layout list `c` that is the small layout, kept
slots rounded by `s` bits (`rndS`), the others zero. Linear in the length. -/
def truncRound (C C' S s : ℕ) (keep : ℤ × ℤ → Bool) (c : List ℤ) : List ℤ :=
  mapIx (fun i x => if keptAt C' S keep i then rndS s x else 0) 0
    ((c.drop (Layout.shift C C' S)).take (Layout.len C' S))

theorem getD_truncRound (C C' S s : ℕ) (keep : ℤ × ℤ → Bool) (c : List ℤ) (i : ℕ) :
    (truncRound C C' S s keep c).getD i 0 =
      if i < Layout.len C' S ∧ keptAt C' S keep i = true then
        rndS s (c.getD (Layout.shift C C' S + i) 0) else 0 := by
  rw [truncRound, getD_mapIx _ (a₀ := 0) (b₀ := 0) (fun i => by simp [rndS_zero]) 0 _ i,
    zero_add]
  by_cases hi : i < Layout.len C' S
  · rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi, List.getElem?_drop,
      ← List.getD_eq_getElem?_getD]
    by_cases hk : keptAt C' S keep i = true
    · simp [hi, hk]
    · simp [hk]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_neg hi]
    simp [hi, rndS_zero]

theorem length_truncRound_le (C C' S s : ℕ) (keep : ℤ × ℤ → Bool) (c : List ℤ) :
    (truncRound C C' S s keep c).length ≤ Layout.len C' S := by
  rw [truncRound, length_mapIx, List.length_take]
  exact min_le_left _ _

theorem colsOk_truncRound (C C' S s : ℕ) (keep : ℤ × ℤ → Bool) (c : List ℤ) :
    colsOk C' S (truncRound C C' S s keep c) = true := by
  have key : ∀ (i₀ : ℕ) (l : List ℤ), colsOkAux C' S i₀
      (mapIx (fun i x => if keptAt C' S keep i then rndS s x else 0) i₀ l) = true := by
    intro i₀ l
    induction l generalizing i₀ with
    | nil => simp [mapIx, colsOkAux]
    | cons c l ih =>
      simp only [mapIx, colsOkAux, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      refine ⟨?_, ih _⟩
      by_cases hk : keptAt C' S keep i₀ = true
      · right
        simp only [keptAt, Bool.and_eq_true, decide_eq_true_eq] at hk
        exact hk.2
      · left; simp [hk]
  exact key 0 _

/-- **Truncation and rounding as a `C¹` statement**, with the exact computed errors: the
product `c` on the large layout is `C¹`-close to `2^s · truncRound … c` on the small one. -/
theorem c1Close_truncRound {C C' S : ℕ} (hC : C' ≤ C) (hS : C + C' < S) (p : Bool) (s : ℕ)
    (keep : ℤ × ℤ → Bool) (c : List ℤ) {e₁ : ℝ}
    (h₁ : ∀ a, (wl1 (Layout.key C S) a (lsub c (embed C C' S
      ((truncRound C C' S s keep c).map ((2 ^ s : ℤ) * ·)))) : ℝ) ≤ e₁) :
    C1Close (evalK (Layout.key C S) p c)
      (fun φ => ((2 ^ s : ℤ) : ℝ) * evalK (Layout.key C' S) p (truncRound C C' S s keep c) φ)
      (l1 (lsub c (embed C C' S ((truncRound C C' S s keep c).map ((2 ^ s : ℤ) * ·))))) e₁ :=
  c1Close_sub hC hS p c _ (colsOk_truncRound C C' S s keep c) _ h₁

/-! ### A-priori bounds -/

/-- The a-priori slot bound of `truncRound` at slot `i` of the large layout: half an ulp if the
slot is kept, `|c_i|` if it is dropped. -/
def trBound (C C' S s : ℕ) (keep : ℤ × ℤ → Bool) (i : ℕ) (x : ℤ) : ℤ :=
  if Layout.shift C C' S ≤ i ∧ i - Layout.shift C C' S < Layout.len C' S ∧
      keptAt C' S keep (i - Layout.shift C C' S) = true then ulpHalf s else |x|

theorem getD_map_mul (m : ℤ) (d : List ℤ) (i : ℕ) :
    (d.map (m * ·)).getD i 0 = m * d.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases d[i]? <;> simp

/-- **Slot error of truncation and rounding**: at every slot `i` of the large layout, the
difference is at most `trBound` (half an ulp where kept, `|c_i|` where dropped). -/
theorem truncRound_err_le (C C' S s : ℕ) (keep : ℤ × ℤ → Bool) (c : List ℤ) (i : ℕ) :
    |(lsub c (embed C C' S ((truncRound C C' S s keep c).map ((2 ^ s : ℤ) * ·)))).getD i 0| ≤
      trBound C C' S s keep i (c.getD i 0) := by
  rw [getD_lsub, embed, getD_replicate_append, trBound]
  have hu : ∀ x, |x - 2 ^ s * rndS s x| ≤ ulpHalf s := fun x => by
    have := abs_sub_rndS_le s x; unfold ulpHalf; exact this
  by_cases h1 : i < Layout.shift C C' S
  · rw [if_pos h1, if_neg (by omega)]; simp
  rw [if_neg h1, getD_map_mul, getD_truncRound]
  by_cases h2 : i - Layout.shift C C' S < Layout.len C' S ∧
      keptAt C' S keep (i - Layout.shift C C' S) = true
  · rw [if_pos h2, if_pos ⟨by omega, h2.1, h2.2⟩, Nat.add_sub_cancel' (by omega)]
    exact hu _
  · rw [if_neg h2, if_neg (by tauto)]
    simp

/-- The a-priori total: `Σ_i trBound_i` bounds the computed `ℓ¹` error. -/
theorem l1_truncRound_le (C C' S s : ℕ) (keep : ℤ × ℤ → Bool) (c : List ℤ) :
    l1 (lsub c (embed C C' S ((truncRound C C' S s keep c).map ((2 ^ s : ℤ) * ·)))) ≤
      ∑ i ∈ range (max c.length (embed C C' S ((truncRound C C' S s keep c).map
        ((2 ^ s : ℤ) * ·))).length), trBound C C' S s keep i (c.getD i 0) := by
  rw [l1_eq, length_lsub]
  exact sum_le_sum fun i _ => truncRound_err_le C C' S s keep c i

/-- The a-priori weighted total. -/
theorem wl1_truncRound_le (C C' S s : ℕ) (keep : ℤ × ℤ → Bool) (c : List ℤ) (a : Fin 2) :
    wl1 (Layout.key C S) a
        (lsub c (embed C C' S ((truncRound C C' S s keep c).map ((2 ^ s : ℤ) * ·)))) ≤
      ∑ i ∈ range (max c.length (embed C C' S ((truncRound C C' S s keep c).map
        ((2 ^ s : ℤ) * ·))).length),
        |kc (Layout.key C S i) a| * trBound C C' S s keep i (c.getD i 0) := by
  rw [wl1_eq, length_lsub]
  exact sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (truncRound_err_le C C' S s keep c i) (abs_nonneg _)

end KAM.EffectiveStability.Tube

end
