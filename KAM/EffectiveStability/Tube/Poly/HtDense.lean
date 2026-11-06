/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Exact
public import KAM.EffectiveStability.Tube.Poly.Dense

/-!
# Cosine series from mode lists in N7's dense box order (T2-CONF, N5a-2)

N7's exact inputs are dense rational lists in box order (`denseCos C cs`, index `c + (2C+1) r` for
the mode `(c - C, r - C)`). This file builds such lists from mode lists and evaluates them:
* `pDense C ts`: slot `i` is the sum of the values of the terms with box index `i`;
  `denseCos_pDense`: for terms in the box, `denseCos C (pDense C ts) = Σ v cos(k·φ)`.
* `scatter L i ps`: the dense list of index-sorted pairs in linear time (for long mode lists);
  `denseCos_scatter`: for strictly increasing indices below `(2C+1)²`,
  `denseCos C (scatter (2C+1)² 0 ps) = Σ v cos(boxKey C j · φ)`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Finset

/-- The box index `c + (2C+1) r` of the mode `(c - C, r - C)`. -/
def boxIdx (C : ℕ) (k : ℤ × ℤ) : ℕ := (k.1 + C).toNat + (2 * C + 1) * (k.2 + C).toNat

/-- The mode lies in the box `|k₁|, |k₂| ≤ C`. -/
def inBox (C : ℕ) (k : ℤ × ℤ) : Bool := decide (|k.1| ≤ C) && decide (|k.2| ≤ C)

theorem boxIdx_lt {C : ℕ} {k : ℤ × ℤ} (h : inBox C k = true) :
    boxIdx C k < (2 * C + 1) * (2 * C + 1) := by
  simp only [inBox, Bool.and_eq_true, decide_eq_true_eq, abs_le] at h
  simp only [boxIdx]
  have h1 : (k.1 + C).toNat ≤ 2 * C := by omega
  have h2 : (k.2 + C).toNat ≤ 2 * C := by omega
  nlinarith

theorem boxKey_boxIdx {C : ℕ} {k : ℤ × ℤ} (h : inBox C k = true) : boxKey C (boxIdx C k) = k := by
  simp only [inBox, Bool.and_eq_true, decide_eq_true_eq, abs_le] at h
  have h1 : (k.1 + C).toNat < 2 * C + 1 := by omega
  simp only [boxKey, boxIdx]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt h1, zero_add]
  ext <;> simp <;> omega

theorem denseCos_eq_sum (C : ℕ) (cs : List ℚ) (φ : Fin 2 → ℝ) :
    denseCos C cs φ = ∑ i ∈ range ((2 * C + 1) * (2 * C + 1)),
      ((cs.getD i 0 : ℚ) : ℝ) * Real.cos (kdot (boxKey C i) φ) := by
  simp [denseCos, evalR, trig]

/-- The dense list of a list of terms `(k, v)`: slot `i` sums the values with box index `i`. -/
def pDense (C : ℕ) (ts : List ((ℤ × ℤ) × ℚ)) : List ℚ :=
  (List.range ((2 * C + 1) * (2 * C + 1))).map fun i =>
    ((ts.filter fun t => boxIdx C t.1 == i).map (·.2)).sum

/-- **The cosine series of a term list in the box.** -/
theorem denseCos_pDense (C : ℕ) (ts : List ((ℤ × ℤ) × ℚ)) (hts : ∀ t ∈ ts, inBox C t.1 = true)
    (φ : Fin 2 → ℝ) :
    denseCos C (pDense C ts) φ = (ts.map fun t => (t.2 : ℝ) * Real.cos (kdot t.1 φ)).sum := by
  rw [denseCos_eq_sum, list_sum_eq_sum_filter (fun t => boxIdx C t.1) _
    (range ((2 * C + 1) * (2 * C + 1))) ts (fun t ht => mem_range.2 (boxIdx_lt (hts t ht)))]
  refine sum_congr rfl fun i hi => ?_
  rw [pDense, List.getD_eq_getElem _ _ (by simpa using mem_range.1 hi), List.getElem_map,
    List.getElem_range, Rat.cast_list_sum, List.map_map, ← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  have hti : boxIdx C t.1 = i := by simpa using (List.mem_filter.1 ht).2
  have htb := hts t (List.mem_filter.1 ht).1
  simp only [Function.comp_apply, ← hti, boxKey_boxIdx htb]

/-! ### Scatter of sorted pairs -/

/-- The dense list of length `L` from index `i` on, with the values of the index-sorted pairs. -/
def scatter : ℕ → ℕ → List (ℕ × ℚ) → List ℚ
  | 0, _, _ => []
  | L + 1, i, [] => 0 :: scatter L (i + 1) []
  | L + 1, i, p :: ps =>
    if p.1 = i then p.2 :: scatter L (i + 1) ps else 0 :: scatter L (i + 1) (p :: ps)

/-- The pairs have strictly increasing indices, all at least `i`. -/
def incFrom : ℕ → List (ℕ × ℚ) → Bool
  | _, [] => true
  | i, p :: ps => decide (i ≤ p.1) && incFrom (p.1 + 1) ps

theorem incFrom_mono {i j : ℕ} (hij : i ≤ j) : ∀ {ps : List (ℕ × ℚ)}, incFrom j ps = true →
    incFrom i ps = true
  | [], _ => rfl
  | p :: ps, h => by
    simp only [incFrom, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨le_trans hij h.1, h.2⟩

theorem incFrom_ge {i : ℕ} : ∀ {ps : List (ℕ × ℚ)}, incFrom i ps = true → ∀ p ∈ ps, i ≤ p.1
  | [], _ => by simp
  | q :: ps, h => by
    simp only [incFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact le_trans (by omega) (incFrom_ge h.2 p hp)

theorem sum_scatter (g : ℕ → ℝ) : ∀ (L i : ℕ) (ps : List (ℕ × ℚ)), incFrom i ps = true →
    (∀ p ∈ ps, p.1 < i + L) →
      ∑ t ∈ range L, (((scatter L i ps).getD t 0 : ℚ) : ℝ) * g (i + t) =
        (ps.map fun p => (p.2 : ℝ) * g p.1).sum
  | 0, i, ps, hinc, hlt => by
    cases ps with
    | nil => simp
    | cons p ps =>
      have h1 := incFrom_ge hinc p List.mem_cons_self
      have h2 := hlt p List.mem_cons_self
      omega
  | L + 1, i, [], _, _ => by
    rw [sum_range_succ', scatter]
    have := sum_scatter g L (i + 1) [] rfl (by simp)
    simp only [List.getD_cons_succ, List.getD_cons_zero] at this ⊢
    rw [show (∑ t ∈ range L, (((scatter L (i + 1) []).getD t 0 : ℚ) : ℝ) * g (i + (t + 1))) =
      ∑ t ∈ range L, (((scatter L (i + 1) []).getD t 0 : ℚ) : ℝ) * g (i + 1 + t) from
      sum_congr rfl fun t _ => by rw [add_assoc, add_comm t 1]]
    rw [this]; simp
  | L + 1, i, p :: ps, hinc, hlt => by
    simp only [incFrom, Bool.and_eq_true, decide_eq_true_eq] at hinc
    rw [sum_range_succ', scatter]
    have hshift : ∀ (l : List ℚ), (∑ t ∈ range L, ((l.getD t 0 : ℚ) : ℝ) * g (i + (t + 1))) =
        ∑ t ∈ range L, ((l.getD t 0 : ℚ) : ℝ) * g (i + 1 + t) :=
      fun l => sum_congr rfl fun t _ => by rw [add_assoc, add_comm t 1]
    split_ifs with hp
    · simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      rw [hshift, sum_scatter g L (i + 1) ps (by rw [← hp]; exact hinc.2)
        (fun q hq => by have := hlt q (List.mem_cons_of_mem p hq); omega)]
      simp [hp, add_comm]
    · simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      rw [hshift, sum_scatter g L (i + 1) (p :: ps)
        (by simp only [incFrom, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega, hinc.2⟩)
        (fun q hq => by have := hlt q hq; omega)]
      simp

/-- **The cosine series of sorted pairs.** -/
theorem denseCos_scatter (C : ℕ) (ps : List (ℕ × ℚ)) (hinc : incFrom 0 ps = true)
    (hlt : ∀ p ∈ ps, p.1 < (2 * C + 1) * (2 * C + 1)) (φ : Fin 2 → ℝ) :
    denseCos C (scatter ((2 * C + 1) * (2 * C + 1)) 0 ps) φ =
      (ps.map fun p => (p.2 : ℝ) * Real.cos (kdot (boxKey C p.1) φ)).sum := by
  rw [denseCos_eq_sum]
  have := sum_scatter (fun j => Real.cos (kdot (boxKey C j) φ)) ((2 * C + 1) * (2 * C + 1)) 0 ps
    hinc (fun p hp => by simpa using hlt p hp)
  simpa using this

/-! ### Checks in blocks -/

/-- A Boolean property of every element follows from the same property on the blocks
`(l.drop (c k)).take c`, `k < K`, when `l` has at most `c K` elements (so that a kernel check can be
split into declarations of `c` elements each). -/
theorem all_of_blocks {α : Type*} (p : α → Bool) (l : List α) {c K : ℕ} (hc : 0 < c)
    (hK : l.length ≤ c * K) (h : ∀ k < K, ((l.drop (c * k)).take c).all p = true) :
    ∀ x ∈ l, p x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  have hk : i / c < K := by
    rw [Nat.div_lt_iff_lt_mul hc]; rw [mul_comm] at hK; omega
  have hmem : l[i] ∈ (l.drop (c * (i / c))).take c := by
    rw [List.mem_iff_getElem]
    have h1 : c * (i / c) ≤ i := Nat.mul_div_le i c
    have h2 : i - c * (i / c) < c := by
      have h3 := Nat.div_add_mod i c
      have h4 := Nat.mod_lt i hc
      omega
    refine ⟨i - c * (i / c), ?_, ?_⟩
    · simp only [List.length_take, List.length_drop]; omega
    · simp only [List.getElem_take, List.getElem_drop]
      congr 1; omega
  exact List.all_eq_true.1 (h _ hk) _ hmem

end KAM.EffectiveStability.Tube

end
