/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Witness.Binomial
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Data.Fintype.BigOperators

/-!
# Binomial remainders of products of powers (T2-CONF, N4)

For a finite set of modes `ι` (in practice `Fin 3`), exponents `s : ι → ℝ` (half-integers `n_j/2`),
base points `B : ι → ℝ` and deviations `u : ι → ℝ`, the product `Π_j (B_j + u_j)^{s_j}` is truncated
at total degree `≤ L` in `u`:

  `binomTrunc s L B u = Σ_{|m| ≤ L} Π_j binom(s_j, m_j) B_j^{s_j - m_j} u_j^{m_j}`.

**Bookkeeping.** Each factor is split into `L + 2` slots (`binomSlot`): the Taylor terms `m ≤ L` and
the one-variable remainder `binomRem s_j (L+1)` as slot `L + 1`. Expanding the product over slot
tuples `p ∈ {0, …, L+1}^ι`, the truncation is the sum over the tuples of `truncSet ι L` (all slots
Taylor terms, total degree `≤ L`); the remainder is the sum over the complement `tailSet ι L`:

  `binomProdRem s L B u = Σ_{p ∈ tailSet} Π_j binomSlot s_j L B_j u_j (p_j)` (`binomProdRem_eq`).

Bounding every slot by a majorant `G j m` gives `|binomProdRem| ≤ tailSum G L` with

  `tailSum G L = Σ_{p ∈ tailSet} Π_j G j (p j)`
  `            = Π_j (Σ_{m ≤ L+1} G j m) - Σ_{p ∈ truncSet} Π_j G j (p j)` (`tailSum_eq`).

The canonical majorant on the box `B_j ∈ [b_min_j, b_max_j]`, `|u_j| ≤ r < b_min_j` is `slotMaj`
(one-variable bounds of `Witness/Binomial.lean`); `tailSum` is monotone in the majorants
(`tailSum_mono`), so the checker may replace them by rational upper bounds.

**Derivatives.** Only factor `i` depends on `u_i` and `B_i`, so the derivatives are again slot sums
with the `i`-th slot family replaced (`Function.update`):
* `∂_{u_i}`: slot derivatives `binomSlotDu`, majorant `slotMajDu`;
* `∂_{B_i}`: slot derivatives `s_i · binomSlot (s_i - 1)`, majorant `|s_i| · slotMaj (s_i - 1)`;
* for `B = B(φ)` on the angle plane, the chain rule gives
  `|∂_{φ_a} binomProdRem| ≤ Σ_i β_i · tailSum (update G i (|s_i| · slotMaj (s_i - 1))) L`
  when `|∂_a B_i| ≤ β_i`.

Main results: `abs_binomProdRem_le_box`, `abs_fderiv_binomProdRem_u_le_box`,
`abs_fderiv_binomProdRem_phi_le_box`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset

/-! ### One-variable slots -/

/-- Slot `m` of the one-variable expansion of `(B + u)^s` at truncation degree `L`: the Taylor term
`binom(s, m) B^{s-m} u^m` for `m ≤ L`, and the remainder `binomRem s (L+1) B u` otherwise. -/
noncomputable def binomSlot (s : ℝ) (L : ℕ) (B u : ℝ) (m : ℕ) : ℝ :=
  if m ≤ L then gbinom s m * B ^ (s - m) * u ^ m else binomRem s (L + 1) B u

theorem sum_binomSlot (s : ℝ) (L : ℕ) (B u : ℝ) :
    ∑ m ∈ range (L + 2), binomSlot s L B u m = (B + u) ^ s := by
  rw [sum_range_succ]
  have h1 : ∑ m ∈ range (L + 1), binomSlot s L B u m = binomTaylor s (L + 1) B u := by
    refine sum_congr rfl fun m hm => ?_
    rw [binomSlot, ite_eq_left (Nat.lt_succ_iff.mp (mem_range.mp hm))]
  rw [h1, binomSlot, ite_eq_right (by omega), binomRem]
  ring

/-- The canonical majorant of `|binomSlot s L B u m|` on the box `B ∈ [b_min, b_max]`, `|u| ≤ r`. -/
noncomputable def slotMaj (s : ℝ) (L : ℕ) (bmin bmax r : ℝ) (m : ℕ) : ℝ :=
  if m ≤ L then |gbinom s m| * max (bmin ^ (s - m)) (bmax ^ (s - m)) * r ^ m
  else |gbinom s (L + 1)| * max ((bmin - r) ^ (s - ((L + 1 : ℕ) : ℝ)))
    ((bmax + r) ^ (s - ((L + 1 : ℕ) : ℝ))) * r ^ (L + 1)

theorem abs_binomSlot_le {s : ℝ} {L : ℕ} {bmin bmax B r u : ℝ} (m : ℕ) (h1 : bmin ≤ B)
    (h2 : B ≤ bmax) (hr : r < bmin) (hu : |u| ≤ r) :
    |binomSlot s L B u m| ≤ slotMaj s L bmin bmax r m := by
  have h0 : 0 < bmin := lt_of_le_of_lt ((abs_nonneg u).trans hu) hr
  unfold binomSlot slotMaj
  split_ifs
  · exact abs_binomTerm_le_box m s h0 h1 h2 hu
  · exact abs_binomRem_le_box (L + 1) s h1 h2 hr hu

theorem slotMaj_nonneg {s : ℝ} {L : ℕ} {bmin bmax r : ℝ} (hr0 : 0 ≤ r) (hr : r < bmin)
    (m : ℕ) : 0 ≤ slotMaj s L bmin bmax r m := by
  unfold slotMaj
  split_ifs
  · exact mul_nonneg (mul_nonneg (abs_nonneg _)
      ((Real.rpow_nonneg (hr0.trans hr.le) _).trans (le_max_left _ _))) (pow_nonneg hr0 _)
  · exact mul_nonneg (mul_nonneg (abs_nonneg _)
      ((Real.rpow_nonneg (by linarith) _).trans (le_max_left _ _))) (pow_nonneg hr0 _)

/-- The `u`-derivative of slot `m`. -/
noncomputable def binomSlotDu (s : ℝ) (L : ℕ) (B u : ℝ) (m : ℕ) : ℝ :=
  if m ≤ L then gbinom s m * B ^ (s - m) * ((m : ℝ) * u ^ (m - 1))
  else s * binomRem (s - 1) L B u

theorem hasDerivAt_binomSlot_u (s : ℝ) (L : ℕ) {B u : ℝ} (hBu : 0 < B + u) (m : ℕ) :
    HasDerivAt (fun u => binomSlot s L B u m) (binomSlotDu s L B u m) u := by
  by_cases h : m ≤ L
  · simp only [binomSlot, binomSlotDu, ite_eq_left h]
    exact (hasDerivAt_pow m u).const_mul _
  · simp only [binomSlot, binomSlotDu, ite_eq_right h]
    exact hasDerivAt_binomRem_u s L hBu

/-- The canonical majorant of `|binomSlotDu s L B u m|` on the box. -/
noncomputable def slotMajDu (s : ℝ) (L : ℕ) (bmin bmax r : ℝ) (m : ℕ) : ℝ :=
  if m ≤ L then (m : ℝ) * |gbinom s m| * max (bmin ^ (s - m)) (bmax ^ (s - m)) * r ^ (m - 1)
  else |s| * (|gbinom (s - 1) L| * max ((bmin - r) ^ (s - 1 - L)) ((bmax + r) ^ (s - 1 - L)) *
    r ^ L)

theorem abs_binomSlotDu_le {s : ℝ} {L : ℕ} {bmin bmax B r u : ℝ} (m : ℕ) (h1 : bmin ≤ B)
    (h2 : B ≤ bmax) (hr : r < bmin) (hu : |u| ≤ r) :
    |binomSlotDu s L B u m| ≤ slotMajDu s L bmin bmax r m := by
  have h0 : 0 < bmin := lt_of_le_of_lt ((abs_nonneg u).trans hu) hr
  unfold binomSlotDu slotMajDu
  split_ifs
  · rw [abs_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
      abs_of_nonneg (Real.rpow_nonneg (h0.le.trans h1) _)]
    have hp := pow_le_pow_left₀ (abs_nonneg u) hu (m - 1)
    have hq := mul_le_mul_of_nonneg_left (rpow_le_max_endpoints (s - m) h0 h1 h2)
      (abs_nonneg (gbinom s m))
    have hr0 : 0 ≤ r := (abs_nonneg u).trans hu
    have hA : 0 ≤ |gbinom s m| * B ^ (s - m) :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (h0.le.trans h1) _)
    calc |gbinom s m| * B ^ (s - ↑m) * (↑m * |u| ^ (m - 1))
        = (m : ℝ) * (|gbinom s m| * B ^ (s - ↑m)) * |u| ^ (m - 1) := by ring
      _ ≤ (m : ℝ) * (|gbinom s m| * max (bmin ^ (s - m)) (bmax ^ (s - m))) * r ^ (m - 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg m)) hp (by positivity)
          (mul_nonneg (Nat.cast_nonneg m) (hA.trans hq))
      _ = _ := by ring
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_binomRem_le_box L (s - 1) h1 h2 hr hu) (abs_nonneg s)

theorem slotMajDu_nonneg {s : ℝ} {L : ℕ} {bmin bmax r : ℝ} (hr0 : 0 ≤ r) (hr : r < bmin)
    (m : ℕ) : 0 ≤ slotMajDu s L bmin bmax r m := by
  unfold slotMajDu
  split_ifs
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg m) (abs_nonneg _))
      ((Real.rpow_nonneg (hr0.trans hr.le) _).trans (le_max_left _ _))) (pow_nonneg hr0 _)
  · exact mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (abs_nonneg _)
      ((Real.rpow_nonneg (by linarith) _).trans (le_max_left _ _))) (pow_nonneg hr0 _))

/-- The `B`-derivative of slot `m` is `s · binomSlot (s - 1) L B u m`. -/
theorem hasDerivAt_binomSlot_B (s : ℝ) (L : ℕ) {B u : ℝ} (hB : 0 < B) (hBu : 0 < B + u)
    (m : ℕ) : HasDerivAt (fun B => binomSlot s L B u m) (s * binomSlot (s - 1) L B u m) B := by
  by_cases h : m ≤ L
  · simp only [binomSlot, ite_eq_left h]
    refine (((Real.hasDerivAt_rpow_const (p := s - m) (Or.inl hB.ne')).const_mul
      (gbinom s m)).mul_const (u ^ m)).congr_deriv ?_
    have he : s - (m : ℝ) - 1 = s - 1 - m := by ring
    rw [he]
    have := gbinom_mul_sub s m
    linear_combination (B ^ (s - 1 - m) * u ^ m) * this
  · simp only [binomSlot, ite_eq_right h]
    exact hasDerivAt_binomRem_B s (L + 1) hB hBu

/-! ### Index sets and the slot expansion -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The kept monomials: exponent tuples `m` with total degree `Σ_j m_j ≤ L`. -/
def truncSet (ι : Type*) [Fintype ι] [DecidableEq ι] (L : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι => range (L + 1)).filter fun m => ∑ j, m j ≤ L

/-- The slot tuples of the remainder: all tuples in `{0, …, L+1}^ι` except the kept monomials. -/
def tailSet (ι : Type*) [Fintype ι] [DecidableEq ι] (L : ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun _ : ι => range (L + 2)) \ truncSet ι L

theorem truncSet_subset (L : ℕ) :
    truncSet ι L ⊆ Fintype.piFinset fun _ : ι => range (L + 2) := by
  intro m hm
  simp only [truncSet, mem_filter, Fintype.mem_piFinset, mem_range] at hm ⊢
  exact fun j => (hm.1 j).trans (by omega)

theorem le_of_mem_truncSet {L : ℕ} {m : ι → ℕ} (hm : m ∈ truncSet ι L) (j : ι) : m j ≤ L := by
  simp only [truncSet, mem_filter, Fintype.mem_piFinset, mem_range] at hm
  exact Nat.lt_succ_iff.mp (hm.1 j)

theorem lt_of_mem_tailSet {L : ℕ} {p : ι → ℕ} (hp : p ∈ tailSet ι L) (j : ι) : p j < L + 2 := by
  simp only [tailSet, mem_sdiff, Fintype.mem_piFinset, mem_range] at hp
  exact hp.1 j

/-- The product of powers `Π_j (B_j + u_j)^{s_j}`. -/
noncomputable def binomProd (s B u : ι → ℝ) : ℝ := ∏ j, (B j + u j) ^ s j

/-- The truncation at total degree `≤ L`:
`Σ_{|m| ≤ L} Π_j binom(s_j, m_j) B_j^{s_j - m_j} u_j^{m_j}`. -/
noncomputable def binomTrunc (s : ι → ℝ) (L : ℕ) (B u : ι → ℝ) : ℝ :=
  ∑ m ∈ truncSet ι L, ∏ j, gbinom (s j) (m j) * B j ^ (s j - m j) * u j ^ (m j)

/-- The truncation remainder `Π_j (B_j + u_j)^{s_j} - binomTrunc s L B u`. -/
noncomputable def binomProdRem (s : ι → ℝ) (L : ℕ) (B u : ι → ℝ) : ℝ :=
  binomProd s B u - binomTrunc s L B u

/-- The slot sum over the tail tuples. -/
noncomputable def tailSum (G : ι → ℕ → ℝ) (L : ℕ) : ℝ := ∑ p ∈ tailSet ι L, ∏ j, G j (p j)

/-- The slot expansion of a product of slot sums. -/
theorem prod_sum_slots_sub (g : ι → ℕ → ℝ) (L : ℕ) :
    ∏ j, ∑ m ∈ range (L + 2), g j m - ∑ p ∈ truncSet ι L, ∏ j, g j (p j) =
      ∑ p ∈ tailSet ι L, ∏ j, g j (p j) := by
  rw [prod_univ_sum, ← sum_sdiff (truncSet_subset (ι := ι) L), tailSet]
  ring

/-- Closed form of `tailSum` (for evaluation). -/
theorem tailSum_eq (G : ι → ℕ → ℝ) (L : ℕ) :
    tailSum G L = ∏ j, ∑ m ∈ range (L + 2), G j m - ∑ p ∈ truncSet ι L, ∏ j, G j (p j) :=
  (prod_sum_slots_sub G L).symm

/-- `tailSum` is monotone in nonnegative majorants. -/
theorem tailSum_mono {G G' : ι → ℕ → ℝ} {L : ℕ} (h0 : ∀ j m, m < L + 2 → 0 ≤ G j m)
    (h : ∀ j m, m < L + 2 → G j m ≤ G' j m) : tailSum G L ≤ tailSum G' L :=
  sum_le_sum fun _ hp => prod_le_prod₀ (fun j _ => h0 j _ (lt_of_mem_tailSet hp j))
    fun j _ => h j _ (lt_of_mem_tailSet hp j)

theorem tailSum_nonneg {G : ι → ℕ → ℝ} {L : ℕ} (h0 : ∀ j m, m < L + 2 → 0 ≤ G j m) :
    0 ≤ tailSum G L :=
  sum_nonneg fun _ hp => prod_nonneg fun j _ => h0 j _ (lt_of_mem_tailSet hp j)

/-- **The slot expansion of the remainder.** -/
theorem binomProdRem_eq (s : ι → ℝ) (L : ℕ) (B u : ι → ℝ) :
    binomProdRem s L B u =
      ∑ p ∈ tailSet ι L, ∏ j, binomSlot (s j) L (B j) (u j) (p j) := by
  rw [← prod_sum_slots_sub, binomProdRem, binomProd, binomTrunc]
  simp only [sum_binomSlot]
  congr 1
  refine sum_congr rfl fun m hm => prod_congr rfl fun j _ => ?_
  rw [binomSlot, ite_eq_left (le_of_mem_truncSet hm j)]

/-- A bound of a slot sum by majorants. -/
theorem abs_tail_le {g G : ι → ℕ → ℝ} {L : ℕ} (h : ∀ j m, m < L + 2 → |g j m| ≤ G j m) :
    |∑ p ∈ tailSet ι L, ∏ j, g j (p j)| ≤ tailSum G L := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
  rw [abs_prod]
  exact prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => h j _ (lt_of_mem_tailSet hp j)

/-- The product over a slot tuple with the `i`-th family replaced. -/
theorem prod_update_slot (G : ι → ℕ → ℝ) (i : ι) (Gi : ℕ → ℝ) (p : ι → ℕ) :
    ∏ j, Function.update G i Gi j (p j) = Gi (p i) * ∏ j ∈ univ.erase i, G j (p j) := by
  rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hj)]

/-! ### Main bounds on the box -/

/-- The canonical slot majorants of the box `B_j ∈ [b_min_j, b_max_j]`, `|u_j| ≤ r`. -/
noncomputable def boxMaj (s : ι → ℝ) (L : ℕ) (bmin bmax : ι → ℝ) (r : ℝ) : ι → ℕ → ℝ :=
  fun j => slotMaj (s j) L (bmin j) (bmax j) r

/-- **Value bound.** On the box,
`|Π_j (B_j + u_j)^{s_j} - binomTrunc s L B u| ≤ tailSum (boxMaj …) L`. -/
theorem abs_binomProdRem_le_box (s : ι → ℝ) (L : ℕ) {bmin bmax B u : ι → ℝ} {r : ℝ}
    (hr : ∀ j, r < bmin j) (h1 : ∀ j, bmin j ≤ B j) (h2 : ∀ j, B j ≤ bmax j)
    (hu : ∀ j, |u j| ≤ r) : |binomProdRem s L B u| ≤ tailSum (boxMaj s L bmin bmax r) L := by
  rw [binomProdRem_eq]
  exact abs_tail_le fun j m _ => abs_binomSlot_le m (h1 j) (h2 j) (hr j) (hu j)

end KAM.EffectiveStability.Tube

end
