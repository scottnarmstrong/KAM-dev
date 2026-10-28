/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.DividedDifference

/-!
# Scalar sublevel estimate (blueprint `bpP:p11a:scalar-sublevel`)

If `f` is `C^q` on `[a,b]` and `β ≤ |f^{(q)}|` on `(a,b)`, then
`vol {t ∈ [a,b] | |f t| ≤ ε} ≤ 2q (ε/β)^{1/q}` (`KAM.Planetary.scalar_sublevel`).

Steps: the distribution function `φ(t) = vol (E ∩ (-∞,t])` of the compact sublevel set `E` is
`1`-Lipschitz (`stepP:p11a:ss-phi`, `p11Phi_dist_le`); there are nodes `tᵢ ∈ E` with
`φ(tᵢ) = i L / q` (`stepP:p11a:ss-nodes`, `p11_exists_node`), whose gaps satisfy
`t_j - tᵢ ≥ (j-i) L / q`, giving `∏_{j≠i} |tᵢ - t_j| ≥ i! (q-i)! (L/q)^q`
(`stepP:p11a:ss-gaps`, `p11_gap_prod`); finally the divided difference of `f` at the nodes is
bounded above by the gaps and below by `β/q!` (`stepP:p11a:ss-dd`).
-/

@[expose] public noncomputable section

open Set MeasureTheory

namespace KAM.Planetary

/-- Distribution function `t ↦ vol (E ∩ (-∞, t])`. -/
def p11Phi (E : Set ℝ) (t : ℝ) : ℝ := (volume (E ∩ Iic t)).toReal

theorem p11Phi_add {E : Set ℝ} (hE : IsCompact E) {s t : ℝ} (h : s ≤ t) :
    p11Phi E t = p11Phi E s + (volume (E ∩ Ioc s t)).toReal := by
  unfold p11Phi
  have hsplit : E ∩ Iic t = E ∩ Iic s ∪ E ∩ Ioc s t := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
    constructor
    · rintro ⟨hx, hxt⟩
      by_cases hxs : x ≤ s
      · exact Or.inl ⟨hx, hxs⟩
      · exact Or.inr ⟨hx, not_le.1 hxs, hxt⟩
    · rintro (⟨hx, hxs⟩ | ⟨hx, _, hxt⟩)
      · exact ⟨hx, hxs.trans h⟩
      · exact ⟨hx, hxt⟩
  have hdisj : Disjoint (E ∩ Iic s) (E ∩ Ioc s t) := by
    refine Set.disjoint_left.2 ?_
    rintro x ⟨_, hxs⟩ ⟨_, hxs', _⟩
    exact absurd hxs (not_le.2 hxs')
  have hfin1 : volume (E ∩ Iic s) ≠ ⊤ :=
    ne_top_of_le_ne_top hE.measure_lt_top.ne (measure_mono inter_subset_left)
  have hfin2 : volume (E ∩ Ioc s t) ≠ ⊤ :=
    ne_top_of_le_ne_top hE.measure_lt_top.ne (measure_mono inter_subset_left)
  rw [hsplit, measure_union hdisj (hE.isClosed.measurableSet.inter measurableSet_Ioc),
    ENNReal.toReal_add hfin1 hfin2]

theorem p11_measure_Ioc_le {E : Set ℝ} {s t : ℝ} (h : s ≤ t) :
    (volume (E ∩ Ioc s t)).toReal ≤ t - s := by
  have : volume (E ∩ Ioc s t) ≤ ENNReal.ofReal (t - s) := by
    calc volume (E ∩ Ioc s t) ≤ volume (Ioc s t) := measure_mono inter_subset_right
      _ = ENNReal.ofReal (t - s) := Real.volume_Ioc
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top this).trans
    (by rw [ENNReal.toReal_ofReal (sub_nonneg.2 h)])

theorem p11Phi_mono {E : Set ℝ} (hE : IsCompact E) {s t : ℝ} (h : s ≤ t) :
    p11Phi E s ≤ p11Phi E t := by
  rw [p11Phi_add hE h]; linarith [ENNReal.toReal_nonneg (a := volume (E ∩ Ioc s t))]

theorem p11Phi_sub_le {E : Set ℝ} (hE : IsCompact E) {s t : ℝ} (h : s ≤ t) :
    p11Phi E t - p11Phi E s ≤ t - s := by
  rw [p11Phi_add hE h]; linarith [p11_measure_Ioc_le (E := E) h]

/-- `stepP:p11a:ss-phi`: continuity of the distribution function. -/
theorem p11Phi_continuous {E : Set ℝ} (hE : IsCompact E) : Continuous (p11Phi E) := by
  have : LipschitzWith 1 (p11Phi E) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases le_total x y with h | h
    · rw [abs_sub_comm, abs_of_nonneg (by linarith [p11Phi_mono hE h]),
        abs_of_nonpos (by linarith)]
      linarith [p11Phi_sub_le hE h]
    · rw [abs_of_nonneg (by linarith [p11Phi_mono hE h]), abs_of_nonneg (by linarith)]
      linarith [p11Phi_sub_le hE h]
  exact this.continuous

theorem p11Phi_of_lt_inf {E : Set ℝ} (hE : IsCompact E) {s t : ℝ} (h : s ≤ t)
    (hempty : E ∩ Ioc s t = ∅) : p11Phi E t = p11Phi E s := by
  rw [p11Phi_add hE h, hempty]; simp

/-- Total mass at `b` when `E ⊆ Icc a b`. -/
theorem p11Phi_top {E : Set ℝ} {a b : ℝ} (hEab : E ⊆ Icc a b) :
    p11Phi E b = (volume E).toReal := by
  unfold p11Phi
  congr 2
  exact inter_eq_left.2 fun x hx => (hEab hx).2

theorem p11Phi_bot {E : Set ℝ} {a : ℝ} (hE : E ⊆ Ici a) : p11Phi E a = 0 := by
  unfold p11Phi
  have : E ∩ Iic a ⊆ {a} := fun x hx => by
    exact le_antisymm hx.2 (hE hx.1)
  rw [measure_mono_null this Real.volume_singleton]; simp

/-- Natural-number core of `p11_prod_erase_nat`. -/
theorem p11_prod_range_dist (q i : ℕ) (hi : i ≤ q) :
    ∏ j ∈ Finset.range (q + 1), (if j = i then 1 else (if j < i then i - j else j - i)) =
      i.factorial * (q - i).factorial := by
  rw [← Finset.prod_range_mul_prod_Ico _ (Nat.le_succ_of_le hi : i ≤ q + 1)]
  have hIco : Finset.Ico i (q + 1) = insert i (Finset.Ico (i + 1) (q + 1)) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [hIco, Finset.prod_insert (by simp)]
  have hl : ∏ x ∈ Finset.range i, (if x = i then 1 else (if x < i then i - x else x - i)) =
      i.factorial := by
    rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.1 hx
    split_ifs <;> omega
  have hr : ∏ x ∈ Finset.Ico (i + 1) (q + 1),
      (if x = i then 1 else (if x < i then i - x else x - i)) = (q - i).factorial := by
    rw [Finset.prod_Ico_eq_prod_range, ← Finset.prod_range_add_one_eq_factorial,
      show q + 1 - (i + 1) = q - i by omega]
    refine Finset.prod_congr rfl fun x hx => ?_
    split_ifs <;> omega
  rw [hl, hr]; simp

/-- Integer-node product: `∏_{j ≠ i} |i - j| = i! (q-i)!` over `Fin (q+1)`. -/
theorem p11_prod_erase_nat (q : ℕ) (i : Fin (q + 1)) :
    ∏ j ∈ Finset.univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| =
      ((i : ℕ).factorial : ℝ) * ((q - (i : ℕ)).factorial : ℝ) := by
  have hi : (i : ℕ) ≤ q := Nat.lt_succ_iff.1 i.2
  set h : ℕ → ℕ := fun j => if j = (i : ℕ) then 1 else (if j < (i : ℕ) then (i : ℕ) - j else j - i)
    with hh
  have h1 : ∏ j ∈ Finset.univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| =
      ∏ j : Fin (q + 1), ((h (j : ℕ) : ℕ) : ℝ) := by
    rw [← Finset.prod_erase Finset.univ (f := fun j : Fin (q + 1) => ((h (j : ℕ) : ℕ) : ℝ))
      (a := i) (by simp [hh])]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne : (j : ℕ) ≠ (i : ℕ) := fun hji => (Finset.ne_of_mem_erase hj) (Fin.ext hji)
    simp only [hh, hne, ite_false]
    by_cases hlt : (j : ℕ) < (i : ℕ)
    · have hle : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_le.2 hlt.le
      simp only [hlt, ↓reduceIte]
      rw [abs_of_nonneg (sub_nonneg.2 hle), Nat.cast_sub hlt.le]
    · have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_le.2 (not_lt.1 hlt)
      simp only [hlt, ↓reduceIte]
      rw [abs_of_nonpos (sub_nonpos.2 hle), Nat.cast_sub (not_lt.1 hlt)]
      ring
  rw [h1, ← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun j => h j) (q + 1)]
  have := p11_prod_range_dist q i hi
  simp only [hh]
  rw [this]; push_cast; ring

/-- `stepP:p11a:ss-nodes`: every level `c ∈ (0, L]` of the distribution function is attained
at a point of `E`. -/
theorem p11_exists_node {E : Set ℝ} (hE : IsCompact E) {a b : ℝ} (hEab : E ⊆ Icc a b)
    {c : ℝ} (hc0 : 0 < c) (hcL : c ≤ (volume E).toReal) :
    ∃ t ∈ E, p11Phi E t = c := by
  have hab : a ≤ b := by
    by_contra h
    have : E = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have := hEab hx; linarith [this.1, this.2, not_le.1 h]
    simp [this] at hcL; linarith
  have hcont := p11Phi_continuous hE
  have h0 : p11Phi E a = 0 := p11Phi_bot fun x hx => (hEab hx).1
  have hb : p11Phi E b = (volume E).toReal := p11Phi_top hEab
  obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc hab hcont.continuousOn
    (show c ∈ Icc (p11Phi E a) (p11Phi E b) from ⟨by rw [h0]; exact hc0.le, by rw [hb]; exact hcL⟩)
  set F := E ∩ Iic s with hF
  have hFc : IsCompact F := hE.inter_right isClosed_Iic
  have hFne : F.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : p11Phi E s = 0 := by simp [p11Phi, ← hF, hne]
    linarith
  obtain ⟨t, ht, htmax⟩ := hFc.exists_isMaxOn hFne continuous_id.continuousOn
  refine ⟨t, ht.1, ?_⟩
  have hts : t ≤ s := ht.2
  rw [← hsc]
  symm
  apply p11Phi_of_lt_inf hE hts
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have hxF : x ∈ F := ⟨hx.1, hx.2.2⟩
  have h : x ≤ t := htmax hxF
  linarith [hx.2.1]

/-- Level `0` is attained at the minimum of a nonempty compact `E`. -/
theorem p11_exists_node_zero {E : Set ℝ} (hE : IsCompact E) (hne : E.Nonempty) :
    ∃ t ∈ E, p11Phi E t = 0 := by
  refine ⟨sInf E, hE.sInf_mem hne, ?_⟩
  unfold p11Phi
  have : E ∩ Iic (sInf E) ⊆ {sInf E} := fun x hx =>
    le_antisymm hx.2 (csInf_le hE.bddBelow hx.1)
  rw [measure_mono_null this Real.volume_singleton]; simp

/-- `stepP:p11a:ss-gaps`: the node products are bounded below by `i! (q-i)! (L/q)^q`. -/
theorem p11_gap_prod {q : ℕ} (hq : 1 ≤ q) {L : ℝ} (hL : 0 < L) {t : Fin (q + 1) → ℝ}
    (hgap : ∀ i j : Fin (q + 1), i < j → (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * (L / q) ≤ t j - t i)
    (i : Fin (q + 1)) :
    ((i : ℕ).factorial : ℝ) * ((q - (i : ℕ)).factorial : ℝ) * (L / q) ^ q ≤
      ∏ j ∈ Finset.univ.erase i, |t i - t j| := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hLq : 0 < L / q := div_pos hL hqpos
  have hterm : ∀ j ∈ Finset.univ.erase i,
      |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (L / q) ≤ |t i - t j| := by
    intro j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hgap j i hlt
      have hle : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_le.2 (Fin.le_def.1 hlt.le)
      rw [abs_of_nonneg (sub_nonneg.2 hle), abs_of_nonneg (by nlinarith)]
      linarith
    · have := hgap i j hlt
      have hle : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_le.2 (Fin.le_def.1 hlt.le)
      rw [abs_of_nonpos (sub_nonpos.2 hle), abs_of_nonpos (by nlinarith)]
      linarith
  calc ((i : ℕ).factorial : ℝ) * ((q - (i : ℕ)).factorial : ℝ) * (L / q) ^ q
      = (∏ j ∈ Finset.univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|) * (L / q) ^ q := by
        rw [p11_prod_erase_nat]
    _ = ∏ j ∈ Finset.univ.erase i, (|((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (L / q)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_erase_of_mem (Finset.mem_univ _)]
        simp
    _ ≤ ∏ j ∈ Finset.univ.erase i, |t i - t j| :=
        Finset.prod_le_prod₀ (fun j _ => mul_nonneg (abs_nonneg _) hLq.le) hterm

/-- `∑ᵢ 1/(i! (q-i)!) = 2^q / q!`. -/
theorem p11_sum_inv_factorial (q : ℕ) :
    ∑ i : Fin (q + 1), 1 / (((i : ℕ).factorial : ℝ) * ((q - (i : ℕ)).factorial : ℝ)) =
      2 ^ q / (q.factorial : ℝ) := by
  have hq : (q.factorial : ℝ) ≠ 0 := by positivity
  rw [Fin.sum_univ_eq_sum_range (fun i => 1 / (((i : ℕ).factorial : ℝ) *
    ((q - i).factorial : ℝ))) (q + 1)]
  have : ∀ i ∈ Finset.range (q + 1), 1 / (((i : ℕ).factorial : ℝ) * ((q - i).factorial : ℝ)) =
      (q.choose i : ℝ) / q.factorial := by
    intro i hi
    have hiq : i ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h := Nat.choose_mul_factorial_mul_factorial hiq
    have h' : (q.choose i : ℝ) * (i.factorial : ℝ) * ((q - i).factorial : ℝ) = q.factorial := by
      exact_mod_cast h
    field_simp
    linarith
  rw [Finset.sum_congr rfl this, ← Finset.sum_div]
  congr 1
  exact_mod_cast Nat.sum_range_choose q

/-- `bpP:p11a:scalar-sublevel`. -/
theorem scalar_sublevel {q : ℕ} (hq : 1 ≤ q) {a b beta eps : ℝ}
    (hab : a < b) (hbeta : 0 < beta) (heps : 0 < eps) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ q f (Icc a b))
    (hlow : ∀ t ∈ Ioo a b, beta ≤ |iteratedDeriv q f t|) :
    volume {t ∈ Icc a b | |f t| ≤ eps} ≤
      ENNReal.ofReal (2*q*(eps/beta)^((q : ℝ)⁻¹)) := by
  set E : Set ℝ := {t ∈ Icc a b | |f t| ≤ eps} with hEdef
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hEc : IsCompact E := by
    have hcl : IsClosed E := by
      have := (hf.continuousOn.abs).preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_Iic (a := eps))
      have hEeq : E = Icc a b ∩ (fun x => |f x|) ⁻¹' Iic eps := by
        rw [hEdef]; ext x; simp
      rwa [hEeq]
    exact isCompact_Icc.of_isClosed_subset hcl (fun x hx => hx.1)
  have hEab : E ⊆ Icc a b := fun x hx => hx.1
  have hfin : volume E ≠ ⊤ := hEc.measure_lt_top.ne
  set L := (volume E).toReal with hLdef
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hrhs : 0 ≤ 2 * (q : ℝ) * (eps / beta) ^ ((q : ℝ)⁻¹) := by positivity
  suffices hmain : L ≤ 2 * (q : ℝ) * (eps / beta) ^ ((q : ℝ)⁻¹) by
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hmain
  rcases hL0.eq_or_lt with hL | hL
  · rw [← hL]; exact hrhs
  -- nodes
  have hne : E.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [hLdef, h] at hL
  have hnode : ∀ i : Fin (q + 1), ∃ t ∈ E, p11Phi E t = ((i : ℕ) : ℝ) * L / q := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · obtain ⟨t, ht, h0⟩ := p11_exists_node_zero hEc hne
      exact ⟨t, ht, by rw [h0, hi]; simp⟩
    · have hipos : (0 : ℝ) < (i : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hi
      have hiq : ((i : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.lt_succ_iff.1 i.2
      refine p11_exists_node hEc hEab (by positivity) ?_
      rw [div_le_iff₀ hqpos]; nlinarith
  choose t htE htφ using hnode
  have hlt : ∀ i j : Fin (q + 1), i < j → t i < t j := by
    intro i j hij
    by_contra h
    have := p11Phi_mono hEc (not_lt.1 h)
    rw [htφ, htφ] at this
    have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := Nat.cast_lt.2 hij
    have : ((j : ℕ) : ℝ) * L / q ≤ ((i : ℕ) : ℝ) * L / q := this
    rw [div_le_div_iff_of_pos_right hqpos] at this
    nlinarith
  have hsm : StrictMono t := fun i j h => hlt i j h
  have hgap : ∀ i j : Fin (q + 1), i < j →
      (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * (L / q) ≤ t j - t i := by
    intro i j hij
    have := p11Phi_sub_le hEc (hlt i j hij).le
    rw [htφ, htφ] at this
    calc (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * (L / q)
        = ((j : ℕ) : ℝ) * L / q - ((i : ℕ) : ℝ) * L / q := by ring
      _ ≤ _ := this
  have ha : ∀ i, a ≤ t i := fun i => (hEab (htE i)).1
  have hb : ∀ i, t i ≤ b := fun i => (hEab (htE i)).2
  obtain ⟨ξ, hξ, hξeq⟩ := divided_difference hq hab hf t hsm ha hb
  have hξab : ξ ∈ Ioo a b := ⟨lt_of_le_of_lt (ha 0) hξ.1, lt_of_lt_of_le hξ.2 (hb _)⟩
  have hβξ := hlow ξ hξab
  set S := ∑ i, f (t i) / ∏ j ∈ Finset.univ.erase i, (t i - t j) with hS
  have hβS : beta ≤ (q.factorial : ℝ) * |S| := by
    have : |iteratedDeriv q f ξ| = (q.factorial : ℝ) * |S| := by
      rw [hξeq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q.factorial)]
      field_simp
    linarith
  have hLq : 0 < L / q := div_pos hL hqpos
  have hSle : |S| ≤ eps * (2 ^ q / (q.factorial : ℝ)) * (q / L) ^ q := by
    calc |S| ≤ ∑ i, |f (t i) / ∏ j ∈ Finset.univ.erase i, (t i - t j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (q + 1), eps * (1 / (((i : ℕ).factorial : ℝ) * ((q - (i : ℕ)).factorial : ℝ))) *
            (q / L) ^ q := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hgp := p11_gap_prod hq hL hgap i
          rw [← Finset.abs_prod] at hgp
          have hprod_pos :
              0 < ((i : ℕ).factorial : ℝ) * ((q - (i : ℕ)).factorial : ℝ) * (L / q) ^ q := by
            positivity
          rw [abs_div]
          have hfi : |f (t i)| ≤ eps := (htE i).2
          have hden : 0 < |∏ j ∈ Finset.univ.erase i, (t i - t j)| := lt_of_lt_of_le hprod_pos hgp
          calc |f (t i)| / |∏ j ∈ Finset.univ.erase i, (t i - t j)|
              ≤ eps / (((i : ℕ).factorial : ℝ) * ((q - (i : ℕ)).factorial : ℝ) * (L / q) ^ q) :=
                div_le_div₀ heps.le hfi hprod_pos hgp
            _ = eps * (1 / (((i : ℕ).factorial : ℝ) * ((q - (i : ℕ)).factorial : ℝ))) *
                (q / L) ^ q := by
                rw [div_pow (q : ℝ) L q, div_pow L (q : ℝ) q]
                field_simp
      _ = eps * (2 ^ q / (q.factorial : ℝ)) * (q / L) ^ q := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, p11_sum_inv_factorial]
  have hfac : (0 : ℝ) < q.factorial := by positivity
  have h1 : beta ≤ eps * 2 ^ q * (q / L) ^ q := by
    calc beta ≤ (q.factorial : ℝ) * |S| := hβS
      _ ≤ (q.factorial : ℝ) * (eps * (2 ^ q / (q.factorial : ℝ)) * (q / L) ^ q) :=
          mul_le_mul_of_nonneg_left hSle hfac.le
      _ = eps * 2 ^ q * (q / L) ^ q := by field_simp
  have h2 : L ^ q ≤ (2 * (q : ℝ)) ^ q * (eps / beta) := by
    have : beta * L ^ q ≤ eps * (2 * q) ^ q := by
      have := mul_le_mul_of_nonneg_right h1 (pow_nonneg hL.le q)
      calc beta * L ^ q ≤ eps * 2 ^ q * (q / L) ^ q * L ^ q := this
        _ = eps * (2 * q) ^ q := by
          rw [div_pow, mul_pow]; field_simp
    rw [mul_div_assoc', le_div_iff₀ hbeta]; linarith
  have h3 : (2 * (q : ℝ) * (eps / beta) ^ ((q : ℝ)⁻¹)) ^ q = (2 * (q : ℝ)) ^ q * (eps / beta) := by
    rw [mul_pow, Real.rpow_inv_natCast_pow (by positivity) (by omega)]
  exact le_of_pow_le_pow_left₀ (by omega) hrhs (h3 ▸ h2)

end KAM.Planetary
