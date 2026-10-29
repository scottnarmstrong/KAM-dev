/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.IsDiophantine
public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Dirichlet emptiness of `Dio_{γ,τ}` for `τ < n - 1` (graph gap GAP-I1a, ruling N1)

For `n ≥ 2` and `γ > 0` there is no `(γ, τ)`-Diophantine vector in `ℝⁿ` when `τ < n - 1`
(pigeonhole on the values `k · ω`, `k ∈ {0, …, N}ⁿ`). Hence the Part 1 specialization
`τ ≥ n - 1` of `KAM.Iso.Linear.Setting` is vacuous relative to the source's `τ ≥ 0`.

* `KAM.DioDirichlet.exists_small_combination`: the pigeonhole step.
* `KAM.IsDiophantine.n_sub_one_le_tau`: `2 ≤ n → 0 < γ → IsDiophantine γ τ ω → n - 1 ≤ τ`.
-/

public section

namespace KAM.DioDirichlet

open Finset

/-- The bucket `min ⌊t⌋₊ (m - 1)` of `t ∈ [0, m]` is within `1` of `t`. -/
theorem bucket_bounds {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ m) :
    ((min ⌊t⌋₊ (m - 1) : ℕ) : ℝ) ≤ t ∧ t ≤ ((min ⌊t⌋₊ (m - 1) : ℕ) : ℝ) + 1 := by
  have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; simp
  rcases le_total ⌊t⌋₊ (m - 1) with h | h
  · rw [min_eq_left h]
    exact ⟨Nat.floor_le h0, (Nat.lt_floor_add_one t).le⟩
  · rw [min_eq_right h, hc]
    have h2 : ((m - 1 : ℕ) : ℝ) ≤ t := by
      have : ((m - 1 : ℕ) : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast h
      exact this.trans (Nat.floor_le h0)
    constructor <;> linarith

/-- Pigeonhole: for `n, N ≥ 1` there is a nonzero `d ∈ ℤⁿ`, `|d_i| ≤ N`, with
`|d · ω| Nⁿ ≤ 2 N ∑ |ω_i|`. -/
theorem exists_small_combination {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN : 1 ≤ N) (ω : Fin n → ℝ) :
    ∃ d : Fin n → ℤ, d ≠ 0 ∧ (∀ i, |(d i : ℝ)| ≤ N) ∧
      |∑ i, (d i : ℝ) * ω i| * (N : ℝ) ^ n ≤ 2 * N * ∑ i, |ω i| := by
  set a : ℝ := ∑ i, |ω i| with ha
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun i _ => abs_nonneg _
  set i0 : Fin n := ⟨0, hn⟩
  rcases ha0.eq_or_lt with ha | ha
  · refine ⟨Pi.single i0 1, fun h => ?_, fun i => ?_, ?_⟩
    · have := congrFun h i0
      simp at this
    · by_cases hi : i = i0
      · subst hi; simp [Nat.one_le_cast.2 hN]
      · simp [Pi.single_eq_of_ne hi]
    · have hz : ∀ i, ω i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (ω i))).1 ha.symm i
          (Finset.mem_univ _)
        exact abs_eq_zero.1 this
      simp [hz, ← ha]
  · -- the pigeonhole
    set m : ℕ := (N + 1) ^ n - 1 with hmdef
    have hNn : N ^ n < (N + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self N) (by omega)
    have hNpos : 0 < N ^ n := Nat.pow_pos hN
    have hm1 : 1 ≤ m := by omega
    have hmN : (N : ℝ) ^ n ≤ m := by
      have : N ^ n ≤ m := by omega
      exact_mod_cast this
    have hL : 0 < 2 * (N : ℝ) * a := by
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    let x : (Fin n → Fin (N + 1)) → ℝ := fun k => ∑ i, ((k i : ℕ) : ℝ) * ω i
    have hx : ∀ k, |x k| ≤ N * a := by
      intro k
      calc |x k| ≤ ∑ i, |((k i : ℕ) : ℝ) * ω i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (N : ℝ) * |ω i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, Nat.abs_cast]
          have : ((k i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (k i).2
          exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = N * a := by rw [← Finset.mul_sum]
    let t : (Fin n → Fin (N + 1)) → ℝ := fun k => (x k + N * a) * m / (2 * N * a)
    have ht0 : ∀ k, 0 ≤ t k := fun k => by
      have := (abs_le.1 (hx k)).1
      have : 0 ≤ x k + N * a := by linarith
      positivity
    have htm : ∀ k, t k ≤ m := fun k => by
      have := (abs_le.1 (hx k)).2
      have h : x k + N * a ≤ 2 * N * a := by linarith
      rw [div_le_iff₀ hL, mul_comm (m : ℝ)]
      exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
    have hcard : (Finset.range m).card < (Finset.univ : Finset (Fin n → Fin (N + 1))).card := by
      simp only [Finset.card_range, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      omega
    obtain ⟨k, -, k', -, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun k => min ⌊t k⌋₊ (m - 1)) (fun k _ =>
        Finset.mem_range.2 (lt_of_le_of_lt (min_le_right _ _) (by omega)))
    obtain ⟨hk1, hk2⟩ := bucket_bounds hm1 (ht0 k) (htm k)
    obtain ⟨hk1', hk2'⟩ := bucket_bounds hm1 (ht0 k') (htm k')
    have heq : min ⌊t k⌋₊ (m - 1) = min ⌊t k'⌋₊ (m - 1) := heq
    rw [heq] at hk1 hk2
    have htt : |t k - t k'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have hxx : |x k - x k'| * m ≤ 2 * N * a := by
      have : t k - t k' = (x k - x k') * m / (2 * N * a) := by simp only [t]; ring
      rw [this, abs_div, abs_mul, abs_of_pos hL, div_le_one hL, Nat.abs_cast] at htt
      exact htt
    refine ⟨fun i => ((k i : ℕ) : ℤ) - ((k' i : ℕ) : ℤ), ?_, ?_, ?_⟩
    · intro h
      apply hne
      funext i
      have := congrFun h i
      simp only [Pi.zero_apply, sub_eq_zero] at this
      exact Fin.ext (by exact_mod_cast this)
    · intro i
      have h1 : ((k i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (k i).2
      have h2 : ((k' i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (k' i).2
      have h3 : (0 : ℝ) ≤ ((k i : ℕ) : ℝ) := Nat.cast_nonneg _
      have h4 : (0 : ℝ) ≤ ((k' i : ℕ) : ℝ) := Nat.cast_nonneg _
      push_cast
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · have hs : ∑ i, (((((k i : ℕ) : ℤ) - ((k' i : ℕ) : ℤ) : ℤ)) : ℝ) * ω i = x k - x k' := by
        simp only [x, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [hs]
      calc |x k - x k'| * (N : ℝ) ^ n ≤ |x k - x k'| * m :=
            mul_le_mul_of_nonneg_left hmN (abs_nonneg _)
        _ ≤ 2 * N * a := hxx

end KAM.DioDirichlet

namespace KAM.IsDiophantine

open KAM.DioDirichlet

/-- Dirichlet emptiness of `Dio_{γ,τ}` for `τ < n - 1` (`n ≥ 2`, `γ > 0`). -/
theorem n_sub_one_le_tau {n : ℕ} (hn : 2 ≤ n) {γ τ : ℝ} (hγ : 0 < γ) {ω : Fin n → ℝ}
    (h : KAM.IsDiophantine γ τ ω) : (n : ℝ) - 1 ≤ τ := by
  by_contra hlt
  push Not at hlt
  have hn1 : 1 ≤ n := by omega
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set τp : ℝ := max τ 0 with hτp
  have hτp0 : 0 ≤ τp := le_max_right _ _
  have hτpτ : τ ≤ τp := le_max_left _ _
  have he : 0 < (n : ℝ) - 1 - τp := by
    have : τp < n - 1 := max_lt hlt (by linarith)
    linarith
  set C : ℝ := 2 * (∑ i, |ω i|) * (n : ℝ) ^ τp with hC
  -- every `N ≥ 1` gives `γ N^e ≤ C`
  have key : ∀ N : ℕ, 1 ≤ N → γ * (N : ℝ) ^ ((n : ℝ) - 1 - τp) ≤ C := by
    intro N hN
    obtain ⟨d, hd0, hdN, hdω⟩ := exists_small_combination hn1 hN ω
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by linarith
    set s : ℝ := ∑ i, |(d i : ℝ)| with hs
    have hs1 : 1 ≤ s := by
      obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hd0 (funext hcon)
      have hj1 : (1 : ℝ) ≤ |(d j : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hj
      exact hj1.trans (Finset.single_le_sum (f := fun i => |(d i : ℝ)|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ j))
    have hsN : s ≤ n * N := by
      calc s ≤ ∑ _i : Fin n, (N : ℝ) := Finset.sum_le_sum fun i _ => hdN i
        _ = n * N := by simp
    have hspos : 0 < s ^ τ := Real.rpow_pos_of_pos (by linarith) _
    have hD := h d hd0
    rw [div_le_iff₀ hspos] at hD
    have hspow : s ^ τ ≤ ((n : ℝ) * N) ^ τp := by
      calc s ^ τ ≤ s ^ τp := Real.rpow_le_rpow_of_exponent_le hs1 hτpτ
        _ ≤ ((n : ℝ) * N) ^ τp := Real.rpow_le_rpow (by linarith) hsN hτp0
    set w : ℝ := |∑ i, (d i : ℝ) * ω i| with hw
    have hNn : (0 : ℝ) < (N : ℝ) ^ n := by positivity
    have hw' : w ≤ 2 * N * (∑ i, |ω i|) / (N : ℝ) ^ n := by
      rw [le_div_iff₀ hNn]; exact hdω
    have hγ' : γ ≤ w * ((n : ℝ) * N) ^ τp := by
      calc γ ≤ w * s ^ τ := hD
        _ ≤ w * ((n : ℝ) * N) ^ τp :=
          mul_le_mul_of_nonneg_left hspow (abs_nonneg _)
    have hpow : (N : ℝ) ^ ((n : ℝ) - 1 - τp) * (N : ℝ) ^ τp * N = (N : ℝ) ^ n := by
      rw [← Real.rpow_add hNpos, show (n : ℝ) - 1 - τp + τp = n - 1 by ring,
        ← Real.rpow_add_one hNpos.ne', show (n : ℝ) - 1 + 1 = n by ring, Real.rpow_natCast]
    have hfin : γ * (N : ℝ) ^ ((n : ℝ) - 1 - τp) ≤ C := by
      have h1 : γ * (N : ℝ) ^ ((n : ℝ) - 1 - τp) ≤
          2 * N * (∑ i, |ω i|) / (N : ℝ) ^ n * ((n : ℝ) * N) ^ τp *
            (N : ℝ) ^ ((n : ℝ) - 1 - τp) :=
        mul_le_mul_of_nonneg_right (hγ'.trans (mul_le_mul_of_nonneg_right hw'
          (Real.rpow_nonneg (by positivity) _))) (Real.rpow_nonneg hNpos.le _)
      refine h1.trans (le_of_eq ?_)
      rw [Real.mul_rpow (by positivity) hNpos.le, hC, ← hpow]
      field_simp
    exact hfin
  -- contradiction for large `N`
  have hev : ∀ᶠ N : ℕ in Filter.atTop, C / γ < (N : ℝ) ^ ((n : ℝ) - 1 - τp) :=
    (tendsto_rpow_atTop he |>.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨N, hN, hN1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  have := key N hN1
  rw [div_lt_iff₀ hγ] at hN
  linarith

end KAM.IsDiophantine
