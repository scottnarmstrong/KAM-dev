/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.UniformLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parameter integrals of holomorphic families (blueprint-W `bpW:w5:new-ham` step `n-field`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`riemann_uniform`: a function of `t ∈ [0,1]` that is `L`-Lipschitz has Riemann sums within `L/n` of
its integral. `smoothing_integral`: if `P_t, Y_t` (`t ∈ [0,1]`) are holomorphic families with
`DP_t = L (Y_t)` and uniformly Lipschitz in `t`, then `∫₀¹ P_t` is holomorphic with derivative
`L (∫₀¹ Y_t)`, and `∫₀¹ Y_t` is holomorphic (via `holomorphic_of_tendstoUniformlyOn`).
-/

@[expose] public section

open Set Metric Filter Topology MeasureTheory intervalIntegral

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Riemann sums of a Lipschitz function** on `[0,1]`. -/
theorem norm_integral_sub_riemann_le {f : ℝ → F} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖f t - f t'‖ ≤ L * |t - t'|) (n : ℕ)
    (hn : 0 < n) :
    ‖(∫ t in (0 : ℝ)..1, f t) - (1 / (n : ℝ)) • ∑ i ∈ Finset.range n, f (i / n)‖ ≤ L / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcont : ContinuousOn f (Icc 0 1) := by
    intro t ht
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ⟨ε / (L + 1), by positivity, fun {t'} ht' hd => ?_⟩
    have := hf t' ht' t ht
    rw [dist_eq_norm]
    rw [Real.dist_eq] at hd
    calc ‖f t' - f t‖ ≤ L * |t' - t| := this
      _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hd.le hL
      _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
  have hint : ∀ k < n, IntervalIntegrable f volume ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n) := by
    intro k hk
    refine (hcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le (by gcongr; simp)]
    intro x hx
    constructor
    · exact le_trans (by positivity) hx.1
    · refine hx.2.trans ?_
      rw [div_le_one hn']
      exact_mod_cast hk
  have hsum := sum_integral_adjacent_intervals (f := f) (μ := volume) (a := fun k : ℕ => (k : ℝ) / n)
    hint
  simp only [Nat.cast_zero, zero_div] at hsum
  have hnn : ((n : ℕ) : ℝ) / n = 1 := div_self hn'.ne'
  rw [hnn] at hsum
  rw [← hsum]
  have hconst : ∀ k ∈ Finset.range n,
      ∫ t in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), f ((k : ℝ) / n) = (1 / (n : ℝ)) • f ((k : ℝ) / n) := by
    intro k _
    rw [intervalIntegral.integral_const]
    congr 1
    push_cast
    field_simp
    ring
  have : (1 / (n : ℝ)) • ∑ i ∈ Finset.range n, f (i / n) =
      ∑ k ∈ Finset.range n, ∫ t in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), f ((k : ℝ) / n) := by
    rw [Finset.smul_sum]
    exact (Finset.sum_congr rfl hconst).symm
  rw [this, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k ∈ Finset.range n,
      ‖(∫ t in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), f t) -
        ∫ t in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), f ((k : ℝ) / n)‖ ≤ L / n / n := by
    intro k hk'
    have hk2 : k < n := Finset.mem_range.mp hk'
    have hik := hint k hk2
    rw [← integral_sub hik intervalIntegrable_const]
    have hlen : |((k + 1 : ℕ) : ℝ) / n - (k : ℝ) / n| = 1 / n := by
      push_cast
      rw [show ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n by field_simp; ring]
      exact abs_of_pos (by positivity)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k : ℝ) / n)
      (b := ((k + 1 : ℕ) : ℝ) / n) (C := L / n) (f := fun t => f t - f ((k : ℝ) / n)) (by
        intro t ht
        rw [uIoc_of_le (by gcongr; simp)] at ht
        have hk3 : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
          constructor
          · positivity
          · rw [div_le_one hn']; exact_mod_cast hk2.le
        have ht3 : t ∈ Icc (0 : ℝ) 1 := by
          constructor
          · exact le_trans (by positivity) ht.1.le
          · refine ht.2.trans ?_
            rw [div_le_one hn']
            exact_mod_cast hk2
        have h5 := hf t ht3 _ hk3
        refine h5.trans ?_
        have : |t - (k : ℝ) / n| ≤ 1 / n := by
          rw [abs_of_nonneg (by linarith [ht.1])]
          have := ht.2
          push_cast at this
          have e : ((k : ℝ) + 1) / n = (k : ℝ) / n + 1 / n := by field_simp
          linarith
        calc L * |t - (k : ℝ) / n| ≤ L * (1 / n) := mul_le_mul_of_nonneg_left this hL
          _ = L / n := by ring)
    rw [hlen] at this
    calc _ ≤ L / n * (1 / n) := this
      _ = L / n / n := by ring
  refine (Finset.sum_le_sum hk).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  exact le_rfl

end KAM.Wave
