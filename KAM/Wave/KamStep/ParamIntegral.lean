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
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ⟨ε / (L + 1), by positivity, fun {t'} ht' hd
        => ?_⟩
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
  have hsum := sum_integral_adjacent_intervals (f := f) (μ := volume) (a := fun k : ℕ => (k : ℝ) /
      n)
    hint
  simp only [Nat.cast_zero, zero_div] at hsum
  have hnn : ((n : ℕ) : ℝ) / n = 1 := div_self hn'.ne'
  rw [hnn] at hsum
  rw [← hsum]
  have hconst : ∀ k ∈ Finset.range n,
      ∫ t in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), f ((k : ℝ) / n) = (1 / (n : ℝ)) • f ((k : ℝ) /
          n) := by
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

section smoothing

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Riemann sums `(1/n) ∑_{i<n} f(i/n)` of a family. -/
noncomputable def riemannSum {β : Type*} [AddCommMonoid β] [Module ℝ β] (f : ℝ → β) (n : ℕ) : β :=
  (1 / (n : ℝ)) • ∑ i ∈ Finset.range n, f (i / n)

theorem tendstoUniformlyOn_riemann {α : Type*} {S : Set α} {f : ℝ → α → G} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ w ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖f t w - f t' w‖ ≤ L * |t - t'|) :
    TendstoUniformlyOn (fun n (w : α) => riemannSum (fun t => f t w) n)
      (fun w => ∫ t in (0 : ℝ)..1, f t w) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (L / ε)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn w hw
  have hn0 : 0 < n := by omega
  have h := norm_integral_sub_riemann_le hL (hf w hw) n hn0
  rw [dist_eq_norm]
  unfold riemannSum
  refine h.trans_lt ?_
  have hnN : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
  rw [div_lt_iff₀ (by positivity)]
  have : L < ε * N := by rwa [div_lt_iff₀ hε, mul_comm] at hN
  nlinarith

/-- **Integral of a holomorphic smoothing family** (`n-field`). -/
theorem smoothing_integral {U : Set E} (hU : IsOpen U) (Lop : G →L[ℂ] (E →L[ℂ] ℂ))
    {P : ℝ → E → ℂ} {Y : ℝ → E → G} {Lp Ly : ℝ} (hLp : 0 ≤ Lp) (hLy : 0 ≤ Ly)
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ U, HasFDerivAt (P t) (Lop (Y t w)) w)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (Y t) U)
    (hPL : ∀ w ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖P t w - P t' w‖ ≤ Lp * |t - t'|)
    (hYL : ∀ w ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖Y t w - Y t' w‖ ≤ Ly * |t - t'|) :
    DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1, P t w) U ∧
      DifferentiableOn ℂ (fun w => ∫ t in (0 : ℝ)..1, Y t w) U ∧
      ∀ w ∈ U, HasFDerivAt (fun w => ∫ t in (0 : ℝ)..1, P t w)
        (Lop (∫ t in (0 : ℝ)..1, Y t w)) w := by
  set fn : ℕ → E → ℂ := fun n w => riemannSum (fun t => P t w) n with hfn
  set Yn : ℕ → E → G := fun n w => riemannSum (fun t => Y t w) n with hYn
  have hPu := tendstoUniformlyOn_riemann (S := U) (f := P) hLp hPL
  have hYu := tendstoUniformlyOn_riemann (S := U) (f := Y) hLy hYL
  -- differentiability of the sums
  have hfd : ∀ n, ∀ w ∈ U, HasFDerivAt (fn n) (Lop (Yn n w)) w := by
    intro n w hw
    have h : ∀ i ∈ Finset.range n, HasFDerivAt (fun w => P ((i : ℝ) / n) w)
        (Lop (Y ((i : ℝ) / n) w)) w := by
      intro i hi
      have hin : (i : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
        have hi' := Finset.mem_range.mp hi
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        exact ⟨by positivity, by rw [div_le_one hn0]; exact_mod_cast hi'.le⟩
      exact hP _ hin w hw
    have hs := HasFDerivAt.sum h
    have hs2 := hs.const_smul ((1 : ℝ) / n)
    have e1 : fn n = ((1 : ℝ) / n) • ∑ i ∈ Finset.range n, fun w => P ((i : ℝ) / n) w := by
      funext w; simp [hfn, riemannSum, Finset.sum_apply]
    have e2 : Lop (Yn n w) = ((1 : ℝ) / n) • ∑ i ∈ Finset.range n, Lop (Y ((i : ℝ) / n) w) := by
      simp [hYn, riemannSum, map_sum, ContinuousLinearMap.map_smul_of_tower]
    rw [e1, e2]; exact hs2
  have hdiffn : ∀ n, DifferentiableOn ℂ (fn n) U := fun n w hw =>
    (hfd n w hw).differentiableAt.differentiableWithinAt
  have hYdn : ∀ n, DifferentiableOn ℂ (Yn n) U := by
    intro n
    have hsum : DifferentiableOn ℂ (fun w => ∑ i ∈ Finset.range n, Y ((i : ℝ) / n) w) U := by
      refine DifferentiableOn.fun_sum fun i hi => hY _ ?_
      have hi' := Finset.mem_range.mp hi
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      exact ⟨by positivity, by rw [div_le_one hn0]; exact_mod_cast hi'.le⟩
    show DifferentiableOn ℂ (fun w => ((1 : ℝ) / n) • ∑ i ∈ Finset.range n, Y ((i : ℝ) / n) w) U
    exact hsum.const_smul _
  obtain ⟨hgd, hder⟩ := holomorphic_of_tendstoUniformlyOn hU hdiffn hPu
  obtain ⟨hYd, -⟩ := holomorphic_of_tendstoUniformlyOn hU hYdn hYu
  refine ⟨hgd, hYd, fun w hw => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU w hw
  have hδ : 0 < ε / 2 := by positivity
  have hsub : ball w (2 * (ε / 2)) ⊆ U := by
    have : 2 * (ε / 2) = ε := by ring
    rw [this]; exact hball
  have h1 := (hder hδ hsub).tendsto_at (mem_ball_self hδ)
  have h2 : Tendsto (fun n => fderiv ℂ (fn n) w) atTop (𝓝 (Lop (∫ t in (0 : ℝ)..1, Y t w))) := by
    have : ∀ n, fderiv ℂ (fn n) w = Lop (Yn n w) := fun n => (hfd n w hw).fderiv
    simp only [this]
    exact (Lop.continuous.tendsto _).comp (hYu.tendsto_at hw)
  have := tendsto_nhds_unique h1 h2
  rw [← this]
  exact (hgd.differentiableAt (hU.mem_nhds hw)).hasFDerivAt

end smoothing

end KAM.Wave
