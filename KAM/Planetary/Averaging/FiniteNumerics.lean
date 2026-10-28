/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# P Part 2: the numerical inequalities of the finite averaging iteration (`stepP:p2:nfb-first`,
`stepP:p2:nfb-N`, `stepP:p2:nfb-ind`)

Pure real-number lemmas: the first step (cases A and B), the inductive step with ratio `1/4`,
the choice of the number of steps `N = ⌊κ/(12 ln 2)⌋`, and the geometric sums. No operator
analysis enters here. Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-12.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Planetary

theorem exp_one_gt_27 : (27 : ℝ) / 10 < Real.exp 1 := by
  have := Real.exp_one_gt_d9
  linarith

/-- The inverse `(1 - 2u)⁻¹` for a small `u`. -/
theorem inv_one_sub_le {u t : ℝ} (hu : u ≤ t) (ht : t < 1 / 2) :
    (1 - 2 * u)⁻¹ ≤ (1 - 2 * t)⁻¹ :=
  inv_anti₀ (by linarith) (by linarith)

/-- First step, case A (`q = e^{-κ/6} ≤ y₀ = E/Q`): the remainder is at most `3E/(4κ)`. -/
theorem step_first {Q E κ q : ℝ} (hQ : 0 < Q) (hE : 0 ≤ E) (hκ : 6 ≤ κ)
    (hy : E / Q ≤ 3 / (8 * κ)) (hq0 : 0 ≤ q) (hq : q ≤ E / Q) :
    (1 - 2 * (1 * E / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (0 + E) + q) * E ≤ 3 * E / (4 * κ) := by
  have hκ0 : 0 < κ := by linarith
  set y := E / Q with hyd
  have hEy : E = y * Q := by rw [hyd]; field_simp
  have hy0 : 0 ≤ y := div_nonneg hE hQ.le
  have hy16 : y ≤ 1 / 16 := by
    refine hy.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h1 : (1 - 2 * (1 * E / Q))⁻¹ ≤ 8 / 7 := by
    rw [one_mul, ← hyd]
    refine (inv_one_sub_le hy16 (by norm_num)).trans ?_
    norm_num
  have h2 : 2 * 1 / (Real.exp 1 * Q) * (0 + E) = 2 * y / Real.exp 1 := by
    rw [hEy, zero_add]; field_simp
  have he := exp_one_gt_27
  have h3 : 2 * y / Real.exp 1 ≤ 3 / 4 * y := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h5 : (1 - 2 * (1 * E / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (0 + E) + q) ≤
      8 / 7 * (7 / 4 * y) := by
    rw [h2]
    refine mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  calc (1 - 2 * (1 * E / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (0 + E) + q) * E
      ≤ (2 * y) * E := mul_le_mul_of_nonneg_right (h5.trans (by linarith)) hE
    _ ≤ (2 * (3 / (8 * κ))) * E := mul_le_mul_of_nonneg_right (by linarith) hE
    _ = 3 * E / (4 * κ) := by field_simp; ring

/-- First step, case B (single doubled-loss step): the remainder is at most `q E`. -/
theorem step_single {Q E q x : ℝ} (hQ : 0 < Q) (hE : 0 ≤ E) (hq0 : 0 ≤ q)
    (hu : E / Q ≤ q / 4) (hu2 : E / Q ≤ 1 / 64) (hx : Real.exp (-x) ≤ q / 2) :
    (1 - 2 * (1 * E / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (0 + E) + Real.exp (-x)) * E ≤ q * E := by
  set y := E / Q with hyd
  have hEy : E = y * Q := by rw [hyd]; field_simp
  have hy0 : 0 ≤ y := div_nonneg hE hQ.le
  have h1 : (1 - 2 * (1 * E / Q))⁻¹ ≤ 32 / 31 := by
    rw [one_mul, ← hyd]
    refine (inv_one_sub_le hu2 (by norm_num)).trans ?_
    norm_num
  have h2 : 2 * 1 / (Real.exp 1 * Q) * (0 + E) = 2 * y / Real.exp 1 := by
    rw [hEy, zero_add]; field_simp
  have he : 2 < Real.exp 1 := by have := exp_one_gt_27; linarith
  have h3 : 2 * y / Real.exp 1 ≤ q / 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h5 : (1 - 2 * (1 * E / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (0 + E) + Real.exp (-x)) ≤
      32 / 31 * (3 / 4 * q) := by
    rw [h2]
    refine mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  calc (1 - 2 * (1 * E / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (0 + E) + Real.exp (-x)) * E
      ≤ q * E := mul_le_mul_of_nonneg_right (h5.trans (by linarith)) hE

/-- The inductive step: ratio `1/4`. -/
theorem step_big {Q δ st x : ℝ} (hQ : 0 < Q) (hδ0 : 0 ≤ δ) (hδ : δ ≤ Q / 256) (hst0 : 0 ≤ st)
    (hst : st ≤ Q / 16) (hx : Real.exp (-x) ≤ 1 / 8) :
    (1 - 2 * (1 * δ / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (st + δ) + Real.exp (-x)) * δ ≤
      δ / 4 := by
  have hu : δ / Q ≤ 1 / 256 := by
    rw [div_le_iff₀ hQ]; linarith
  have h1 : (1 - 2 * (1 * δ / Q))⁻¹ ≤ 128 / 127 := by
    rw [one_mul]
    refine (inv_one_sub_le hu (by norm_num)).trans ?_
    norm_num
  have he := exp_one_gt_27
  have h3 : 2 * 1 / (Real.exp 1 * Q) * (st + δ) ≤ 1 / 10 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : 27 / 10 * Q ≤ Real.exp 1 * Q := mul_le_mul_of_nonneg_right he.le hQ.le
    nlinarith
  have h5 : (1 - 2 * (1 * δ / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (st + δ) + Real.exp (-x)) ≤
      128 / 127 * (1 / 10 + 1 / 8) := by
    refine mul_le_mul h1 (add_le_add h3 hx) (by positivity) (by norm_num)
  calc (1 - 2 * (1 * δ / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (st + δ) + Real.exp (-x)) * δ
      ≤ (1 / 4) * δ := mul_le_mul_of_nonneg_right (h5.trans (by norm_num)) hδ0
    _ = δ / 4 := by ring

/-- `∑_{i<l} 4^{-i} ≤ 4/3`. -/
theorem geom_quarter (l : ℕ) : ∑ i ∈ Finset.range l, (1 / 4 : ℝ) ^ i ≤ 4 / 3 := by
  have : ∑ i ∈ Finset.range l, (1 / 4 : ℝ) ^ i = 4 / 3 - 4 / 3 * (1 / 4) ^ l := by
    induction l with
    | zero => norm_num
    | succ l ih => rw [Finset.sum_range_succ, ih]; ring
  rw [this]
  have : 0 ≤ (1 / 4 : ℝ) ^ l := by positivity
  linarith

/-- The number of steps `N = ⌊κ/(12 ln 2)⌋`. -/
theorem steps_lt {κ : ℝ} (hκ : 0 < κ) : (⌊κ / (12 * Real.log 2)⌋₊ : ℝ) < κ / 8 := by
  have hl := Real.log_two_gt_d9
  have h12 : 0 < 12 * Real.log 2 := by linarith
  have h1 := Nat.floor_le (div_nonneg hκ.le h12.le)
  refine h1.trans_lt ?_
  rw [div_lt_div_iff₀ h12 (by norm_num)]
  nlinarith

theorem steps_le {κ : ℝ} (hκ : 0 < κ) : (⌊κ / (12 * Real.log 2)⌋₊ : ℝ) * (12 * Real.log 2) ≤ κ := by
  have hl := Real.log_two_gt_d9
  have h12 : 0 < 12 * Real.log 2 := by linarith
  have h1 := Nat.floor_le (div_nonneg hκ.le h12.le)
  rwa [le_div_iff₀ h12] at h1

theorem steps_succ_gt {κ : ℝ} :
    κ < ((⌊κ / (12 * Real.log 2)⌋₊ : ℝ) + 1) * (12 * Real.log 2) := by
  have hl := Real.log_two_gt_d9
  have h12 : 0 < 12 * Real.log 2 := by linarith
  have h1 := Nat.lt_floor_add_one (κ / (12 * Real.log 2))
  rwa [div_lt_iff₀ h12] at h1

/-- `exp (-(κ/(4N))) ≤ 1/8` when `N ≤ κ/(12 ln 2)`. -/
theorem exp_step_le {κ N : ℝ} (hN : 0 < N) (hle : N * (12 * Real.log 2) ≤ κ) :
    Real.exp (-(κ / (4 * N))) ≤ 1 / 8 := by
  have h3 : 3 * Real.log 2 ≤ κ / (4 * N) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have h8 : Real.exp (-(3 * Real.log 2)) = 1 / 8 := by
    rw [Real.exp_neg, show 3 * Real.log 2 = Real.log ((2 : ℝ) ^ 3) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]
    norm_num
  rw [← h8]
  exact Real.exp_le_exp.2 (by linarith)

/-- `4^{-(N+1)} < e^{-κ/6}` for `N+1 > κ/(12 ln 2)`. -/
theorem quarter_pow_lt {κ : ℝ} {N : ℕ} (hlt : κ < ((N : ℝ) + 1) * (12 * Real.log 2)) :
    (1 / 4 : ℝ) ^ (N + 1) < Real.exp (-(κ / 6)) := by
  have h4 : Real.exp (2 * Real.log 2) = 4 := by
    rw [show 2 * Real.log 2 = Real.log ((2 : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]
    norm_num
  have h1 : Real.exp (κ / 6) < 4 ^ (N + 1) := by
    have := Real.exp_nat_mul (2 * Real.log 2) (N + 1)
    rw [h4] at this
    rw [← this]
    refine Real.exp_lt_exp.2 ?_
    push_cast
    nlinarith
  have h2 : (1 / 4 : ℝ) ^ (N + 1) = (4 ^ (N + 1))⁻¹ := by
    rw [one_div, inv_pow]
  rw [h2, Real.exp_neg]
  exact inv_strictAnti₀ (Real.exp_pos _) h1

/-- No steps are possible in case A: `e^{-κ/6} ≤ 1/16` forces `N ≥ 1`. -/
theorem steps_pos {κ : ℝ} (hq : Real.exp (-(κ / 6)) ≤ 1 / 16) :
    1 ≤ ⌊κ / (12 * Real.log 2)⌋₊ := by
  by_contra hN
  have h0 : ⌊κ / (12 * Real.log 2)⌋₊ = 0 := by omega
  have hl := Real.log_two_gt_d9
  have h12 : 0 < 12 * Real.log 2 := by linarith
  have := steps_succ_gt (κ := κ)
  rw [h0] at this
  push_cast at this
  have h4 : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
    rw [Real.exp_neg, show 2 * Real.log 2 = Real.log ((2 : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num)]
    norm_num
  have : (1 / 4 : ℝ) < Real.exp (-(κ / 6)) := by
    rw [← h4]
    exact Real.exp_lt_exp.2 (by linarith)
  linarith

end KAM.Planetary

end
