/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.Schedule
public import KAM.Planetary.MaximalStep.Loss

/-! # P11B weak-KAM strip budget and elementary schedule properties

`strip_budget` (`bpP:p11a:strip-budget`): the cutoff losses `selectiond` are summable with total at
most `strip / 4`, the geometric widths `3 σ_j` sum to `strip / 4`, the strip radii stay above
`strip / 2` and the cutoff error is at most `ϖ / 8`. `schedule_props` (`bpP:p11a:schedule-props`):
the elementary properties (S1)–(S5) of the schedule. The two named bridges
`selectionCN_eq_p11C` and `selectionCutoffError_eq_p11Error` identify the schedule formulas with
the P11A ones, so that `loss_choice` and `loss_sum` apply.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

theorem selectionCN_eq_p11C (n : ℕ) : selectionCN n = p11C n := rfl

theorem selectionCutoffError_eq_p11Error (n : ℕ) (T d : ℝ) :
    selectionCutoffError n T d = p11Error n T d := by
  simp only [selectionCutoffError, p11Error, selectionCN, p11C, inv_pow]

/-- `0 < ϖ ≤ 1` for a nonnegative Diophantine exponent. -/
theorem selectionVarpi_pos_le_one (n μ : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 < selectionVarpi n μ τ ∧ selectionVarpi n μ τ ≤ 1 := by
  have hE : 0 ≤ selectionExponent n μ τ := by
    unfold selectionExponent
    positivity
  unfold selectionVarpi
  refine ⟨by positivity, ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)

/-- The schedule's cutoff loss is the P11A loss at tolerance `ϖ / 8`. -/
theorem selectiond_eq_p11Loss (a : SelectionSchedule n) (j : ℕ) :
    selectiond a j = p11Loss n (a.T₀ * 2 ^ j) (selectionVarpi n a.μ a.τ / 8) := by
  have hv : selectionVarpi n a.μ a.τ ≠ 0 := by
    unfold selectionVarpi
    positivity
  have h : 16 * selectionCN n / selectionVarpi n a.μ a.τ =
      2 * p11C n / (selectionVarpi n a.μ a.τ / 8) := by
    rw [selectionCN_eq_p11C]
    field_simp
    ring
  simp only [selectiond, p11Loss, selectionT, h]

/-- Logarithmic estimate `n log X ≤ s X / 32 + n log (32 n / s)` (`bpP:p11a:y-log`). -/
private theorem n_log_le {n : ℕ} (hn : 1 ≤ n) {s X : ℝ} (hs : 0 < s) (hX : 0 < X) :
    (n : ℝ) * Real.log X ≤ s * X / 32 + n * Real.log (32 * n / s) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy : 0 < s * X / (32 * n) := by positivity
  have hl := Real.log_le_sub_one_of_pos hy
  have hsplit : Real.log X = Real.log (s * X / (32 * n)) + Real.log (32 * n / s) := by
    rw [← Real.log_mul hy.ne' (by positivity)]
    congr 1
    field_simp
  have e : (n : ℝ) * (s * X / (32 * n) - 1) = s * X / 32 - n := by
    field_simp
  rw [hsplit, mul_add]
  have := mul_le_mul_of_nonneg_left hl hn0.le
  nlinarith

theorem strip_budget (a : SelectionSchedule n) (hn : 1 ≤ n) (hμ : 1 ≤ a.μ)
    (hτ : 0 ≤ a.τ) (hs : 0 < a.strip) (hs1 : a.strip ≤ 1) (hT : 1 ≤ a.T₀)
    (hT' : 16 / (π * a.strip) *
      (Real.log (16 * selectionCN n / selectionVarpi n a.μ a.τ) +
        n * Real.log (32 * n / a.strip)) ≤ a.T₀) :
    Summable (selectiond a) ∧ (∑' j, selectiond a j) ≤ a.strip / 4 ∧
    (∑' j, 3 * selectionσ a j) = a.strip / 4 ∧
    ∀ j, a.strip / 2 ≤ selectionr a j ∧
      selectionr a (j + 1) = selectionr a j - selectiond a j - 3 * selectionσ a j ∧
      selectiond a j ≤ a.strip / 4 ∧ selectiond a j ≤ 1 / 4 ∧
      selectionCutoffError n (selectionT a j) (selectiond a j) ≤
        selectionVarpi n a.μ a.τ / 8 := by
  obtain ⟨hv0, hv1⟩ := selectionVarpi_pos_le_one n a.μ hτ
  set v := selectionVarpi n a.μ a.τ with hvdef
  have hα0 : 0 < v / 8 := by positivity
  have hα1 : v / 8 ≤ 1 := by linarith
  have hpi := Real.pi_gt_three
  have hT0 : 0 < a.T₀ := by linarith
  have hπT0 : 0 < π * a.T₀ := by positivity
  set A0 := Real.log (16 * selectionCN n / v) with hA0
  have hlogA : ∀ j : ℕ, Real.log (2 * p11C n / (v / 8)) ≤ A0 + 0 * (j : ℝ) := fun j => by
    have h : 16 * selectionCN n / v = 2 * p11C n / (v / 8) := by
      rw [selectionCN_eq_p11C]
      field_simp
      ring
    rw [hA0, h]
    simp
  have hLS := loss_sum hn (theta := 2) (T0 := a.T₀) (a := A0) (b := 0)
    (by norm_num) hT ?_ le_rfl (fun _ => v / 8) (fun _ => ⟨hα0, hα1⟩) hlogA
  swap
  · -- `0 ≤ A0`
    rw [hA0]
    apply Real.log_nonneg
    have hc : 1 ≤ p11C n := p11C_ge_one hn
    rw [← selectionCN_eq_p11C] at hc
    rw [le_div_iff₀ hv0]
    nlinarith
  obtain ⟨hsum, -, hbound⟩ := hLS
  have hdeq : selectiond a = fun j => p11Loss n (a.T₀ * 2 ^ j) (v / 8) :=
    funext fun j => selectiond_eq_p11Loss a j
  have hsumd : Summable (selectiond a) := by rw [hdeq]; exact hsum
  have hdpos : ∀ j, 0 ≤ selectiond a j := fun j => by
    rw [selectiond_eq_p11Loss]
    exact (loss_choice hn hα0 hα1 (by
      have := one_le_pow₀ (n := j) (show (1 : ℝ) ≤ 2 by norm_num)
      nlinarith)).1.le
  -- sum of the losses
  have hsumle : (∑' j, selectiond a j) ≤ a.strip / 4 := by
    rw [hdeq]
    refine hbound.trans ?_
    have hy := n_log_le hn hs (X := 2 * (π * a.T₀)) (by positivity)
    rw [Real.log_mul (by norm_num) hπT0.ne'] at hy
    have hB : A0 + n * Real.log (32 * n / a.strip) ≤ a.strip * (π * a.T₀) / 16 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hT'
      nlinarith
    rw [div_le_iff₀ hπT0]
    nlinarith
  have hσs : Summable (fun j => 3 * selectionσ a j) := by
    have : Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact (this.mul_left (a.strip / 24)).mul_left 3 |>.congr fun j => by
      simp only [selectionσ]
  have hσsum : (∑' j, 3 * selectionσ a j) = a.strip / 4 := by
    have e : (fun j => 3 * selectionσ a j) = fun j : ℕ => 3 * (a.strip / 24) * (2 : ℝ)⁻¹ ^ j :=
      funext fun j => by simp only [selectionσ]; ring
    rw [e, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  have hσ0 : ∀ j, 0 ≤ 3 * selectionσ a j := fun j => by
    simp only [selectionσ]; positivity
  have hdsum : ∀ j, selectiond a j ≤ a.strip / 4 := fun j =>
    (hsumd.le_tsum j fun i _ => hdpos i).trans hsumle
  have hpart : ∀ j, ∑ i ∈ Finset.range j, (selectiond a i + 3 * selectionσ a i) ≤
      a.strip / 2 := fun j => by
    have hs2 : Summable (fun i => selectiond a i + 3 * selectionσ a i) := hsumd.add hσs
    refine (hs2.sum_le_tsum _ fun i _ => add_nonneg (hdpos i) (hσ0 i)).trans ?_
    rw [hsumd.tsum_add hσs, hσsum]
    linarith
  refine ⟨hsumd, hsumle, hσsum, fun j => ⟨?_, ?_, hdsum j, ?_, ?_⟩⟩
  · have := hpart j
    simp only [selectionr]
    linarith
  · simp only [selectionr, Finset.sum_range_succ]
    ring
  · linarith [hdsum j]
  · rw [selectionCutoffError_eq_p11Error, selectiond_eq_p11Loss]
    have hge : (1 : ℝ) ≤ a.T₀ * 2 ^ j := by
      have := one_le_pow₀ (n := j) (show (1 : ℝ) ≤ 2 by norm_num)
      nlinarith
    have hd1 : p11Loss n (a.T₀ * 2 ^ j) (v / 8) ≤ 1 := by
      rw [← selectiond_eq_p11Loss]
      linarith [hdsum j]
    exact (loss_choice hn hα0 hα1 hge).2.1 hd1

end KAM.Planetary
