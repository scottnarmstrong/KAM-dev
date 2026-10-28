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

/-- `T_j^x = T₀^x (2^x)^j` for positive `T₀`. -/
theorem selectionT_rpow (a : SelectionSchedule n) (hT : 0 < a.T₀) (x : ℝ) (j : ℕ) :
    selectionT a j ^ x = a.T₀ ^ x * ((2 : ℝ) ^ x) ^ j := by
  unfold selectionT
  have h : ((2 : ℝ) ^ j) ^ x = ((2 : ℝ) ^ x) ^ j := by
    rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [Real.mul_rpow hT.le (by positivity), h]

/-- `t_j = t₀ ((2^{τ+1})⁻¹)^j`. -/
theorem selectiont_eq (a : SelectionSchedule n) (j : ℕ) :
    selectiont a j = a.t₀ * (((2 : ℝ) ^ (a.τ + 1))⁻¹) ^ j := by
  unfold selectiont
  rw [← Real.rpow_neg (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-- `ε_j / s_j = λ₀ ϱ^j`. -/
theorem selection_eps_div_s (a : SelectionSchedule n) (hn : 1 ≤ n) (hμ : 1 ≤ a.μ)
    (hτ : 0 ≤ a.τ) (hs : 0 < a.s₀) (j : ℕ) :
    selectionε a j / selections a j =
      (a.ε₀ / a.s₀) * selectionVarrho n a.μ a.τ ^ j := by
  have hq := (schedule_ratios hn hμ hτ).1
  simp only [selectionε, selections, selectionVarrho]
  rw [div_pow]
  field_simp

/-- A geometric series with ratio at most `1/2` has sum at most `2`. -/
theorem geom_tsum_le_two {g : ℝ} (h0 : 0 ≤ g) (h1 : g ≤ 1 / 2) :
    Summable (fun i : ℕ => g ^ i) ∧ ∑' i : ℕ, g ^ i ≤ 2 := by
  refine ⟨summable_geometric_of_lt_one h0 (by linarith), ?_⟩
  rw [tsum_geometric_of_lt_one h0 (by linarith), inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- Partial geometric sums with ratio at most `1/2` are at most `2`. -/
theorem geom_sum_le_two {g : ℝ} (h0 : 0 ≤ g) (h1 : g ≤ 1 / 2) (j : ℕ) :
    ∑ i ∈ Finset.range j, g ^ i ≤ 2 :=
  ((geom_tsum_le_two h0 h1).1.sum_le_tsum _ fun i _ => pow_nonneg h0 i).trans
    (geom_tsum_le_two h0 h1).2

theorem schedule_props (a : SelectionSchedule n) (hn : 1 ≤ n) (hμ : 1 ≤ a.μ)
    (hτ : 0 ≤ a.τ) (hγ : 0 < a.γ) (hT : 1 ≤ a.T₀)
    (ht : 0 < a.t₀) (hs : 0 < a.s₀) (he : 0 < a.ε₀) (hstrip : 0 < a.strip)
    (hC : 1 ≤ C₁) (h1 : 4 * (a.ε₀ / a.s₀) ≤ a.γ * a.T₀ ^ (-a.τ - 1))
    (h2 : 8 * (a.ε₀ / a.s₀) ≤ C₁ * a.t₀)
    (h3 : 4 * C₁ * a.t₀ ≤ a.γ * a.T₀ ^ (-a.τ - 1)) :
    ∀ j m, selectionT a (j + 1) = 2 * selectionT a j ∧
      selectiont a (j + 1) = (2 : ℝ) ^ (-(a.τ + 1)) * selectiont a j ∧
      selectiont a (j + 1) ≤ selectiont a j / 2 ∧
      selectiont a j ≤ a.γ * selectionT a j ^ (-a.τ - 1) / (4 * C₁) ∧
      selectionε a j / selections a j =
        (a.ε₀ / a.s₀) * selectionVarrho n a.μ a.τ ^ j ∧
      Summable (fun i => selectionell a (i + m)) ∧
      selectionTail a m ≤ 4 * (a.ε₀ / a.s₀) * selectionVarrho n a.μ a.τ ^ m ∧
      selectionTail a m ≤ a.γ * selectionT a m ^ (-a.τ - 1) ∧
      (∑ i ∈ Finset.range j, 4 * selectionε a i / (selections a i * selectiont a i))
        ≤ 8 * (a.ε₀ / a.s₀) / a.t₀ ∧
      (∑ i ∈ Finset.range j, 4 * selectionε a i / (selections a i * selectiont a i))
        ≤ C₁ ∧
      (∑ i ∈ Finset.range j, selectionell a i / selectiont a i ^ a.μ)
        ≤ 4 * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ ∧
      selectionQsharp a j = selectionQ₀ a * selectionG n a.μ a.τ 0 ^ j ∧
      selectiont a (j + 1) * selectionT a j * (2 * C₁) ≤ selectionD a j / 2 := by
  intro j m
  have hT0 : 0 < a.T₀ := by linarith
  have hC0 : 0 < C₁ := by linarith
  obtain ⟨hq, -, -, hG, hρ⟩ := schedule_ratios hn hμ hτ
  obtain ⟨hv0, -⟩ := selectionVarpi_pos_le_one n a.μ hτ
  have hρ0 : 0 < selectionVarrho n a.μ a.τ := by
    unfold selectionVarrho; positivity
  set ρ := selectionVarrho n a.μ a.τ with hρdef
  set w : ℝ := (2 : ℝ) ^ (a.τ + 1) with hw
  have hw2 : 2 ≤ w := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1 : ℝ) ≤ a.τ + 1 by linarith)
    simpa [hw] using this
  have hw0 : 0 < w := by linarith
  have hwr : (2 : ℝ) ^ (-(a.τ + 1)) = w⁻¹ := Real.rpow_neg (by norm_num) _
  rw [hwr] at hρ
  have hρw : ρ * w ≤ 1 / 32 := by
    have := mul_le_mul_of_nonneg_right hρ hw0.le
    have e : w⁻¹ / 32 * w = 1 / 32 := by field_simp
    linarith
  have hρr : ρ ≤ w⁻¹ := by
    have : 0 < w⁻¹ := inv_pos.2 hw0
    linarith
  have hρ2 : ρ ≤ 1 / 2 := by nlinarith
  have hr0 : 0 ≤ w⁻¹ := (inv_pos.2 hw0).le
  have hlam : 0 < a.ε₀ / a.s₀ := by positivity
  have hs_pos : ∀ k, 0 < selections a k := fun k => by
    unfold selections; positivity
  have ht_pos : ∀ k, 0 < selectiont a k := fun k => by
    rw [selectiont_eq]; positivity
  have hE5 := selection_eps_div_s a hn hμ hτ hs
  have hell : ∀ k, selectionell a k = 2 * ((a.ε₀ / a.s₀) * ρ ^ k) := fun k => by
    simp only [selectionell]
    rw [mul_div_assoc, hE5]
  have hTneg : ∀ k, selectionT a k ^ (-a.τ - 1) = a.T₀ ^ (-a.τ - 1) * (w⁻¹) ^ k := fun k => by
    rw [selectionT_rpow a hT0, show -a.τ - 1 = -(a.τ + 1) by ring, hwr]
  have hG1 : selectionG n a.μ a.τ 1 = ρ * w := by
    simp [selectionG, hρdef, hw]
  have hG2 : selectionG n a.μ a.τ 2 = ρ * w ^ a.μ := by
    simp only [selectionG, hρdef, hw]
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    rfl
  have hg2 : ρ * w ≤ 1 / 2 := by linarith
  have hg3 : ρ * w ^ a.μ ≤ 1 / 2 := by
    have := hG 2
    rw [hG2] at this
    norm_num at this ⊢
    linarith
  have hsum2 := geom_tsum_le_two hρ0.le hρ2
  have h11 : (∑ i ∈ Finset.range j, selectionell a i / selectiont a i ^ a.μ)
      ≤ 4 * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ := by
    have hterm : ∀ i, selectionell a i / selectiont a i ^ a.μ =
        (2 * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ) * (ρ * w ^ a.μ) ^ i := fun i => by
      have e1 : ((w⁻¹) ^ i) ^ a.μ * (w ^ a.μ) ^ i = 1 := by
        rw [← pow_mul, ← pow_mul, mul_comm a.μ i, ← mul_pow, inv_mul_cancel₀ hw0.ne', one_pow]
      have hY : (w ^ a.μ) ^ i = (((w⁻¹) ^ i) ^ a.μ)⁻¹ := eq_inv_of_mul_eq_one_right e1
      have hX : ((w⁻¹) ^ i) ^ a.μ ≠ 0 := by positivity
      rw [hell, selectiont_eq, ← hw, mul_pow, mul_pow, hY]
      field_simp
    simp only [hterm]
    rw [← Finset.mul_sum]
    have := geom_sum_le_two (mul_nonneg hρ0.le (pow_nonneg hw0.le a.μ)) hg3 j
    have h0 : 0 ≤ 2 * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ := by positivity
    calc _ ≤ 2 * (a.ε₀ / a.s₀) / a.t₀ ^ a.μ * 2 := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have ht3 : selectiont a (j + 1) ≤ selectiont a j / 2 := by
    rw [selectiont_eq, selectiont_eq, pow_succ]
    have : 0 ≤ a.t₀ * (w⁻¹) ^ j := by positivity
    have hh : w⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ hw0 (by norm_num)]; linarith
    nlinarith
  have ht4 : selectiont a j * (4 * C₁) ≤ a.γ * selectionT a j ^ (-a.τ - 1) := by
    rw [selectiont_eq, hTneg]
    have := mul_le_mul_of_nonneg_right h3 (pow_nonneg hr0 j)
    nlinarith
  have h9 : (∑ i ∈ Finset.range j, 4 * selectionε a i / (selections a i * selectiont a i))
      ≤ 8 * (a.ε₀ / a.s₀) / a.t₀ := by
    have hterm : ∀ i, 4 * selectionε a i / (selections a i * selectiont a i) =
        (4 * (a.ε₀ / a.s₀) / a.t₀) * (ρ * w) ^ i := fun i => by
      have h := hE5 i
      have hsi := hs_pos i
      have hti := ht_pos i
      rw [show 4 * selectionε a i / (selections a i * selectiont a i) =
        4 * (selectionε a i / selections a i) / selectiont a i by field_simp, h, selectiont_eq,
        ← hw, inv_pow, mul_pow]
      field_simp
      try rfl
    simp only [hterm]
    rw [← Finset.mul_sum]
    have := geom_sum_le_two (mul_nonneg hρ0.le hw0.le) hg2 j
    have h0 : 0 ≤ 4 * (a.ε₀ / a.s₀) / a.t₀ := by positivity
    calc _ ≤ 4 * (a.ε₀ / a.s₀) / a.t₀ * 2 := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_, hE5 j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [selectionT, pow_succ]; ring
  · rw [selectiont_eq, selectiont_eq, hwr, pow_succ]; ring
  · exact ht3
  · rw [le_div_iff₀ (by positivity)]
    exact ht4
  · have e : (fun i => selectionell a (i + m)) =
        fun i => (2 * ((a.ε₀ / a.s₀) * ρ ^ m)) * ρ ^ i :=
      funext fun i => by rw [hell, pow_add]; ring
    rw [e]
    exact hsum2.1.mul_left _
  · have e : (fun i => selectionell a (i + m)) =
        fun i => (2 * ((a.ε₀ / a.s₀) * ρ ^ m)) * ρ ^ i :=
      funext fun i => by rw [hell, pow_add]; ring
    unfold selectionTail
    rw [e, tsum_mul_left]
    have := mul_le_mul_of_nonneg_left hsum2.2 (show 0 ≤ 2 * ((a.ε₀ / a.s₀) * ρ ^ m) by positivity)
    nlinarith
  · have e : (fun i => selectionell a (i + m)) =
        fun i => (2 * ((a.ε₀ / a.s₀) * ρ ^ m)) * ρ ^ i :=
      funext fun i => by rw [hell, pow_add]; ring
    unfold selectionTail
    rw [e, tsum_mul_left, hTneg]
    have h4 := mul_le_mul_of_nonneg_left hsum2.2
      (show 0 ≤ 2 * ((a.ε₀ / a.s₀) * ρ ^ m) by positivity)
    have h5 : ρ ^ m ≤ (w⁻¹) ^ m := pow_le_pow_left₀ hρ0.le hρr m
    have h6 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ0.le m)
    have h7 := mul_le_mul_of_nonneg_left h5 (show 0 ≤ a.γ * a.T₀ ^ (-a.τ - 1) by positivity)
    nlinarith
  · exact h9
  · exact h9.trans (by rw [div_le_iff₀ ht]; linarith)
  · exact h11
  · have hD : selectionD a j = a.γ * ((a.T₀ ^ a.τ)⁻¹ * (((2 : ℝ) ^ a.τ)⁻¹) ^ j) := by
      simp only [selectionD, selectionT_rpow a hT0, Real.rpow_neg hT0.le,
        Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num)]
    have hG0 : selectionG n a.μ a.τ 0 = ρ * (2 : ℝ) ^ a.τ * 2 ^ (n + 1) := by
      simp [selectionG, hρdef]
    have hε : selectionε a j = ((a.ε₀ / a.s₀) * ρ ^ j) * selections a j := by
      rw [← hE5 j]; exact (div_mul_cancel₀ _ (hs_pos j).ne').symm
    have hsne := (hs_pos j).ne'
    have hP : (0 : ℝ) < (2 : ℝ) ^ a.τ := by positivity
    have hTp : 0 < a.T₀ ^ a.τ := by positivity
    unfold selectionQsharp selectionQ₀
    rw [hε, hD, hG0]
    simp only [selectionσ, inv_pow, div_pow, mul_pow]
    field_simp
    ring
  · have hTp : 0 < selectionT a j := by unfold selectionT; positivity
    have hx : selectionT a j ^ (-a.τ - 1) * selectionT a j = selectionT a j ^ (-a.τ) := by
      rw [← Real.rpow_add_one hTp.ne', sub_add_cancel]
    have hD : selectionD a j = a.γ * selectionT a j ^ (-a.τ) := rfl
    have hT1 := mul_le_mul_of_nonneg_right ht4 hTp.le
    have hT2 : selectiont a (j + 1) * selectionT a j * (2 * C₁) ≤
        selectiont a j / 2 * selectionT a j * (2 * C₁) := by
      gcongr
    have hpos : 0 ≤ a.γ * selectionT a j ^ (-a.τ) := by positivity
    have hT3 : selectiont a j * (4 * C₁) * selectionT a j ≤ a.γ * selectionT a j ^ (-a.τ) :=
      hT1.trans_eq (by rw [mul_assoc, hx])
    rw [hD]
    linarith

end KAM.Planetary
