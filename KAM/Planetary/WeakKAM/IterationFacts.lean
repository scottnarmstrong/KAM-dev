/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationBridge

/-! # P11B iteration: stage-wise scalar facts

For an admissible schedule `a` (a `WeakBudgetCtx`), the scalar inequalities of one inductive
step: `C1` (strip budget), `C2` (divisor smallness), `C3` (flow smallness) and the remainder
recursion `ε_ν (2q² + 2E_ν + Q_ν) ≤ ε_{ν+1}`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- The schedule with the selection constants of `d` and free `s₀`, `ε₀`. -/
def selectionSchedGen (d : SelectionData n) (s₀ ε₀ : ℝ) : SelectionSchedule n :=
  ⟨d.μ, d.τ, selectionGamma d, d.strip, selectionT₀ d, selectiont₀ d, s₀, ε₀⟩

/-- Standing facts of the iteration: the budget context and the `γ` of the data. -/
structure IterCtx (d : SelectionData n) (a : SelectionSchedule n) : Prop where
  budget : WeakBudgetCtx d a
  hγ : a.γ = selectionGamma d

section Stage
variable {d : SelectionData n} {a : SelectionSchedule n} (c : WeakBudgetCtx d a)
include c

theorem iter_strip (j : ℕ) :
    a.strip / 2 ≤ selectionr a j ∧
      selectionr a (j + 1) = selectionr a j - selectiond a j - 3 * selectionσ a j ∧
      selectiond a j ≤ a.strip / 4 ∧ selectiond a j ≤ 1 / 4 ∧
      selectionCutoffError n (selectionT a j) (selectiond a j) ≤
        selectionVarpi n a.μ a.τ / 8 := by
  have h := c.hyp
  exact (strip_budget a h.hn h.hμ h.hτ h.hstrip h.hstrip1 h.hT h.hloss).2.2.2 j

theorem iter_r_pos (j : ℕ) : 0 < selectionr a j := by
  have := (iter_strip c j).1
  have := c.hyp.hstrip
  linarith

omit c in
theorem iter_s_succ (j : ℕ) :
    selections a (j + 1) = selectionQ n a.μ a.τ * selections a j := by
  unfold selections
  ring

omit c in
theorem iter_eps_succ (j : ℕ) :
    selectionε a (j + 1) = selectionVarpi n a.μ a.τ * selectionε a j := by
  unfold selectionε
  ring

theorem iter_t_anti : Antitone (selectiont a) := by
  refine antitone_nat_of_succ_le fun j => ?_
  have h := c.hyp
  have := schedule_props a h.hn h.hμ h.hτ h.hγ h.hT h.ht h.hs h.he h.hstrip h.hC
    (by have := h.inc; have := h.col; have := h.hC; have := h.ht; nlinarith) h.inc h.col j 0
  exact this.2.2.1.trans (by linarith [wbud_t_pos c j])

theorem iter_E_nonneg (j : ℕ) : 0 ≤ selectionCutoffError n (selectionT a j) (selectiond a j) :=
  (wbud_E_bounds c.hyp j).1

theorem iter_varpi_pos : 0 < selectionVarpi n a.μ a.τ :=
  (selectionVarpi_pos_le_one n a.μ c.hyp.hτ).1

theorem iter_q_le : selectionQ n a.μ a.τ ≤ 1 / 2 := by
  have := (wbud_ratios c).2.1
  linarith

theorem iter_Qactual_le (j : ℕ) : selectionQactual a j ≤ selectionVarpi n a.μ a.τ / 2 := by
  have h := c.hyp
  have hQ := (wbud_stage h j).2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, hg, -, -⟩ := wbud_ratios c
  have hQ0 := wbud_Q₀_nonneg c
  have hg1 : selectionG n a.μ a.τ 0 ^ j ≤ 1 := pow_le_one₀ (wbud_ratios c).2.2.1.le (by linarith)
  have := c.adm.quadratic
  nlinarith

/-- `C3`: the flow smallness, in the form needed by `P11Step`. -/
theorem iter_flow_small (j : ℕ) :
    4 * (n + 1) * p11Lambda n (selectionσ a j) *
        (1 + p11Error n (selectionT a j) (selectiond a j)) * selectionε a j ≤
      Real.pi * selectionD a j * selections a j * selectionσ a j := by
  have h := c.hyp
  have hQ := iter_Qactual_le c j
  have hv1 := (selectionVarpi_pos_le_one n a.μ h.hτ).2
  have hσ := wbud_σ_pos h j
  have hD := wbud_D_pos h j
  have hs := wbud_s_pos h j
  have hε := wbud_ε_pos h j
  have hP : 0 < Real.pi * selectionD a j * selections a j * selectionσ a j := by positivity
  have hΛ := selectionΛ_nonneg n hσ
  have hQe : selectionQactual a j * (Real.pi * selectionD a j * selections a j *
      selectionσ a j) = selectionCQ n * selectionΛ n (selectionσ a j) * selectionε a j := by
    unfold selectionQactual
    field_simp
  have hE := (wbud_E_bounds h j).2
  rw [selectionCutoffError_eq_p11Error] at hE
  have hE0 : 0 ≤ p11Error n (selectionT a j) (selectiond a j) := by
    rw [← selectionCutoffError_eq_p11Error]
    exact iter_E_nonneg c j
  rw [← selectionΛ_eq_p11Lambda]
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
  have hCQ : 5 * ((n : ℝ) + 1) ≤ selectionCQ n := by unfold selectionCQ; nlinarith
  have h1 : selectionCQ n * selectionΛ n (selectionσ a j) * selectionε a j ≤
      Real.pi * selectionD a j * selections a j * selectionσ a j := by
    rw [← hQe]
    nlinarith
  have hΛε : 0 ≤ selectionΛ n (selectionσ a j) * selectionε a j := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show 4 * ((n : ℝ) + 1) *
    (1 + p11Error n (selectionT a j) (selectiond a j)) ≤ selectionCQ n by
      nlinarith [hE0]) hΛε]

/-- The remainder recursion `ε_ν (2 q² + 2 E_ν + Q_ν) ≤ ε_{ν+1}`. -/
theorem iter_rem_le (j : ℕ) :
    selectionε a j * (2 * selectionQ n a.μ a.τ ^ 2 +
        2 * p11Error n (selectionT a j) (selectiond a j)) +
      selectionCQ n * p11Lambda n (selectionσ a j) * selectionε a j ^ 2 /
        (Real.pi * selectionD a j * selections a j * selectionσ a j) ≤ selectionε a (j + 1) := by
  have h := c.hyp
  have hσ := wbud_σ_pos h j
  have hD := wbud_D_pos h j
  have hs := wbud_s_pos h j
  have hε := wbud_ε_pos h j
  have hv := iter_varpi_pos c
  have hq2 := (schedule_ratios h.hn h.hμ h.hτ).2.2.1
  have hE := (iter_strip c j).2.2.2.2
  rw [selectionCutoffError_eq_p11Error] at hE
  have hQ := iter_Qactual_le c j
  have e : selectionCQ n * p11Lambda n (selectionσ a j) * selectionε a j ^ 2 /
      (Real.pi * selectionD a j * selections a j * selectionσ a j) =
      selectionε a j * selectionQactual a j := by
    unfold selectionQactual
    rw [← selectionΛ_eq_p11Lambda]
    field_simp
  rw [e, iter_eps_succ]
  nlinarith [mul_le_mul_of_nonneg_left hQ hε.le, mul_le_mul_of_nonneg_left hE hε.le]

end Stage

/-- The scalar premises of one canonical step, at stage `ν` of the schedule `a`. -/
structure StepFacts (a : SelectionSchedule n) (C₁ : ℝ) (ν : ℕ) : Prop where
  n_pos : 1 ≤ n
  t_pos : 0 < selectiont a (ν + 1)
  s_pos : 0 < selections a ν
  T_pos : 0 < selectionT a ν
  d_pos : 0 < selectiond a ν
  σ_pos : 0 < selectionσ a ν
  radius : 0 < selectionr a ν - selectiond a ν - selectionσ a ν - 2 * selectionσ a ν
  q_pos : 0 < selectionQ n a.μ a.τ
  q_le : selectionQ n a.μ a.τ ≤ 1 / 2
  D_pos : 0 < selectionD a ν
  L_nonneg : 0 ≤ 2 * C₁
  eps_nonneg : 0 ≤ selectionε a ν
  cutoff_error : p11Error n (selectionT a ν) (selectiond a ν) ≤ 1
  divisor_small : selectiont a (ν + 1) * selectionT a ν * (2 * C₁) ≤ selectionD a ν / 2
  flow_small : 4 * (n + 1) * p11Lambda n (selectionσ a ν) *
      (1 + p11Error n (selectionT a ν) (selectiond a ν)) * selectionε a ν ≤
    Real.pi * selectionD a ν * selections a ν * selectionσ a ν

/-- The canonical-step parameters at stage `ν`: `E = K_{ν+1}`, `t = t_{ν+1}`, `r = r_ν`,
`s = s_ν`, `T = T_ν`, `d = d_ν`, `δ = σ = σ_ν`, `q = Q`, `D = D_ν`, `L = 2 C₁`, `ε = ε_ν`. -/
def stageStep (a : SelectionSchedule n) (C₁ : ℝ) (ν : ℕ) (K : Set (SelectionR n))
    (hf : StepFacts a C₁ ν) : P11Step n where
  E := K
  t := selectiont a (ν + 1)
  r := selectionr a ν
  s := selections a ν
  T := selectionT a ν
  d := selectiond a ν
  delta := selectionσ a ν
  sigma := selectionσ a ν
  q := selectionQ n a.μ a.τ
  D := selectionD a ν
  L := 2 * C₁
  eps := selectionε a ν
  n_pos := hf.n_pos
  t_pos := hf.t_pos
  s_pos := hf.s_pos
  T_pos := hf.T_pos
  d_pos := hf.d_pos
  delta_pos := hf.σ_pos
  sigma_pos := hf.σ_pos
  radius := hf.radius
  q_pos := hf.q_pos
  q_le := hf.q_le
  D_pos := hf.D_pos
  L_nonneg := hf.L_nonneg
  eps_nonneg := hf.eps_nonneg
  cutoff_error := hf.cutoff_error
  divisor_small := hf.divisor_small
  flow_small := hf.flow_small

section Stage
variable {d : SelectionData n} {a : SelectionSchedule n} (c : WeakBudgetCtx d a)
include c

theorem stepFacts_of_ctx (ν : ℕ) : StepFacts a d.C₁ ν := by
  have h := c.hyp
  have hr := iter_strip c ν
  have hr1 := iter_strip c (ν + 1)
  have hs := wbud_s_pos h ν
  have hσ := wbud_σ_pos h ν
  refine ⟨h.hn, wbud_t_pos c (ν + 1), hs, wbud_T_pos h ν, wbud_d_pos h ν, hσ, ?_,
    (wbud_ratios c).1, iter_q_le c, wbud_D_pos h ν, by linarith [h.hC], wbud_ε_pos h ν |>.le,
    ?_, ?_, iter_flow_small c ν⟩
  · have := hr.2.1
    have := hr1.1
    have := h.hstrip
    rw [hr.2.1] at *
    linarith
  · have h1 := (wbud_E_bounds h ν).2
    rw [selectionCutoffError_eq_p11Error] at h1
    linarith
  · have := schedule_props a h.hn h.hμ h.hτ h.hγ h.hT h.ht h.hs h.he h.hstrip h.hC
      (by have := h.inc; have := h.col; have := h.hC; have := h.ht; nlinarith) h.inc h.col ν 0
    exact this.2.2.2.2.2.2.2.2.2.2.2.2

theorem iter_tail (m : ℕ) :
    Summable (fun i => selectionell a (i + m)) ∧
      selectionTail a m ≤ a.γ * selectionT a m ^ (-a.τ - 1) := by
  have h := c.hyp
  have := schedule_props a h.hn h.hμ h.hτ h.hγ h.hT h.ht h.hs h.he h.hstrip h.hC
    (by have := h.inc; have := h.col; have := h.hC; have := h.ht; nlinarith) h.inc h.col 0 m
  exact ⟨this.2.2.2.2.2.1, this.2.2.2.2.2.2.2.1⟩

theorem iter_t_half (j : ℕ) : selectiont a (j + 1) ≤ selectiont a j / 2 := by
  have h := c.hyp
  exact (schedule_props a h.hn h.hμ h.hτ h.hγ h.hT h.ht h.hs h.he h.hstrip h.hC
    (by have := h.inc; have := h.col; have := h.hC; have := h.ht; nlinarith) h.inc h.col j 0).2.2.1

theorem iter_sum_le (ν : ℕ) :
    (∑ i ∈ Finset.range ν, 4 * selectionε a i / (selections a i * selectiont a i)) ≤ d.C₁ := by
  have h := c.hyp
  exact (schedule_props a h.hn h.hμ h.hτ h.hγ h.hT h.ht h.hs h.he h.hstrip h.hC
    (by have := h.inc; have := h.col; have := h.hC; have := h.ht; nlinarith) h.inc h.col
    ν 0).2.2.2.2.2.2.2.2.2.1

theorem iter_rr (ν : ℕ) :
    selectionr a ν - selectiond a ν - selectionσ a ν - 2 * selectionσ a ν =
      selectionr a (ν + 1) := by
  rw [(iter_strip c ν).2.1]
  ring

theorem iter_E_le_one (ν : ℕ) : 1 + p11Error n (selectionT a ν) (selectiond a ν) ≤ 2 := by
  have h1 := (wbud_E_bounds c.hyp ν).2
  rw [selectionCutoffError_eq_p11Error] at h1
  linarith

theorem iter_E_nonneg' (ν : ℕ) : 0 ≤ p11Error n (selectionT a ν) (selectiond a ν) := by
  rw [← selectionCutoffError_eq_p11Error]
  exact iter_E_nonneg c ν

end Stage

end KAM.Planetary

end
