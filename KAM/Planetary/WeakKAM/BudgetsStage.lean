/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.Admissible

/-! # P11B weak-KAM scalar budgets: definitions and stagewise bounds

The exact scalar schedules `selectionA`, `selectionAlpha`, `selectionKappa`, `selectionMapBudget`,
`selectionRealBudget`, `selectionQactual` and the homological factor `selectionΛ`, together with
the stagewise estimates (E1) of `bpP:p11a:exported-sums`: `A_ν ≤ 2 σ_ν Q_ν / C_Q`,
`κ_ν ≤ Q_ν / 16`, `α_ν = κ_ν s_ν / 2`, `Λ_ℝ,ν ≤ (4π / C_Q) T₀ ς₀ Q_ν`, `Q_ν ≤ Q₀ g₁^ν`.
The estimates hold for every schedule satisfying `WeakBudgetHyp`, a bundle of the standing
positivity facts and the two collar inequalities; no iteration hypothesis is used.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- a, alpha, kappa, Lambda_R, m, Q are exact scalar schedules, not map suprema. -/
def selectionΛ (n : ℕ) (r : ℝ) : ℝ :=
  ((Real.exp (2 * π * r) + 1) / (Real.exp (2 * π * r) - 1)) ^ n - 1

def selectionA (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  selectionΛ n (selectionσ a j) *
    (1 + selectionCutoffError n (selectionT a j) (selectiond a j)) * selectionε a j /
      (π * selectionD a j * selections a j)
def selectionAlpha (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  (n + 1) * selections a j * selectionA a j / selectionσ a j
def selectionKappa (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  2 * (n + 1) * selectionA a j / selectionσ a j
def selectionMapBudget (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  2 * selectionKappa a j + selectionKappa a j * selections a j / selectionσ a j
def selectionRealBudget (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  2 * selectionT a j *
    (1 + selectionCutoffError n (selectionT a j) (selectiond a j)) * selectionε a j *
      selectionΛ n (selectionr a j - selectiond a j) / (selectionD a j * selections a j)

def selectionQactual (a : SelectionSchedule n) (j : ℕ) : ℝ :=
  selectionCQ n * selectionΛ n (selectionσ a j) * selectionε a j /
    (π * selectionD a j * selections a j * selectionσ a j)

theorem selectionΛ_one_le {r : ℝ} (hr : 0 < r) :
    1 ≤ (Real.exp (2 * π * r) + 1) / (Real.exp (2 * π * r) - 1) := by
  have h : 1 < Real.exp (2 * π * r) := Real.one_lt_exp_iff.2 (by positivity)
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem selectionΛ_nonneg (n : ℕ) {r : ℝ} (hr : 0 < r) : 0 ≤ selectionΛ n r := by
  unfold selectionΛ
  have := one_le_pow₀ (n := n) (selectionΛ_one_le hr)
  linarith

/-- `Λ` is decreasing in the radius. -/
theorem selectionΛ_anti (n : ℕ) {r₁ r₂ : ℝ} (h1 : 0 < r₁) (h : r₁ ≤ r₂) :
    selectionΛ n r₂ ≤ selectionΛ n r₁ := by
  unfold selectionΛ
  have h2 : 0 < r₂ := h1.trans_le h
  have e1 : 1 < Real.exp (2 * π * r₁) := Real.one_lt_exp_iff.2 (by positivity)
  have e12 : Real.exp (2 * π * r₁) ≤ Real.exp (2 * π * r₂) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  set E₁ := Real.exp (2 * π * r₁)
  set E₂ := Real.exp (2 * π * r₂)
  have hu : (E₂ + 1) / (E₂ - 1) ≤ (E₁ + 1) / (E₁ - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have := pow_le_pow_left₀ (zero_le_one.trans (selectionΛ_one_le h2)) hu n
  linarith

/-- `Λ_R ≤ (2/R)^n` for `0 < R ≤ 1`. -/
theorem selectionΛ_le_pow (n : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    selectionΛ n r ≤ (2 / r) ^ n := by
  unfold selectionΛ
  have hE : 1 + 2 * π * r ≤ Real.exp (2 * π * r) := by
    linarith [Real.add_one_le_exp (2 * π * r)]
  set E := Real.exp (2 * π * r)
  have hpi := Real.pi_gt_three
  have hu : (E + 1) / (E - 1) ≤ 2 / r := by
    rw [div_le_div_iff₀ (by nlinarith [mul_pos Real.pi_pos hr]) hr]
    have h1 := mul_le_mul_of_nonneg_right hE (show 0 ≤ 2 - r by linarith)
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hr.le) (sub_nonneg.2 hr1)]
  have := pow_le_pow_left₀ (zero_le_one.trans (selectionΛ_one_le hr)) hu n
  linarith

/-- Standing facts shared by the scalar budget estimates; `C` is the Hessian bound `C₁`. -/
structure WeakBudgetHyp (a : SelectionSchedule n) (C : ℝ) : Prop where
  hn : 1 ≤ n
  hμ : 1 ≤ a.μ
  hτ : 0 ≤ a.τ
  hγ : 0 < a.γ
  hT : 1 ≤ a.T₀
  ht : 0 < a.t₀
  hs : 0 < a.s₀
  he : 0 < a.ε₀
  hstrip : 0 < a.strip
  hstrip1 : a.strip ≤ 1
  hloss : 16 / (π * a.strip) *
    (Real.log (16 * selectionCN n / selectionVarpi n a.μ a.τ) +
      n * Real.log (32 * n / a.strip)) ≤ a.T₀
  hC : 1 ≤ C
  inc : 8 * (a.ε₀ / a.s₀) ≤ C * a.t₀
  col : 4 * C * a.t₀ ≤ a.γ * a.T₀ ^ (-a.τ - 1)

/-- The standing facts for an admissible schedule built from the data `d`. -/
theorem weakBudgetHyp_of_adm (d : SelectionData n) (a : SelectionSchedule n)
    (hadm : SelectionAdmissibility d a) (hμ : a.μ = d.μ) (hτ : a.τ = d.τ)
    (hγ : a.γ = selectionGamma d) (hstrip : a.strip = d.strip)
    (hs : 0 < a.s₀) (he : 0 < a.ε₀) : WeakBudgetHyp a d.C₁ := by
  refine ⟨d.n_pos, hμ ▸ d.μ_pos, hτ ▸ d.tau_nonneg, hγ ▸ selectionGamma_pos d, hadm.cutoff_ge,
    hadm.t_pos, hs, he, hstrip ▸ d.strip_pos, hstrip ▸ d.strip_le, ?_, d.hessian_normalized,
    hadm.increment, hadm.collar⟩
  have := hadm.cutoff_loss
  rw [← hstrip, ← hμ, ← hτ] at this
  exact this

section Stage
variable {a : SelectionSchedule n} {C : ℝ} (h : WeakBudgetHyp a C)
include h

theorem wbud_T_pos (j : ℕ) : 0 < selectionT a j := by
  have := h.hT
  unfold selectionT
  positivity

theorem wbud_σ_pos (j : ℕ) : 0 < selectionσ a j := by
  have := h.hstrip
  unfold selectionσ
  positivity

theorem wbud_σ_le_one (j : ℕ) : selectionσ a j ≤ 1 := by
  have h0 := h.hstrip1
  have : (2 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold selectionσ
  have hs := h.hstrip
  nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ a.strip / 24 by positivity)]

theorem wbud_D_pos (j : ℕ) : 0 < selectionD a j := by
  have := wbud_T_pos h j
  have := h.hγ
  unfold selectionD
  positivity

theorem wbud_s_pos (j : ℕ) : 0 < selections a j := by
  have := h.hs
  unfold selections
  have := (schedule_ratios h.hn h.hμ h.hτ).1
  positivity

theorem wbud_ε_pos (j : ℕ) : 0 < selectionε a j := by
  have := h.he
  unfold selectionε
  have := (selectionVarpi_pos_le_one n a.μ h.hτ).1
  positivity

theorem wbud_d_pos (j : ℕ) : 0 < selectiond a j := by
  obtain ⟨hv0, hv1⟩ := selectionVarpi_pos_le_one n a.μ h.hτ
  rw [selectiond_eq_p11Loss]
  refine (loss_choice h.hn (by positivity) (by linarith) ?_).1
  have := one_le_pow₀ (n := j) (show (1 : ℝ) ≤ 2 by norm_num)
  have := h.hT
  nlinarith

theorem wbud_E_bounds (j : ℕ) :
    0 ≤ selectionCutoffError n (selectionT a j) (selectiond a j) ∧
      selectionCutoffError n (selectionT a j) (selectiond a j) ≤ 1 / 8 := by
  obtain ⟨hv0, hv1⟩ := selectionVarpi_pos_le_one n a.μ h.hτ
  have hsb := (strip_budget a h.hn h.hμ h.hτ h.hstrip h.hstrip1 h.hT h.hloss).2.2.2 j
  have hCN := selectionCN_pos h.hn
  have hd := wbud_d_pos h j
  refine ⟨?_, hsb.2.2.2.2.trans (by linarith)⟩
  unfold selectionCutoffError
  positivity

/-- The `Q₀ g₁^ν` bound `Q_ν ≤ Q^♯_ν` and the other stagewise facts of (E1). -/
theorem wbud_stage (j : ℕ) :
    0 ≤ selectionQactual a j ∧
    0 ≤ selectionA a j ∧
      selectionA a j ≤ 2 * selectionσ a j * selectionQactual a j / selectionCQ n ∧
    0 ≤ selectionKappa a j ∧ selectionKappa a j ≤ selectionQactual a j / 16 ∧
    selectionAlpha a j = selectionKappa a j * selections a j / 2 ∧
    0 ≤ selectionRealBudget a j ∧
      selectionRealBudget a j ≤ 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) *
        selectionQactual a j ∧
    selectionQactual a j ≤ selectionQ₀ a * selectionG n a.μ a.τ 0 ^ j := by
  have hn := h.hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hσ := wbud_σ_pos h j
  have hT := wbud_T_pos h j
  have hD := wbud_D_pos h j
  have hs := wbud_s_pos h j
  have hε := wbud_ε_pos h j
  have hCQ : 162 ≤ selectionCQ n := by
    unfold selectionCQ
    nlinarith
  have hCQ0 : 0 < selectionCQ n := by linarith
  have hpi := Real.pi_pos
  have hΛ := selectionΛ_nonneg n hσ
  obtain ⟨hE0, hE1⟩ := wbud_E_bounds h j
  set E := selectionCutoffError n (selectionT a j) (selectiond a j) with hEdef
  have hQ0 : 0 ≤ selectionQactual a j := by
    unfold selectionQactual
    positivity
  have hAeq : selectionA a j =
      (1 + E) * (selectionσ a j * selectionQactual a j / selectionCQ n) := by
    rw [hEdef]
    unfold selectionA selectionQactual
    field_simp
  have hA0 : 0 ≤ selectionA a j := by
    rw [hAeq]
    positivity
  have hAle : selectionA a j ≤ 2 * selectionσ a j * selectionQactual a j / selectionCQ n := by
    rw [hAeq]
    have : 0 ≤ selectionσ a j * selectionQactual a j / selectionCQ n := by positivity
    calc (1 + E) * (selectionσ a j * selectionQactual a j / selectionCQ n)
        ≤ 2 * (selectionσ a j * selectionQactual a j / selectionCQ n) := by nlinarith
      _ = _ := by ring
  have hκ : selectionKappa a j =
      2 * (n + 1) * (1 + E) * selectionQactual a j / selectionCQ n := by
    unfold selectionKappa
    rw [hAeq]
    field_simp
  have hκ0 : 0 ≤ selectionKappa a j := by rw [hκ]; positivity
  have hκle : selectionKappa a j ≤ selectionQactual a j / 16 := by
    rw [hκ, div_le_iff₀ hCQ0]
    have hq : 64 * ((n : ℝ) + 1) ≤ selectionCQ n := by
      unfold selectionCQ
      nlinarith
    have h1 : 2 * ((n : ℝ) + 1) * (1 + E) ≤ 4 * ((n : ℝ) + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hQ0
    nlinarith
  have hα : selectionAlpha a j = selectionKappa a j * selections a j / 2 := by
    unfold selectionAlpha selectionKappa
    field_simp
  -- the real-flow budget
  have hsb := (strip_budget a hn h.hμ h.hτ h.hstrip h.hstrip1 h.hT h.hloss).2.2.2 j
  have hsb' := (strip_budget a hn h.hμ h.hτ h.hstrip h.hstrip1 h.hT h.hloss).2.2.2 (j)
  have hr : selectionσ a j ≤ selectionr a j - selectiond a j := by
    have := (strip_budget a hn h.hμ h.hτ h.hstrip h.hstrip1 h.hT h.hloss).2.2.2 (j + 1)
    have h2 := hsb.2.1
    have h3 := this.1
    have h4 : 0 < 3 * selectionσ a j := by positivity
    have h5 := h.hstrip
    have : a.strip / 2 ≤ selectionr a (j + 1) := h3
    rw [h2] at this
    linarith
  have hΛr := selectionΛ_anti n hσ hr
  have hΛr0 : 0 ≤ selectionΛ n (selectionr a j - selectiond a j) :=
    selectionΛ_nonneg n (hσ.trans_le hr)
  have hTσ : selectionT a j * selectionσ a j = a.T₀ * (a.strip / 24) := by
    unfold selectionT selectionσ
    rw [inv_pow]
    field_simp
  have hRB0 : 0 ≤ selectionRealBudget a j := by
    unfold selectionRealBudget
    positivity
  have hRBle : selectionRealBudget a j ≤ 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) *
      selectionQactual a j := by
    have hform : 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) * selectionQactual a j =
        4 * selectionT a j * selectionε a j * selectionΛ n (selectionσ a j) /
          (selectionD a j * selections a j) := by
      calc 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) * selectionQactual a j
          = 4 * π / selectionCQ n * (a.T₀ * (a.strip / 24)) * selectionQactual a j := by ring
        _ = 4 * π / selectionCQ n * (selectionT a j * selectionσ a j) *
              selectionQactual a j := by rw [hTσ]
        _ = _ := by
          unfold selectionQactual
          field_simp
    rw [hform]
    unfold selectionRealBudget
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hK : 0 ≤ 2 * selectionT a j * selectionε a j := by positivity
    have h1 : (1 + E) * selectionΛ n (selectionr a j - selectiond a j) ≤
        2 * selectionΛ n (selectionσ a j) := by nlinarith
    calc 2 * selectionT a j * (1 + E) * selectionε a j *
          selectionΛ n (selectionr a j - selectiond a j)
        = (2 * selectionT a j * selectionε a j) *
            ((1 + E) * selectionΛ n (selectionr a j - selectiond a j)) := by ring
      _ ≤ (2 * selectionT a j * selectionε a j) * (2 * selectionΛ n (selectionσ a j)) :=
          mul_le_mul_of_nonneg_left h1 hK
      _ = _ := by ring
  -- the `Q^♯` comparison
  have hrat := schedule_props a hn h.hμ h.hτ h.hγ h.hT h.ht h.hs h.he h.hstrip h.hC
    (by have := h.inc; have := h.col; have := h.hC; have := h.ht; nlinarith) h.inc h.col j 0
  have hQs := hrat.2.2.2.2.2.2.2.2.2.2.2.1
  have hQle : selectionQactual a j ≤ selectionQsharp a j := by
    unfold selectionQactual selectionQsharp
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have := selectionΛ_le_pow n hσ (wbud_σ_le_one h j)
    have h1 := mul_le_mul_of_nonneg_left this hCQ0.le
    exact mul_le_mul_of_nonneg_right h1 hε.le
  exact ⟨hQ0, hA0, hAle, hκ0, hκle, hα, hRB0, hRBle, hQs ▸ hQle⟩

end Stage

end KAM.Planetary
