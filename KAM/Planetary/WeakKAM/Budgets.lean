/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.BudgetsStage

/-! # P11B weak-KAM summable budgets

`exported_sums` (`bpP:p11a:exported-sums`, items (E1)--(E3); (E4) is the returned map estimate) and
`param_lip_sum` (`bpP:p11a:param-lip-sum`). Both are derived from one general estimate for every
admissible schedule built from the data `d` (`WeakBudgetCtx`): every budget is dominated by a
geometric series with ratio `1/32`, with explicit constants controlled by `Q₀ Ξ ≤ 2⁻¹⁰`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- A nonnegative sequence dominated by `c x^j`, `x ≤ 1/32`, has a summable shifted tail. -/
theorem wbud_tsum_le {f : ℕ → ℝ} {c x : ℝ} (hf0 : ∀ j, 0 ≤ f j) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 32) (hf : ∀ j, f j ≤ c * x ^ j) (ν : ℕ) :
    Summable (fun j => f (j + ν)) ∧ ∑' j, f (j + ν) ≤ 32 / 31 * (c * x ^ ν) := by
  have hc : 0 ≤ c := by simpa using (hf0 0).trans (hf 0)
  have hg : Summable (fun j : ℕ => (c * x ^ ν) * x ^ j) :=
    (summable_geometric_of_lt_one hx0 (by linarith)).mul_left _
  have hle : ∀ j, f (j + ν) ≤ (c * x ^ ν) * x ^ j := fun j =>
    (hf (j + ν)).trans_eq (by ring)
  have hs : Summable (fun j => f (j + ν)) :=
    Summable.of_nonneg_of_le (fun j => hf0 _) hle hg
  refine ⟨hs, ?_⟩
  have hinv : (1 - x)⁻¹ ≤ 32 / 31 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ∑' j, f (j + ν) ≤ ∑' j : ℕ, (c * x ^ ν) * x ^ j := hs.tsum_le_tsum hle hg
    _ = (c * x ^ ν) * (1 - x)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hx0 (by linarith)]
    _ ≤ (c * x ^ ν) * (32 / 31) := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

theorem wbud_tsum_le_zero {f : ℕ → ℝ} {c : ℝ} (hf0 : ∀ j, 0 ≤ f j)
    (hf : ∀ j, f j ≤ c * (1 / 32 : ℝ) ^ j) :
    Summable f ∧ ∑' j, f j ≤ 32 / 31 * c := by
  simpa using wbud_tsum_le hf0 (by norm_num) le_rfl hf 0

/-- The data under which the scalar budgets of an admissible schedule are controlled. -/
structure WeakBudgetCtx (d : SelectionData n) (a : SelectionSchedule n) : Prop where
  adm : SelectionAdmissibility d a
  hyp : WeakBudgetHyp a d.C₁
  hμ : a.μ = d.μ
  hτ : a.τ = d.τ
  hstrip : a.strip = d.strip
  ht0 : a.t₀ = selectiont₀ d
  hT0 : a.T₀ = selectionT₀ d

theorem weakBudgetCtx_of (d : SelectionData n) (a : SelectionSchedule n)
    (hadm : SelectionAdmissibility d a) (hμ : a.μ = d.μ) (hτ : a.τ = d.τ)
    (hγ : a.γ = selectionGamma d) (hstrip : a.strip = d.strip) (ht0 : a.t₀ = selectiont₀ d)
    (hT0 : a.T₀ = selectionT₀ d) (hs : 0 < a.s₀) (he : 0 < a.ε₀) : WeakBudgetCtx d a :=
  ⟨hadm, weakBudgetHyp_of_adm d a hadm hμ hτ hγ hstrip hs he, hμ, hτ, hstrip, ht0, hT0⟩

section Main
variable {d : SelectionData n} {a : SelectionSchedule n} (c : WeakBudgetCtx d a)
include c

theorem wbud_Q₀_nonneg : 0 ≤ selectionQ₀ a := by
  have h := c.hyp
  have := h.hs
  have := h.he
  have := h.hγ
  have := h.hstrip
  have hT : 0 < a.T₀ := by linarith [h.hT]
  unfold selectionQ₀ selectionCQ
  positivity

/-- Ratios of the schedule at the data's exponent. -/
theorem wbud_ratios :
    0 < selectionQ n a.μ a.τ ∧ selectionQ n a.μ a.τ ≤ 1 / 32 ∧
    0 < selectionG n a.μ a.τ 0 ∧ selectionG n a.μ a.τ 0 ≤ 1 / 32 ∧
    selectionG n a.μ a.τ 0 * (2 : ℝ) ^ (a.τ + 1) = 2 * selectionG n a.μ a.τ 3 ∧
    selectionG n a.μ a.τ 3 ≤ 1 / 32 := by
  have h := c.hyp
  obtain ⟨hq, hq5, -, hG, -⟩ := schedule_ratios h.hn h.hμ h.hτ
  have hv := (selectionVarpi_pos_le_one n a.μ h.hτ).1
  have hρ : 0 < selectionVarrho n a.μ a.τ := by unfold selectionVarrho; positivity
  have h5 : (2 : ℝ)⁻¹ ^ 5 = 1 / 32 := by norm_num
  have hG0 : selectionG n a.μ a.τ 0 =
      selectionVarrho n a.μ a.τ * (2 : ℝ) ^ a.τ * 2 ^ (n + 1) := by simp [selectionG]
  have hG3 : selectionG n a.μ a.τ 3 =
      selectionVarrho n a.μ a.τ * (2 : ℝ) ^ (2 * a.τ) * 2 ^ (n + 1) := by simp [selectionG]
  refine ⟨hq, h5 ▸ hq5, ?_, h5 ▸ hG 0, ?_, h5 ▸ hG 3⟩
  · rw [hG0]
    positivity
  · rw [hG0, hG3, Real.rpow_add (by norm_num), Real.rpow_one,
      show 2 * a.τ = a.τ + a.τ by ring, Real.rpow_add (by norm_num)]
    ring

/-- Lower bounds for `Ξ`, in the schedule's own variables. -/
theorem wbud_Xi_le :
    2 + a.t₀ / (a.strip / 24) ≤ selectionXi d ∧
    (2 : ℝ) ^ (a.τ + 1) * (a.strip / 24) / a.t₀ ≤ selectionXi d ∧
    (2 : ℝ) ^ (a.τ + 1) ≤ selectionXi d ∧
    2 * (a.T₀ * (a.strip / 24)) ≤ selectionXi d := by
  have h := c.hyp
  have hw2 : 2 ≤ (2 : ℝ) ^ (a.τ + 1) := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1 : ℝ) ≤ a.τ + 1 by linarith [h.hτ])
    simpa using this
  have hσ : 0 < a.strip / 24 := by have := h.hstrip; positivity
  have hT : 0 < a.T₀ := by linarith [h.hT]
  have hp : 0 ≤ a.t₀ / (a.strip / 24) := by have := h.ht; positivity
  have hq : 0 ≤ (a.strip / 24) / a.t₀ := by have := h.ht; positivity
  have hr : 0 ≤ a.T₀ * (a.strip / 24) := by positivity
  have hX : selectionXi d = (2 : ℝ) ^ (a.τ + 1) * (1 + a.t₀ / (a.strip / 24) +
      (a.strip / 24) / a.t₀ + a.T₀ * (a.strip / 24)) := by
    unfold selectionXi
    rw [← c.hτ, ← c.hstrip, ← c.ht0, ← c.hT0]
  rw [hX]
  set w : ℝ := (2 : ℝ) ^ (a.τ + 1)
  set p := a.t₀ / (a.strip / 24)
  set q := (a.strip / 24) / a.t₀
  set r := a.T₀ * (a.strip / 24)
  have e : w * (a.strip / 24) / a.t₀ = w * q := by simp only [q]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.2 hw2) (add_nonneg zero_le_one hp), mul_nonneg
      (zero_le_two.trans hw2) (add_nonneg hq hr)]
  · rw [e]
    nlinarith [mul_nonneg (zero_le_two.trans hw2) (add_nonneg (add_nonneg zero_le_one hp) hr)]
  · nlinarith [mul_nonneg (zero_le_two.trans hw2) (add_nonneg (add_nonneg hp hq) hr)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hw2) (add_nonneg (add_nonneg zero_le_one hp) hq),
      mul_nonneg (sub_nonneg.2 hw2) hr, mul_nonneg (zero_le_two.trans hw2) hr]

/-- Geometric domination of the stagewise budgets by `c (1/32)^j`. -/
theorem wbud_geo (j : ℕ) :
    selectionA a j ≤ (2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) * (1 / 32 : ℝ) ^ j ∧
    selectionAlpha a j ≤ (selectionQ₀ a * a.s₀ / 32) * (1 / 32 : ℝ) ^ j ∧
    selectionMapBudget a j ≤
      (selectionQ₀ a * (2 + a.t₀ / (a.strip / 24)) / 16) * (1 / 32 : ℝ) ^ j ∧
    selectionRealBudget a j ≤
      (4 * π / selectionCQ n * a.T₀ * (a.strip / 24) * selectionQ₀ a) * (1 / 32 : ℝ) ^ j := by
  have h := c.hyp
  obtain ⟨hq, hq32, hg, hg32, -, -⟩ := wbud_ratios c
  have hQ0 := wbud_Q₀_nonneg c
  have hσ := wbud_σ_pos h j
  have hs := wbud_s_pos h j
  have hCQ : 162 ≤ selectionCQ n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    unfold selectionCQ
    nlinarith
  have hCQ0 : 0 < selectionCQ n := by linarith
  obtain ⟨hQ0j, hA0, hAle, hκ0, hκle, hα, hRB0, hRBle, hQle⟩ := wbud_stage h j
  set g := selectionG n a.μ a.τ 0 with hgdef
  have hgj : g ^ j ≤ (1 / 32 : ℝ) ^ j := pow_le_pow_left₀ hg.le hg32 j
  have hQj : selectionQactual a j ≤ selectionQ₀ a * (1 / 32 : ℝ) ^ j :=
    hQle.trans (mul_le_mul_of_nonneg_left hgj hQ0)
  have hσ0 : 0 < a.strip / 24 := by have := h.hstrip; positivity
  have hσle : selectionσ a j ≤ a.strip / 24 := by
    have : (2 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    unfold selectionσ
    nlinarith
  have hsle : selections a j ≤ a.s₀ := by
    have : selectionQ n a.μ a.τ ^ j ≤ 1 := pow_le_one₀ hq.le (by linarith)
    unfold selections
    nlinarith [h.hs]
  have hs0 := h.hs
  have hP : 0 ≤ (1 / 32 : ℝ) ^ j := by positivity
  have hradius := c.adm.radius
  have hst : a.s₀ ≤ a.t₀ := by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    refine hradius.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [h.ht]
  have hratio : selections a j / selectionσ a j ≤ a.t₀ / (a.strip / 24) := by
    have hss : selections a j / selectionσ a j ≤ a.s₀ / (a.strip / 24) := by
      rw [div_le_div_iff₀ hσ hσ0]
      have : selections a j * (a.strip / 24) ≤ a.s₀ * selectionσ a j := by
        have e1 : selections a j ≤ a.s₀ * (2 : ℝ)⁻¹ ^ j := by
          unfold selections
          have := pow_le_pow_left₀ hq.le (show selectionQ n a.μ a.τ ≤ 2⁻¹ by linarith) j
          nlinarith [h.hs]
        have e2 : selectionσ a j = a.strip / 24 * (2 : ℝ)⁻¹ ^ j := rfl
        rw [e2]
        nlinarith [mul_le_mul_of_nonneg_right e1 hσ0.le]
      exact this
    exact hss.trans (div_le_div_of_nonneg_right hst hσ0.le)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc selectionA a j ≤ 2 * selectionσ a j * selectionQactual a j / selectionCQ n := hAle
      _ ≤ 2 * (a.strip / 24) * (selectionQ₀ a * (1 / 32 : ℝ) ^ j) / selectionCQ n := by
          refine div_le_div_of_nonneg_right ?_ hCQ0.le
          exact mul_le_mul (by linarith) hQj hQ0j (by positivity)
      _ = _ := by ring
  · rw [hα]
    calc selectionKappa a j * selections a j / 2
        ≤ selectionQactual a j / 16 * a.s₀ / 2 := by
          have := mul_le_mul hκle hsle hs.le (by positivity)
          linarith
      _ ≤ selectionQ₀ a * (1 / 32 : ℝ) ^ j / 16 * a.s₀ / 2 := by
          have := mul_le_mul_of_nonneg_right hQj hs0.le
          linarith
      _ = _ := by ring
  · unfold selectionMapBudget
    have hk : selectionKappa a j * selections a j / selectionσ a j ≤
        selectionKappa a j * (a.t₀ / (a.strip / 24)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hratio hκ0
    calc 2 * selectionKappa a j + selectionKappa a j * selections a j / selectionσ a j
        ≤ selectionKappa a j * (2 + a.t₀ / (a.strip / 24)) := by linarith
      _ ≤ selectionQactual a j / 16 * (2 + a.t₀ / (a.strip / 24)) :=
          mul_le_mul_of_nonneg_right hκle (by have := h.ht; positivity)
      _ ≤ (selectionQ₀ a * (1 / 32 : ℝ) ^ j) / 16 * (2 + a.t₀ / (a.strip / 24)) := by
          have : 0 ≤ (2 + a.t₀ / (a.strip / 24)) := by have := h.ht; positivity
          exact mul_le_mul_of_nonneg_right (by linarith) this
      _ = _ := by ring
  · refine hRBle.trans ?_
    have hK : 0 ≤ 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) := by
      have : 0 < a.T₀ := by linarith [h.hT]
      positivity
    calc 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) * selectionQactual a j
        ≤ 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) *
            (selectionQ₀ a * (1 / 32 : ℝ) ^ j) := mul_le_mul_of_nonneg_left hQj hK
      _ = _ := by ring

/-- Numerical consequences of `Q₀ Ξ ≤ 2⁻¹⁰` for the geometric constants. -/
theorem wbud_nums :
    32 / 31 * (selectionQ₀ a * (2 + a.t₀ / (a.strip / 24)) / 16) ≤ (2 : ℝ)⁻¹ ^ 12 ∧
    32 / 31 * (4 * π / selectionCQ n * a.T₀ * (a.strip / 24) * selectionQ₀ a) ≤ (2 : ℝ)⁻¹ ^ 12 ∧
    32 / 31 * (2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) ≤
      3 * (a.strip / 24) * selectionQ₀ a / selectionCQ n ∧
    32 / 31 * (selectionQ₀ a * a.s₀ / 32) ≤ a.s₀ * selectionQ₀ a / 16 ∧
    32 / 31 * ((2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) *
        (2 : ℝ) ^ (a.τ + 1) / a.t₀ + (selectionQ₀ a * a.s₀ / 32) * (2 : ℝ) ^ (a.τ + 1) / a.t₀)
      ≤ (2 : ℝ)⁻¹ ^ 10 / 16 := by
  have h := c.hyp
  have hQ0 := wbud_Q₀_nonneg c
  obtain ⟨hX1, hX2, hX3, hX4⟩ := wbud_Xi_le c
  have hW := c.adm.weighted
  have hCQ : 162 ≤ selectionCQ n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    unfold selectionCQ
    nlinarith
  have hCQ0 : 0 < selectionCQ n := by linarith
  have hσ0 : 0 < a.strip / 24 := by have := h.hstrip; positivity
  have hT : 0 < a.T₀ := by linarith [h.hT]
  have ht := h.ht
  have hs0 := h.hs
  have hpi := Real.pi_le_four
  have hpi0 := Real.pi_pos
  have hst : a.s₀ ≤ a.t₀ := by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    refine c.adm.radius.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [h.ht]
  have hw0 : 0 < (2 : ℝ) ^ (a.τ + 1) := by positivity
  set q0 := selectionQ₀ a with hq0
  set Ξ := selectionXi d
  set w := (2 : ℝ) ^ (a.τ + 1)
  have hP : q0 * Ξ ≤ (2 : ℝ)⁻¹ ^ 10 := hW
  have h12 : (2 : ℝ)⁻¹ ^ 12 = (2 : ℝ)⁻¹ ^ 10 / 4 := by norm_num
  have h10 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ 10 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hX1 hQ0
    rw [h12]
    nlinarith
  · have hc4 : 4 * π / selectionCQ n ≤ 16 / 162 := by
      rw [div_le_div_iff₀ hCQ0 (by norm_num)]
      nlinarith
    have hc0 : 0 ≤ 4 * π / selectionCQ n := by positivity
    have e : 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) * q0 =
        (4 * π / selectionCQ n) * ((a.T₀ * (a.strip / 24)) * q0) := by ring
    have h1 : (a.T₀ * (a.strip / 24)) * q0 ≤ q0 * Ξ / 2 := by
      have := mul_le_mul_of_nonneg_right hX4 hQ0
      nlinarith
    have h2 := mul_le_mul hc4 h1 (by positivity) (by norm_num)
    rw [e, h12]
    nlinarith
  · have : 0 ≤ (a.strip / 24) * q0 / selectionCQ n := by positivity
    have e1 : 2 * (a.strip / 24) * q0 / selectionCQ n = 2 * ((a.strip / 24) * q0 / selectionCQ n) :=
      by ring
    have e2 : 3 * (a.strip / 24) * q0 / selectionCQ n = 3 * ((a.strip / 24) * q0 / selectionCQ n) :=
      by ring
    rw [e1, e2]
    linarith
  · have : 0 ≤ q0 * a.s₀ := by positivity
    linarith
  · have hA : (2 * (a.strip / 24) * q0 / selectionCQ n) * w / a.t₀ ≤ 2 / 162 * (q0 * Ξ) := by
      have e : (2 * (a.strip / 24) * q0 / selectionCQ n) * w / a.t₀ =
          (2 / selectionCQ n) * (q0 * (w * (a.strip / 24) / a.t₀)) := by
        field_simp
      rw [e]
      have h1 : 2 / selectionCQ n ≤ 2 / 162 := by
        rw [div_le_div_iff₀ hCQ0 (by norm_num)]
        nlinarith
      have h2 : q0 * (w * (a.strip / 24) / a.t₀) ≤ q0 * Ξ :=
        mul_le_mul_of_nonneg_left hX2 hQ0
      exact mul_le_mul h1 h2 (by positivity) (by norm_num)
    have hB : (q0 * a.s₀ / 32) * w / a.t₀ ≤ q0 * Ξ / 32 := by
      have e : (q0 * a.s₀ / 32) * w / a.t₀ = (q0 * w / 32) * (a.s₀ / a.t₀) := by
        field_simp
      rw [e]
      have h1 : a.s₀ / a.t₀ ≤ 1 := (div_le_one ht).2 hst
      have h2 : q0 * w ≤ q0 * Ξ := mul_le_mul_of_nonneg_left hX3 hQ0
      have h3 : 0 ≤ q0 * w / 32 := by positivity
      calc q0 * w / 32 * (a.s₀ / a.t₀) ≤ q0 * w / 32 * 1 := mul_le_mul_of_nonneg_left h1 h3
        _ ≤ _ := by linarith
    nlinarith


end Main

end KAM.Planetary
