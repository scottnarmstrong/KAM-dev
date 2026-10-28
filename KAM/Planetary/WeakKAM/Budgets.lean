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

/-- The shifted tail of a nonnegative summable series is at most the whole sum. -/
theorem wbud_tsum_shift_le {f : ℕ → ℝ} (hf0 : ∀ j, 0 ≤ f j) (hs : Summable f) (ν : ℕ) :
    ∑' j, f (j + ν) ≤ ∑' j, f j := by
  have h1 : Summable (fun j => f (j + ν)) := (summable_nat_add_iff ν).2 hs
  have h2 := Summable.sum_add_tsum_nat_add' (f := f) (k := ν) h1
  have h0 : 0 ≤ ∑ i ∈ Finset.range ν, f i := Finset.sum_nonneg fun i _ => hf0 i
  linarith

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


theorem wbud_t_pos (j : ℕ) : 0 < selectiont a j := by
  have := c.hyp.ht
  rw [selectiont_eq]
  positivity

/-- `c y^j / t_{j+1} = (c w / t₀) (w y)^j` for `w = 2^{τ+1}`. -/
theorem wbud_div_t (c' y : ℝ) (j : ℕ) :
    c' * y ^ j / selectiont a (j + 1) =
      (c' * (2 : ℝ) ^ (a.τ + 1) / a.t₀) * (y * (2 : ℝ) ^ (a.τ + 1)) ^ j := by
  have ht := c.hyp.ht
  have hw : (2 : ℝ) ^ (a.τ + 1) ≠ 0 := by positivity
  rw [selectiont_eq, inv_pow, pow_succ, mul_pow]
  field_simp

/-- Termwise bound of `(A_j + α_j) / t_{j+1}` by a geometric series. -/
theorem wbud_lip_term (j : ℕ) :
    0 ≤ (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) ∧
    (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) ≤
      ((2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) *
        (2 : ℝ) ^ (a.τ + 1) / a.t₀ + (selectionQ₀ a * a.s₀ / 32) * (2 : ℝ) ^ (a.τ + 1) / a.t₀) *
        (1 / 32 : ℝ) ^ j := by
  have h := c.hyp
  obtain ⟨hq, hq32, hg, hg32, hgw, hG3⟩ := wbud_ratios c
  have hQ0 := wbud_Q₀_nonneg c
  have hσ := wbud_σ_pos h j
  have hs := wbud_s_pos h j
  have htj := wbud_t_pos c (j + 1)
  have hCQ : 162 ≤ selectionCQ n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    unfold selectionCQ
    nlinarith
  have hCQ0 : 0 < selectionCQ n := by linarith
  obtain ⟨hQ0j, hA0, hAle, hκ0, hκle, hα, -, -, hQle⟩ := wbud_stage h j
  have hα0 : 0 ≤ selectionAlpha a j := by rw [hα]; positivity
  have hnum : 0 ≤ selectionA a j + selectionAlpha a j := add_nonneg hA0 hα0
  refine ⟨div_nonneg hnum htj.le, ?_⟩
  set g := selectionG n a.μ a.τ 0 with hgdef
  set w : ℝ := (2 : ℝ) ^ (a.τ + 1) with hwdef
  have hw0 : 0 < w := by positivity
  have hs0 := h.hs
  have hσ0 : 0 < a.strip / 24 := by have := h.hstrip; positivity
  have hQj : selectionQactual a j ≤ selectionQ₀ a * g ^ j := hQle
  have hAj : selectionA a j ≤
      (2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) * (g / 2) ^ j := by
    refine hAle.trans ?_
    have e : 2 * selectionσ a j * (selectionQ₀ a * g ^ j) / selectionCQ n =
        (2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) * (g / 2) ^ j := by
      unfold selectionσ
      rw [div_pow, inv_pow]
      field_simp
    rw [← e]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQj (by positivity)) hCQ0.le
  have hαj : selectionAlpha a j ≤ (selectionQ₀ a * a.s₀ / 32) * (g * selectionQ n a.μ a.τ) ^ j := by
    rw [hα]
    have h1 : selectionKappa a j * selections a j ≤
        (selectionQactual a j / 16) * selections a j :=
      mul_le_mul_of_nonneg_right hκle hs.le
    have h2 : selectionQactual a j / 16 * selections a j ≤
        (selectionQ₀ a * g ^ j / 16) * (a.s₀ * selectionQ n a.μ a.τ ^ j) := by
      refine mul_le_mul (by linarith) (le_of_eq rfl) hs.le (by positivity)
    have e : (selectionQ₀ a * g ^ j / 16) * (a.s₀ * selectionQ n a.μ a.τ ^ j) / 2 =
        (selectionQ₀ a * a.s₀ / 32) * (g * selectionQ n a.μ a.τ) ^ j := by
      rw [mul_pow]
      ring
    linarith
  have hx1 : g / 2 * w ≤ 1 / 32 := by nlinarith
  have hx2 : g * selectionQ n a.μ a.τ * w ≤ 1 / 32 := by
    have : g * w ≤ 1 / 16 := by linarith
    nlinarith
  rw [add_div]
  have hA' := div_le_div_of_nonneg_right hAj htj.le
  have hα' := div_le_div_of_nonneg_right hαj htj.le
  rw [wbud_div_t c] at hA' hα'
  have hc1 : 0 ≤ (2 * (a.strip / 24) * selectionQ₀ a / selectionCQ n) * w / a.t₀ := by
    have := h.ht; positivity
  have hc2 : 0 ≤ (selectionQ₀ a * a.s₀ / 32) * w / a.t₀ := by
    have := h.ht; positivity
  have hp1 : (g / 2 * w) ^ j ≤ (1 / 32 : ℝ) ^ j := pow_le_pow_left₀ (by positivity) hx1 j
  have hp2 : (g * selectionQ n a.μ a.τ * w) ^ j ≤ (1 / 32 : ℝ) ^ j :=
    pow_le_pow_left₀ (by positivity) hx2 j
  have := mul_le_mul_of_nonneg_left hp1 hc1
  have := mul_le_mul_of_nonneg_left hp2 hc2
  linarith

theorem wbud_lip :
    Summable (fun j => (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)) ∧
    ∑' j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) ≤ (2 : ℝ)⁻¹ ^ 10 / 16 := by
  obtain ⟨hs, hsum⟩ := wbud_tsum_le_zero (fun j => (wbud_lip_term c j).1)
    (fun j => (wbud_lip_term c j).2)
  exact ⟨hs, hsum.trans (wbud_nums c).2.2.2.2⟩

theorem wbud_sums_Aα :
    Summable (selectionA a) ∧ Summable (selectionAlpha a) ∧
    (∑' j, selectionA a j) ≤ 3 * (a.strip / 24) * selectionQ₀ a / selectionCQ n ∧
    (∑' j, selectionAlpha a j) ≤ a.s₀ * selectionQ₀ a / 16 := by
  have hn := wbud_nums c
  have hg := wbud_geo c
  have h := c.hyp
  obtain ⟨hsA, hA⟩ := wbud_tsum_le_zero (fun j => (wbud_stage h j).2.1) (fun j => (hg j).1)
  obtain ⟨hsα, hα⟩ := wbud_tsum_le_zero
    (fun j => by
      obtain ⟨-, -, -, -, -, hα, -⟩ := wbud_stage h j
      have := wbud_s_pos h j
      have := (wbud_stage h j).2.2.2.1
      rw [hα]; positivity) (fun j => (hg j).2.1)
  exact ⟨hsA, hsα, hA.trans hn.2.2.1, hα.trans hn.2.2.2.1⟩

theorem wbud_tail (ν : ℕ) :
    (∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) / selectiont a (ν + 1) ≤
      (2 : ℝ)⁻¹ ^ 10 := by
  have h := c.hyp
  obtain ⟨hsu, hsum⟩ := wbud_lip c
  obtain ⟨hsA, hsα, -, -⟩ := wbud_sums_Aα c
  have hAα : Summable (fun j => selectionA a (j + ν) + selectionAlpha a (j + ν)) :=
    ((summable_nat_add_iff ν).2 hsA).add ((summable_nat_add_iff ν).2 hsα)
  have hsh := (summable_nat_add_iff ν).2 hsu
  have hnn : ∀ j, 0 ≤ selectionA a j + selectionAlpha a j := fun j => by
    obtain ⟨-, hA0, -, -, -, hα, -⟩ := wbud_stage h j
    have := wbud_s_pos h j
    have := (wbud_stage h j).2.2.2.1
    rw [hα]; positivity
  have hmono : ∀ j, selectiont a (j + ν + 1) ≤ selectiont a (ν + 1) := fun j => by
    rw [selectiont_eq, selectiont_eq]
    have hw : (2 : ℝ) ≤ (2 : ℝ) ^ (a.τ + 1) := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show (1 : ℝ) ≤ a.τ + 1 by linarith [h.hτ])
      simpa using this
    have h1 : ((2 : ℝ) ^ (a.τ + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) h1 ?_) h.ht.le
    omega
  rw [← tsum_div_const]
  calc ∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν)) / selectiont a (ν + 1)
      ≤ ∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν)) /
          selectiont a (j + ν + 1) :=
        Summable.tsum_le_tsum (fun j => div_le_div_of_nonneg_left (hnn _)
          (wbud_t_pos c _) (hmono j)) (hAα.div_const _) hsh
    _ ≤ ∑' j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) :=
        wbud_tsum_shift_le (fun j => div_nonneg (hnn j) (wbud_t_pos c _).le) hsu ν
    _ ≤ (2 : ℝ)⁻¹ ^ 10 / 16 := hsum
    _ ≤ _ := by norm_num


theorem wbud_exported :
    Summable (selectionA a) ∧ Summable (selectionAlpha a) ∧
    Summable (selectionMapBudget a) ∧ Summable (selectionRealBudget a) ∧
    (∑' j, selectionMapBudget a j) ≤ (2 : ℝ)⁻¹ ^ 12 ∧
    (∑' j, selectionRealBudget a j) ≤ (2 : ℝ)⁻¹ ^ 12 ∧
    (∑' j, selectionA a j) ≤ 3 * (a.strip / 24) * selectionQ₀ a / selectionCQ n ∧
    (∑' j, selectionAlpha a j) ≤ a.s₀ * selectionQ₀ a / 16 ∧
    (∀ ν, selectionA a ν ≤ 2 * selectionσ a ν * selectionQactual a ν / selectionCQ n ∧
      selectionKappa a ν ≤ selectionQactual a ν / 16 ∧
      selectionAlpha a ν = selectionKappa a ν * selections a ν / 2 ∧
      selectionRealBudget a ν ≤ 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) *
        selectionQactual a ν ∧
      selectionQactual a ν ≤ selectionQ₀ a * selectionG n a.μ a.τ 0 ^ ν) ∧
    ∀ ν, (∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) /
      selectiont a (ν + 1) ≤ (2 : ℝ)⁻¹ ^ 10 := by
  have h := c.hyp
  have hn := wbud_nums c
  have hg := wbud_geo c
  obtain ⟨hsA, hsα, hA, hα⟩ := wbud_sums_Aα c
  have hM0 : ∀ j, 0 ≤ selectionMapBudget a j := fun j => by
    have hκ0 := (wbud_stage h j).2.2.2.1
    have := wbud_σ_pos h j
    have := wbud_s_pos h j
    unfold selectionMapBudget
    positivity
  obtain ⟨hsM, hM⟩ := wbud_tsum_le_zero hM0 (fun j => (hg j).2.2.1)
  obtain ⟨hsR, hR⟩ := wbud_tsum_le_zero (fun j => (wbud_stage h j).2.2.2.2.2.2.1)
    (fun j => (hg j).2.2.2)
  refine ⟨hsA, hsα, hsM, hsR, hM.trans hn.1, hR.trans hn.2.1, hA, hα, fun ν => ?_,
    wbud_tail c⟩
  obtain ⟨-, -, hAle, -, hκle, hαe, -, hRBle, hQle⟩ := wbud_stage h ν
  exact ⟨hAle, hκle, hαe, hRBle, hQle⟩


end Main

theorem exported_sums (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := adm_params d ε
    Summable (selectionA a) ∧ Summable (selectionAlpha a) ∧
    Summable (selectionMapBudget a) ∧ Summable (selectionRealBudget a) ∧
    (∑' j, selectionMapBudget a j) ≤ (2 : ℝ)⁻¹ ^ 12 ∧
    (∑' j, selectionRealBudget a j) ≤ (2 : ℝ)⁻¹ ^ 12 ∧
    (∑' j, selectionA a j) ≤ 3 * (a.strip / 24) * selectionQ₀ a / selectionCQ n ∧
    (∑' j, selectionAlpha a j) ≤ a.s₀ * selectionQ₀ a / 16 ∧
    (∀ ν, selectionA a ν ≤ 2 * selectionσ a ν * selectionQactual a ν / selectionCQ n ∧
      selectionKappa a ν ≤ selectionQactual a ν / 16 ∧
      selectionAlpha a ν = selectionKappa a ν * selections a ν / 2 ∧
      selectionRealBudget a ν ≤ 4 * π / selectionCQ n * a.T₀ * (a.strip / 24) *
        selectionQactual a ν ∧
      selectionQactual a ν ≤ selectionQ₀ a * selectionG n a.μ a.τ 0 ^ ν) ∧
    ∀ ν, (∑' j, (selectionA a (j + ν) + selectionAlpha a (j + ν))) /
      selectiont a (ν + 1) ≤ (2 : ℝ)⁻¹ ^ 10 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast d.n_pos
  have hC : 0 < d.C₁ := by linarith [d.hessian_normalized]
  have hL := selectionLambdaMax_pos d
  have hs : 0 < (adm_params d ε).s₀ := by
    show 0 < selectionLambdaMax d / (n * d.C₁)
    positivity
  have he' : 0 < (adm_params d ε).ε₀ := by
    show 0 < ε + n / 2 * d.C₁ * (selectionLambdaMax d / (n * d.C₁)) ^ 2
    positivity
  exact wbud_exported (weakBudgetCtx_of d (adm_params d ε) (adm_choice d ε he hsmall).2.1
    rfl rfl rfl rfl rfl rfl hs he')

/-- Derived scalar budgets at the adapted radius; no iteration hypotheses. -/
theorem param_lip_sum (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := selectionAdapted d ε
    Summable (fun j => (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)) ∧
    (∑' j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)) ≤
      (2 : ℝ)⁻¹ ^ 10 / 16 := by
  obtain ⟨hadm, hs, -⟩ := free_radius d ε he hsmall
  have he' : 0 < (selectionAdapted d ε).ε₀ := by
    show 0 < 2 * ε
    positivity
  exact wbud_lip (weakBudgetCtx_of d (selectionAdapted d ε) hadm rfl rfl rfl rfl rfl rfl hs he')

end KAM.Planetary
