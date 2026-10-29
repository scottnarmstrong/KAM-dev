/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.Budgets

/-!
# The increments against the collars: the literal steps (P11A-4)

Unsigned literal exports of `stepP:p11a:pl4-terms` and `stepP:p11a:pl4-sum` (proof steps of
`bpP:p11a:param-lip-sum`) at the adapted schedule `a = selectionAdapted d ε`, `0 < ε ≤ ε_adm`:

* `pl4_terms_node`: `a_j/t_{j+1} ≤ (2ς₀Q₀2^{τ+1}/(C_Q t₀)) g₄^j`,
  `α_j/t_{j+1} ≤ (s₀Q₀2^{τ+1}/(32t₀)) (2 q g₄)^j` and `g₄ = g₁ 2^τ`
  (`g₁ = selectionG … 0`, `g₄ = selectionG … 3`, `q = selectionQ`, `ς₀ = strip/24`);
* `pl4_sum_node`: `S_b ≤ (32/31) Q₀ Ξ (2/C_Q + 1/32) ≤ 0.046·2⁻¹⁰ ≤ 2⁻¹⁰/16`.

`wbud_lip_term` only states the combined rate `(1/32)^j`; the separate rates are re-derived here.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

section Ctx
variable {d : SelectionData n} {a : SelectionSchedule n} (c : WeakBudgetCtx d a)
include c

/-- The separate geometric rates of the two increments, from the budget context. -/
theorem pl4_terms_ctx (j : ℕ) :
    selectionA a j / selectiont a (j + 1) ≤
      ((2 * (a.strip / 24) * selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1)) / (selectionCQ n * a.t₀)) *
        selectionG n a.μ a.τ 3 ^ j ∧
    selectionAlpha a j / selectiont a (j + 1) ≤
      ((a.s₀ * selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1)) / (32 * a.t₀)) *
        (2 * selectionQ n a.μ a.τ * selectionG n a.μ a.τ 3) ^ j ∧
    selectionG n a.μ a.τ 3 = selectionG n a.μ a.τ 0 * (2 : ℝ) ^ a.τ := by
  have h := c.hyp
  obtain ⟨hq, hq32, hg, hg32, hgw, hG3⟩ := wbud_ratios c
  have hQ0 := wbud_Q₀_nonneg c
  have hs := wbud_s_pos h j
  have hσ := wbud_σ_pos h j
  have htj := wbud_t_pos c (j + 1)
  have hCQ : 162 ≤ selectionCQ n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    unfold selectionCQ
    nlinarith
  have hCQ0 : 0 < selectionCQ n := by linarith
  obtain ⟨hQ0j, hA0, hAle, hκ0, hκle, hα, -, -, hQle⟩ := wbud_stage h j
  set g := selectionG n a.μ a.τ 0 with hgdef
  set g4 := selectionG n a.μ a.τ 3 with hg4def
  set w : ℝ := (2 : ℝ) ^ (a.τ + 1) with hwdef
  have hw0 : 0 < w := by positivity
  have hs0 := h.hs
  have hσ0 : 0 < a.strip / 24 := by have := h.hstrip; positivity
  have ht0 := h.ht
  have hQj : selectionQactual a j ≤ selectionQ₀ a * g ^ j := hQle
  have hgw' : g * w = 2 * g4 := hgw
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
  have hαj : selectionAlpha a j ≤
      (selectionQ₀ a * a.s₀ / 32) * (g * selectionQ n a.μ a.τ) ^ j := by
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
  have hA' := div_le_div_of_nonneg_right hAj htj.le
  have hα' := div_le_div_of_nonneg_right hαj htj.le
  rw [wbud_div_t c] at hA' hα'
  have e1 : g / 2 * w = g4 := by linarith
  have e2 : g * selectionQ n a.μ a.τ * w = 2 * selectionQ n a.μ a.τ * g4 := by
    calc g * selectionQ n a.μ a.τ * w = selectionQ n a.μ a.τ * (g * w) := by ring
      _ = _ := by rw [hgw']; ring
  rw [e1] at hA'
  rw [e2] at hα'
  refine ⟨hA'.trans (le_of_eq ?_), hα'.trans (le_of_eq ?_), ?_⟩
  · rw [hwdef]; field_simp
  · rw [hwdef]; field_simp
  · have : g * (2 : ℝ) ^ a.τ * 2 = 2 * g4 := by
      rw [← hgw', hwdef, Real.rpow_add (by norm_num), Real.rpow_one]
      ring
    linarith

/-- The intermediate bound `(32/31) Q₀ Ξ (2/C_Q + 1/32)` and the numerical conclusion. -/
theorem pl4_sum_ctx :
    Summable (fun j => (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)) ∧
    ∑' j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) ≤
      32 / 31 * (selectionQ₀ a * selectionXi d * (2 / selectionCQ n + 1 / 32)) ∧
    32 / 31 * (selectionQ₀ a * selectionXi d * (2 / selectionCQ n + 1 / 32)) ≤
      (46 / 1000 : ℝ) * (2 : ℝ)⁻¹ ^ 10 ∧
    (46 / 1000 : ℝ) * (2 : ℝ)⁻¹ ^ 10 ≤ (2 : ℝ)⁻¹ ^ 10 / 16 := by
  have h := c.hyp
  obtain ⟨hq, hq32, hg, hg32, hgw, hG3⟩ := wbud_ratios c
  have hQ0 := wbud_Q₀_nonneg c
  obtain ⟨hX1, hX2, hX3, hX4⟩ := wbud_Xi_le c
  have hW : selectionQ₀ a * selectionXi d ≤ (2 : ℝ)⁻¹ ^ 10 := c.adm.weighted
  have hCQ : 162 ≤ selectionCQ n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    unfold selectionCQ
    nlinarith
  have hCQ0 : 0 < selectionCQ n := by linarith
  have hσ0 : 0 < a.strip / 24 := by have := h.hstrip; positivity
  have ht := h.ht
  have hs0 := h.hs
  have hst : a.s₀ ≤ a.t₀ := by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.hn
    refine c.adm.radius.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [h.ht]
  have hw0 : 0 < (2 : ℝ) ^ (a.τ + 1) := by positivity
  set q0 := selectionQ₀ a with hq0
  set Ξ := selectionXi d
  set w := (2 : ℝ) ^ (a.τ + 1) with hwdef
  set c1 := (2 * (a.strip / 24) * q0 * w) / (selectionCQ n * a.t₀) with hc1
  set c2 := (a.s₀ * q0 * w) / (32 * a.t₀) with hc2
  have hc1le : c1 ≤ 2 / selectionCQ n * (q0 * Ξ) := by
    have e : c1 = (2 / selectionCQ n) * (q0 * (w * (a.strip / 24) / a.t₀)) := by
      rw [hc1]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX2 hQ0) (by positivity)
  have hc2le : c2 ≤ q0 * Ξ / 32 := by
    have e : c2 = (q0 * w / 32) * (a.s₀ / a.t₀) := by rw [hc2]; field_simp
    rw [e]
    have h1 : a.s₀ / a.t₀ ≤ 1 := (div_le_one ht).2 hst
    have h2 : q0 * w ≤ q0 * Ξ := mul_le_mul_of_nonneg_left hX3 hQ0
    have h3 : 0 ≤ q0 * w / 32 := by positivity
    calc q0 * w / 32 * (a.s₀ / a.t₀) ≤ q0 * w / 32 * 1 := mul_le_mul_of_nonneg_left h1 h3
      _ ≤ _ := by linarith
  have hc1_0 : 0 ≤ c1 := by rw [hc1]; positivity
  have hc2_0 : 0 ≤ c2 := by rw [hc2]; positivity
  have hnn : ∀ j, 0 ≤ (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) :=
    fun j => (wbud_lip_term c j).1
  have hrate : ∀ j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) ≤
      (c1 + c2) * (1 / 32 : ℝ) ^ j := by
    intro j
    obtain ⟨t1, t2, -⟩ := pl4_terms_ctx c j
    have hG30 : 0 ≤ selectionG n a.μ a.τ 3 := by
      rw [(pl4_terms_ctx c 0).2.2]; positivity
    rw [add_div]
    have hp1 : selectionG n a.μ a.τ 3 ^ j ≤ (1 / 32 : ℝ) ^ j :=
      pow_le_pow_left₀ hG30 hG3 j
    have hp2 : (2 * selectionQ n a.μ a.τ * selectionG n a.μ a.τ 3) ^ j ≤ (1 / 32 : ℝ) ^ j :=
      pow_le_pow_left₀ (by have := hg32; positivity) (by nlinarith) j
    have := mul_le_mul_of_nonneg_left hp1 hc1_0
    have := mul_le_mul_of_nonneg_left hp2 hc2_0
    nlinarith
  obtain ⟨hs, hsum⟩ := wbud_tsum_le_zero hnn hrate
  have hmid : 32 / 31 * (c1 + c2) ≤ 32 / 31 * (q0 * Ξ * (2 / selectionCQ n + 1 / 32)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    nlinarith
  refine ⟨hs, hsum.trans hmid, ?_, by norm_num⟩
  have hc : 2 / selectionCQ n + 1 / 32 ≤ 437 / 10000 := by
    have : 2 / selectionCQ n ≤ 2 / 162 := by
      rw [div_le_div_iff₀ hCQ0 (by norm_num)]
      nlinarith
    linarith [show (2 : ℝ) / 162 + 1 / 32 ≤ 437 / 10000 by norm_num]
  have hc0 : 0 ≤ 2 / selectionCQ n + 1 / 32 := by positivity
  have h1 : q0 * Ξ * (2 / selectionCQ n + 1 / 32) ≤ (2 : ℝ)⁻¹ ^ 10 * (437 / 10000) :=
    mul_le_mul hW hc hc0 (by positivity)
  nlinarith

end Ctx

/-- `stepP:p11a:pl4-terms`. -/
theorem pl4_terms_node (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := selectionAdapted d ε
    ∀ j : ℕ,
      selectionA a j / selectiont a (j + 1) ≤
        ((2 * (a.strip / 24) * selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1)) / (selectionCQ n * a.t₀)) *
          selectionG n a.μ a.τ 3 ^ j ∧
      selectionAlpha a j / selectiont a (j + 1) ≤
        ((a.s₀ * selectionQ₀ a * (2 : ℝ) ^ (a.τ + 1)) / (32 * a.t₀)) *
          (2 * selectionQ n a.μ a.τ * selectionG n a.μ a.τ 3) ^ j ∧
      selectionG n a.μ a.τ 3 = selectionG n a.μ a.τ 0 * (2 : ℝ) ^ a.τ := by
  intro a j
  obtain ⟨hadm, hs, -⟩ := free_radius d ε he hsmall
  have he' : 0 < (selectionAdapted d ε).ε₀ := by
    show 0 < 2 * ε
    positivity
  exact pl4_terms_ctx
    (weakBudgetCtx_of d (selectionAdapted d ε) hadm rfl rfl rfl rfl rfl rfl hs he') j

/-- `stepP:p11a:pl4-sum`. -/
theorem pl4_sum_node (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) :
    let a := selectionAdapted d ε
    Summable (fun j => (selectionA a j + selectionAlpha a j) / selectiont a (j + 1)) ∧
    ∑' j, (selectionA a j + selectionAlpha a j) / selectiont a (j + 1) ≤
      32 / 31 * (selectionQ₀ a * selectionXi d * (2 / selectionCQ n + 1 / 32)) ∧
    32 / 31 * (selectionQ₀ a * selectionXi d * (2 / selectionCQ n + 1 / 32)) ≤
      (46 / 1000 : ℝ) * (2 : ℝ)⁻¹ ^ 10 ∧
    (46 / 1000 : ℝ) * (2 : ℝ)⁻¹ ^ 10 ≤ (2 : ℝ)⁻¹ ^ 10 / 16 := by
  intro a
  obtain ⟨hadm, hs, -⟩ := free_radius d ε he hsmall
  have he' : 0 < (selectionAdapted d ε).ε₀ := by
    show 0 < 2 * ε
    positivity
  exact pl4_sum_ctx (weakBudgetCtx_of d (selectionAdapted d ε) hadm rfl rfl rfl rfl rfl rfl hs he')

end KAM.Planetary

end
