/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.FlowVariational
public import KAM.Wave.Analytic.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Joint continuity of the flow and its derivative (blueprint-W `bpW:w5:flow-calc` (i))

For `h : FlowHyp X V U M δ` (blueprint `bpW:w1:flow`), with no further premise:

* `continuousOn_holoFlow_joint`: `(t, w) ↦ φ^t(w)` is continuous on `[-1, 1] × U`;
* `continuousOn_fderiv_holoFlow_joint`: `(t, w) ↦ Dφ^t(w)` is continuous on `[-1, 1] × U`.

Both follow from `continuousOn_jointOfLocLip` (continuity in `t` at each fixed `w`, plus a local
Lipschitz bound in `w` uniform in `t`). For `φ^t` the Lipschitz bound is the mean value inequality
with `‖Dφ^t‖ ≤ e^{M/δ}` (`norm_fderiv_holoFlow_le`); for `Dφ^t` it is the Cauchy estimate
`norm_fderiv_sub_le_holoMargin` with the uniform bound `‖φ^t(z)‖ ≤ ‖z‖ + M`
(`norm_holoFlow_sub_le`). Time continuity is `continuousOn_holoFlow_time` (W1) and
`continuousOn_fderiv_holoFlow_time`.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Wave

/-- Continuity on `I × U` from continuity in `t` at each `w ∈ U` and a local Lipschitz bound in `w`
that is uniform in `t ∈ I`. -/
theorem continuousOn_jointOfLocLip {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {f : ℝ → F → G} {I : Set ℝ} {U : Set F}
    (hT : ∀ w ∈ U, ContinuousOn (fun t => f t w) I)
    (hL : ∀ w₀ ∈ U, ∃ ρ > 0, ∃ C ≥ 0, ∀ t ∈ I, ∀ w ∈ ball w₀ ρ,
      ‖f t w - f t w₀‖ ≤ C * ‖w - w₀‖) :
    ContinuousOn (fun x : ℝ × F => f x.1 x.2) (I ×ˢ U) := by
  rintro ⟨t₀, w₀⟩ ⟨ht₀, hw₀⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨ρ, hρ, C, hC, hLip⟩ := hL w₀ hw₀
  obtain ⟨δ₁, hδ₁, hT₁⟩ := Metric.continuousWithinAt_iff.1 (hT w₀ hw₀ t₀ ht₀) (ε / 2)
    (by positivity)
  refine ⟨min δ₁ (min ρ (ε / (2 * (C + 1)))), by positivity, ?_⟩
  rintro ⟨t, w⟩ ⟨ht, _⟩ hd
  rw [Prod.dist_eq] at hd
  have hdt : dist t t₀ < δ₁ :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hd (min_le_left _ _))
  have hdw : dist w w₀ < min ρ (ε / (2 * (C + 1))) :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hd (min_le_right _ _))
  have hwρ : w ∈ ball w₀ ρ := lt_of_lt_of_le hdw (min_le_left _ _)
  have hwε : ‖w - w₀‖ < ε / (2 * (C + 1)) := by
    rw [← dist_eq_norm]; exact lt_of_lt_of_le hdw (min_le_right _ _)
  have h1 := hLip t ht w hwρ
  have h2 := hT₁ ht hdt
  rw [dist_eq_norm] at h2 ⊢
  have hCε : C * ‖w - w₀‖ ≤ ε / 2 := by
    have hC1 : 0 < C + 1 := by linarith
    calc C * ‖w - w₀‖ ≤ (C + 1) * ‖w - w₀‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ ≤ (C + 1) * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hwε.le hC1.le
      _ = ε / 2 := by field_simp
  calc ‖f t w - f t₀ w₀‖ = ‖(f t w - f t w₀) + (f t w₀ - f t₀ w₀)‖ := by abel_nf
    _ ≤ ‖f t w - f t w₀‖ + ‖f t w₀ - f t₀ w₀‖ := norm_add_le _ _
    _ < ε := by linarith

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {X : F → F} {V U : Set F} {M δ : ℝ} (h : FlowHyp X V U M δ)
include h

/-- **`(t, w) ↦ φ^t(w)` is continuous on `[-1, 1] × U`** (`bpW:w5:flow-calc` (i), step `c-cont`). -/
theorem continuousOn_holoFlow_joint :
    ContinuousOn (fun x : ℝ × F => holoFlow X x.1 x.2) (Icc (-1 : ℝ) 1 ×ˢ U) := by
  refine continuousOn_jointOfLocLip (fun w hw => continuousOn_holoFlow_time h hw) ?_
  intro w₀ hw₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp h.isOpen_U w₀ hw₀
  refine ⟨ρ, hρ, Real.exp (M / δ), (Real.exp_pos _).le, fun t ht w hw => ?_⟩
  have hL : 0 ≤ M / δ := div_nonneg h.M_pos.le h.delta_pos.le
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ) (f := holoFlow X t)
    (fun z hz => (holomorphicOn_holoFlow h ht).differentiableAt
      (h.isOpen_U.mem_nhds (hball hz))) (fun z hz => ?_) (convex_ball w₀ ρ)
    (mem_ball_self hρ) hw
  refine (norm_fderiv_holoFlow_le h (hball hz) ht).trans (Real.exp_le_exp.mpr ?_)
  nlinarith

/-- **`(t, w) ↦ Dφ^t(w)` is continuous on `[-1, 1] × U`** (`bpW:w5:flow-calc` (i), step
`c-cont`). -/
theorem continuousOn_fderiv_holoFlow_joint :
    ContinuousOn (fun x : ℝ × F => fderiv ℂ (holoFlow X x.1) x.2) (Icc (-1 : ℝ) 1 ×ˢ U) := by
  refine continuousOn_jointOfLocLip (fun w hw => continuousOn_fderiv_holoFlow_time h hw) ?_
  intro w₀ hw₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h.isOpen_U w₀ hw₀
  set ρ := ε / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hsub : ball w₀ (2 * ρ) ⊆ U := by rw [hρdef, show 2 * (ε / 2) = ε by ring]; exact hball
  set B := ‖w₀‖ + 2 * ρ + M with hB
  have hB0 : 0 ≤ B := by have := h.M_pos; positivity
  refine ⟨ρ / 2, by positivity, 2 * B * (ρ ^ 2)⁻¹, by positivity, fun t ht w hw => ?_⟩
  have hbd : ∀ z ∈ ball w₀ (2 * ρ), ‖holoFlow X t z‖ ≤ B := fun z hz => by
    have h1 := norm_holoFlow_sub_le h (hsub hz) ht
    have ht1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hz' : ‖z - w₀‖ < 2 * ρ := by rw [← dist_eq_norm]; exact hz
    have hzn : ‖z‖ ≤ ‖w₀‖ + ‖z - w₀‖ := by
      have := norm_add_le w₀ (z - w₀); simpa using this
    have hzt : ‖holoFlow X t z‖ ≤ ‖z‖ + ‖holoFlow X t z - z‖ := by
      have := norm_add_le z (holoFlow X t z - z); simpa using this
    have hMt : M * |t| ≤ M := by nlinarith [h.M_pos]
    linarith
  exact norm_fderiv_sub_le_holoMargin h.isOpen_U (holomorphicOn_holoFlow h ht) hρ hB0 hsub hbd hw
    (mem_ball_self (by positivity))

end KAM.Wave

end
