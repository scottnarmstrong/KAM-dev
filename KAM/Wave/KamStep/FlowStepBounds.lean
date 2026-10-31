/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.FlowSmoothDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The flow estimates with the numerical margins (`bpW:w5:flow` (i), (ii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

With `L = M/δ ≤ 1/64` (the step hypotheses: `M = M_F ≤ σ/256`, `δ = σ/4`) one has
`1 + L e^L ≤ 2`, so the displacement `Ψ^t` of `FlowSmooth` satisfies
`‖Ψ^t‖ ≤ M`, `‖Ψ_Z^t - Ψ_{Z'}^t‖ ≤ 2N` (`bpW:w5:flow` (i), step `f-par`) and, on points with a
`ρ`-ball in `U`, `‖DΨ^t‖ ≤ M/ρ`, `‖DΨ_Z^t - DΨ_{Z'}^t‖ ≤ 2N/ρ` (step `f-der`, `ρ = σ/8`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Wave

theorem one_add_mul_exp_le_two {L : ℝ} (h0 : 0 ≤ L) (h1 : L ≤ 1 / 64) : 1 + L * Real.exp L ≤ 2 := by
  have h2 : Real.exp L ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  have h3 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos L]

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {ι : G →L[ℂ] F} {Z Z' : F → G} {V U : Set F} {M δ : ℝ}

omit [CompleteSpace G] in
/-- `‖Ψ^t‖ ≤ M` (`|t| ≤ 1`). -/
theorem flowII_disp (h : FlowHyp (smoothField ι Z) V U M δ)
    (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖smoothDisp ι Z t w‖ ≤ M := by
  have := norm_smoothDisp_le h hb hw ht
  have h1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  nlinarith [h.M_pos]

omit [CompleteSpace G] in
/-- `‖Ψ_Z^t - Ψ_{Z'}^t‖ ≤ 2N` when `M/δ ≤ 1/64`. -/
theorem flowII_disp_sub (h : FlowHyp (smoothField ι Z) V U M δ)
    (h' : FlowHyp (smoothField ι Z') V U M δ) (hZ : DifferentiableOn ℂ Z V)
    (hZ' : DifferentiableOn ℂ Z' V) (hι : ∀ g, ‖ι g‖ ≤ ‖g‖) (hb' : ∀ z ∈ V, ‖Z' z‖ ≤ M)
    (hL : M / δ ≤ 1 / 64) {N : ℝ} (hN : 0 ≤ N) (hZZ : ∀ z ∈ V, ‖Z z - Z' z‖ ≤ N) {w : F}
    (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖smoothDisp ι Z t w - smoothDisp ι Z' t w‖ ≤ 2 * N := by
  have := norm_smoothDisp_sub_le h h' hZ hZ' hι hb' hN hZZ hw ht
  have h1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have h2 := one_add_mul_exp_le_two (div_nonneg h.M_pos.le h.delta_pos.le) hL
  have h3 : N * (1 + M / δ * Real.exp (M / δ)) ≤ 2 * N := by nlinarith
  have hc0 : 0 ≤ N * (1 + M / δ * Real.exp (M / δ)) :=
    mul_nonneg hN (by have := Real.exp_pos (M / δ); have := div_nonneg h.M_pos.le h.delta_pos.le; positivity)
  calc _ ≤ |t| * (N * (1 + M / δ * Real.exp (M / δ))) := this
    _ ≤ 1 * (2 * N) := mul_le_mul h1 h3 hc0 zero_le_one
    _ = 2 * N := one_mul _

omit [CompleteSpace G] in
/-- `‖DΨ^t(w)‖ ≤ M/ρ` and `Dφ^t - I = ι ∘ DΨ^t`. -/
theorem flowII_deriv (h : FlowHyp (smoothField ι Z) V U M δ) (hZ : DifferentiableOn ℂ Z V)
    (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) {w : F} {ρ : ℝ} (hρ : 0 < ρ) (hball : ball w ρ ⊆ U) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖fderiv ℂ (smoothDisp ι Z t) w‖ ≤ M / ρ := by
  have := norm_fderiv_smoothDisp_le h hZ hb hρ hball ht
  have h1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  refine this.trans (div_le_div_of_nonneg_right ?_ hρ.le)
  nlinarith [h.M_pos]

omit [CompleteSpace G] in
/-- `‖DΨ_Z^t(w) - DΨ_{Z'}^t(w)‖ ≤ 2N/ρ` when `M/δ ≤ 1/64`. -/
theorem flowII_deriv_sub (h : FlowHyp (smoothField ι Z) V U M δ)
    (h' : FlowHyp (smoothField ι Z') V U M δ) (hZ : DifferentiableOn ℂ Z V)
    (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) (hZ' : DifferentiableOn ℂ Z' V) (hb' : ∀ z ∈ V, ‖Z' z‖ ≤ M)
    (hι : ∀ g, ‖ι g‖ ≤ ‖g‖) (hL : M / δ ≤ 1 / 64) {N : ℝ} (hN : 0 ≤ N)
    (hZZ : ∀ z ∈ V, ‖Z z - Z' z‖ ≤ N) {w : F} {ρ : ℝ} (hρ : 0 < ρ) (hball : ball w ρ ⊆ U)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖fderiv ℂ (smoothDisp ι Z t) w - fderiv ℂ (smoothDisp ι Z' t) w‖ ≤ 2 * N / ρ := by
  have := norm_fderiv_smoothDisp_sub_le h hZ hb h' hZ' hb' hι hN hZZ hρ hball ht
  have h1 : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have h2 := one_add_mul_exp_le_two (div_nonneg h.M_pos.le h.delta_pos.le) hL
  have h3 : N * (1 + M / δ * Real.exp (M / δ)) ≤ 2 * N := by nlinarith
  have hc0 : 0 ≤ N * (1 + M / δ * Real.exp (M / δ)) :=
    mul_nonneg hN (by have := Real.exp_pos (M / δ); have := div_nonneg h.M_pos.le h.delta_pos.le; positivity)
  refine this.trans (div_le_div_of_nonneg_right ?_ hρ.le)
  calc _ ≤ 1 * (2 * N) := mul_le_mul h1 h3 hc0 zero_le_one
    _ = 2 * N := one_mul _

end KAM.Wave
