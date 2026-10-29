/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ActionBudgetDefs
public import KAM.Planetary.PGAssembly.ActionBudgetDio
public import KAM.Planetary.PGAssembly.ActionBudgetCollar

/-!
# P Part 5: the budget on the action side (`bpP:p5:budget`)

`budget` bounds the measure of the part of `D × 𝕋ⁿ` missed by the whole tori over `D₀` by
`c_n C_b √r · meas D` with the explicit data-only constant `pgBudget` of `ActionBudgetDefs`.
The proof reads the measure clause (3.1) of `PGFamilySpec` (`stepP:p5:bu-read`), bounds
`D \ D₀` by the P4 two-scale Diophantine measure estimate (`stepP:p5:bu-dio`,
`ActionBudgetDio`) and the enlargement `N_{rK}(D) \ D` through the collar (`stepP:p5:bu-collar`,
`ActionBudgetCollar`). Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-BU.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

theorem pgMeasureUpper1_nonneg (d : PGData a b) : 0 ≤ pgMeasureUpper1 d := by
  unfold pgMeasureUpper1
  dsimp only
  have hV := volume_V_pos d
  have hS : 0 ≤ latticeS (a+b) (pgTau a b) :=
    latticeS_nonneg (by unfold pgTau; exact lt_add_of_pos_right _ one_pos)
  have := (pgInverse_spec d).2.1
  have := (pgInverse_spec d).1
  refine mul_nonneg (by positivity) (le_max_of_le_left ?_)
  positivity

theorem budget (d : PGData a b) : 0 < pgBudget d ∧
    ∀ r mu : ℝ, ∀ h : admissible d (pgRstar d) r mu,
      volume (({z : Phase (a+b) | z.2 ∈ pgActionDomain d r mu ∧
        z.1 ∈ unitCube (a+b)}) \ rawUnion d r mu h (pgD0 d r mu)) ≤
        ENNReal.ofReal (kamMeasureConstant (a+b)*pgBudget d*Real.sqrt r)*
          volume (pgActionDomain d r mu) := by
  have hV := volume_V_pos d
  have hk0 := pgScales_k0_pos d
  have hk1 := pgScales_k1_pos d
  have hU1 := pgMeasureUpper1_nonneg d
  have hU2 : 0 ≤ pgMeasureUpper2 d := by
    unfold pgMeasureUpper2
    have := (pgAnalytic_spec d).2.2.2.2.2.2.1
    have hS : 0 ≤ latticeS b (pgTau a b+1) :=
      latticeS_nonneg (by
        have := pgTau_pos a b
        have : (b:ℝ) ≤ ((a+b:ℕ):ℝ) := by exact_mod_cast Nat.le_add_left b a
        unfold pgTau at *; linarith)
    positivity
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast d.hb
  have hA := (pgBoundary_spec d).1
  have hCd := (pgAnalytic_spec d).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCg := pgCgamma_pos d
  have hpos : 0 < pgBudget d := by
    unfold pgBudget
    have : 0 ≤ 4^(b+1)*2*Real.pi*(pgScales d).k0*(5*pgMeasureUpper1 d+4*pgMeasureUpper2 d) := by
      positivity
    have : 0 < 8*(pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/(volume d.V).toReal := by
      positivity
    have : 0 < (b:ℝ)*(pgScales d).k1/16 := by positivity
    linarith
  refine ⟨hpos, fun r mu h => ?_⟩
  have hspec : PGFamilySpec d r mu h (pgFamily d r mu h) := (torus_conv d r mu h).choose_spec
  obtain ⟨-, -, -, -, -, hmeas, -⟩ := hspec
  obtain ⟨hr0, hr1, -, -, -, -, -, -, hrK0, -⟩ := budget_facts d h
  have hsub : ({z : Phase (a+b) | z.2 ∈ pgActionDomain d r mu ∧ z.1 ∈ unitCube (a+b)}) \
      rawUnion d r mu h (pgD0 d r mu) ⊆
      ({z : Phase (a+b) | z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK ∧
        z.1 ∈ unitCube (a+b)}) \ (⋃ J ∈ pgD0 d r mu, range ((pgFamily d r mu h).raw J)) := by
    rintro z ⟨⟨hz2, hz1⟩, hznot⟩
    exact ⟨⟨⟨z.2, hz2, by simpa using hrK0⟩, hz1⟩, hznot⟩
  have hd := budget_dio d h
  have hc := budget_collar d h
  have hsq : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hP1 : 0 ≤ 4^(b+1)*2*Real.pi*(pgScales d).k0*
      (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d)*Real.sqrt r := by positivity
  have hP2 : 0 ≤ (8*(pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/(volume d.V).toReal +
      b*(pgScales d).k1/16)*Real.sqrt r := by positivity
  have hcn : 0 ≤ kamMeasureConstant (a+b) := by unfold kamMeasureConstant; positivity
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := hmeas
    _ ≤ ENNReal.ofReal (kamMeasureConstant (a+b)) *
        (ENNReal.ofReal (pgBudget d*Real.sqrt r) * volume (pgActionDomain d r mu)) := by
      refine mul_le_mul' le_rfl ?_
      calc _ ≤ _ := add_le_add hd hc
        _ = _ := by
          rw [← add_mul, ← ENNReal.ofReal_add hP1 hP2]
          congr 2
          unfold pgBudget
          ring
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hcn, mul_assoc]

end KAM.Planetary

end
