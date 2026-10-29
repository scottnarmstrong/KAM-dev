/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic
public import KAM.Strip.Averages

/-!
# The torus average after the period conversion (P11A-P2e, `stepP:p11:hc-mean`)

`p11_torusAverage_eq_avg`: the unit-cube average of `θ ↦ φ (2π θ)` is the `2π`-cell average
`SecularForm.avg φ` used by `SecularSpectrum.diagonalize`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace KAM.Planetary

section Avg

variable {n : ℕ}

/-- `hc-mean`: the unit-cube average of `φ (2π ·)` is the `2π`-cell average of `φ`. -/
theorem p11_torusAverage_eq_avg (φ : SecularForm.Vec n → ℝ) :
    KAM.torusAverage (fun θ : Fin n → ℝ => φ ((2 * Real.pi) • θ)) = SecularForm.avg φ := by
  set f : SecularForm.Vec n → ℝ := (SecularForm.cell n).indicator φ with hf
  have hpt : ∀ θ : Fin n → ℝ, f ((2 * Real.pi) • θ) =
      (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)).indicator
        (fun θ => φ ((2 * Real.pi) • θ)) θ := by
    intro θ
    have hpi : 0 < 2 * Real.pi := by positivity
    have : (2 * Real.pi) • θ ∈ SecularForm.cell n ↔
        θ ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1) := by
      simp only [SecularForm.cell, Set.mem_pi, Set.mem_univ, true_implies, Pi.smul_apply,
        smul_eq_mul, Set.mem_Icc]
      refine forall_congr' fun i => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by nlinarith, by nlinarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by nlinarith, by nlinarith⟩
    by_cases h : θ ∈ Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)
    · rw [hf, Set.indicator_of_mem (this.2 h), Set.indicator_of_mem h]
    · rw [hf, Set.indicator_of_notMem (fun h' => h (this.1 h')), Set.indicator_of_notMem h]
  have hsc := MeasureTheory.Measure.integral_comp_smul (μ := volume) f (2 * Real.pi)
  have hbox : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hcell : MeasurableSet (SecularForm.cell n) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  unfold KAM.torusAverage SecularForm.avg
  rw [← integral_indicator hbox]
  simp only [← hpt]
  rw [hsc, integral_indicator hcell]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul]
  rw [abs_of_nonneg (by positivity), zpow_neg, zpow_natCast]

end Avg

end KAM.Planetary

end
