/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A triangular double integral (external fact `bpW:w5:ext-triangle`)

For continuous `g : ℝ → V` (Banach `V`), `∫₀¹ ∫₀ᵗ g(τ) dτ dt = ∫₀¹ (1-τ) g(τ) dτ`
(`stepTriangle`), proved without Fubini: `h(t) = ∫₀ᵗ g` has `h' = g`, and integrating
`d/dt ((t-1) h(t)) = h(t) + (t-1) g(t)` over `[0,1]` gives `0 = ∫ h + ∫ (t-1) g`.
-/

@[expose] public section

namespace KAM.Wave

open intervalIntegral

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem stepTriangle {g : ℝ → V} (hg : Continuous g) :
    ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..t, g τ = ∫ τ in (0 : ℝ)..1, (1 - τ) • g τ := by
  set h : ℝ → V := fun t => ∫ τ in (0 : ℝ)..t, g τ with hh
  have hh' : ∀ t, HasDerivAt h (g t) t := fun t =>
    hg.integral_hasStrictDerivAt 0 t |>.hasDerivAt
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hh' t).continuousAt
  have h0 : h 0 = 0 := by simp [hh]
  have hd : ∀ t, HasDerivAt (fun t => (t - 1) • h t) (h t + (t - 1) • g t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 t := (hasDerivAt_id t).sub_const 1
    exact (h1.smul (hh' t)).congr_deriv (by simp [add_comm])
  have hc2 : Continuous (fun t : ℝ => (t - 1) • g t) := by fun_prop
  have hcont : Continuous fun t => h t + (t - 1) • g t := hhc.add hc2
  have key := integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable 0 1)
  have hz : (1 - 1 : ℝ) • h 1 - (0 - 1 : ℝ) • h 0 = 0 := by simp [h0]
  have key' : ∫ t in (0 : ℝ)..1, (h t + (t - 1) • g t) = 0 := by rw [key]; exact hz
  have e1 : ∫ t in (0 : ℝ)..1, (h t + (t - 1) • g t) =
      (∫ t in (0 : ℝ)..1, h t) + ∫ t in (0 : ℝ)..1, (t - 1) • g t :=
    integral_add (hhc.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1)
  have e2 : ∫ t in (0 : ℝ)..1, (t - 1) • g t = -∫ t in (0 : ℝ)..1, (1 - t) • g t := by
    rw [← integral_neg]
    refine integral_congr fun t _ => ?_
    simp [sub_smul, neg_sub]
  rw [e1, e2] at key'
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using key')

/-- The same for `g` continuous on `[0,1]` only. -/
theorem stepTriangle_on {g : ℝ → V} (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..t, g τ = ∫ τ in (0 : ℝ)..1, (1 - τ) • g τ := by
  set g' : ℝ → V := fun t => g (Set.projIcc (0 : ℝ) 1 zero_le_one t) with hg'
  have hc : Continuous g' :=
    hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t).2)
  have hEq : ∀ t ∈ Set.Icc (0 : ℝ) 1, g' t = g t := fun t ht => by
    simp [hg', Set.projIcc_of_mem _ ht]
  have h1 : ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..t, g τ =
      ∫ t in (0 : ℝ)..1, ∫ τ in (0 : ℝ)..t, g' τ := by
    refine integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    refine integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le ht.1] at hτ
    exact (hEq τ ⟨hτ.1, hτ.2.trans ht.2⟩).symm
  have h2 : ∫ τ in (0 : ℝ)..1, (1 - τ) • g τ = ∫ τ in (0 : ℝ)..1, (1 - τ) • g' τ := by
    refine integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le zero_le_one] at hτ
    simp only [hEq τ hτ]
  rw [h1, h2]
  exact stepTriangle hc

end KAM.Wave
