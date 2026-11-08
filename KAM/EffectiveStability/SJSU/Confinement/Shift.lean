/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.Center
public import KAM.EffectiveStability.SJSU.Ecc.Main
public import KAM.EffectiveStability.SJSU.Model.SJSU18O2
public import KAM.EffectiveStability.Tube.Check.Center
public import KAM.EffectiveStability.Tube.Check.Domain
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# The SJSU shift `B` and the regularity of `SJSU18-O2` (T2-CONF, N5b phase B)

Hypotheses of `KAM.EffectiveStability.Tube.tubeChart_confinement` for the SJSU instance that need no
observable:

* the shift `B = sjsuB` (N5a): it is N6's tube centre (`sjsuB_eq_eccCenter`, by `rfl`),
  `2π`-periodic (`shiftPeriodic_sjsuB`), differentiable (`differentiable_sjsuB`), symmetric
  (`sjsuB_symm`, N5a), and `sjsuBmin_k ≤ B_k ≤ sjsuBmax_k` with
  `sjsuBmin_k = Ī_k - (L₁ k + L₂ k)`, `sjsuBmax_k = Ī_k + (L₁ k + L₂ k)` (N6's global check;
  `sjsuB_bounds`), with `2·10⁻⁶ < sjsuBmin_k` (`sjsu_rho_lt_bmin`). The bound
  `|∂_{φ_b} B_l| ≤ β_l` is N5c's `sjsu_hβ`;
* `contDiff_sjsu18O2`: `SJSU18-O2` is `C^∞` (a real part of a polynomial in `z`, `z̄`), proved for
  an arbitrary term list (`contDiff_polyRe`), so the 7,941 literal rows are never unfolded.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-! ### The shift -/

/-- The lower bound `Ī_k - (L₁ k + L₂ k)` of the SJSU tube centre. -/
def sjsuBmin (k : Fin 3) : ℚ := sjsuEccIbar k - (sjsuEccData.L₁ k + sjsuEccData.L₂ k)

/-- The upper bound `Ī_k + (L₁ k + L₂ k)` of the SJSU tube centre. -/
def sjsuBmax (k : Fin 3) : ℚ := sjsuEccIbar k + (sjsuEccData.L₁ k + sjsuEccData.L₂ k)

/-- N5a's shift is N6's tube centre. -/
theorem sjsuB_eq_eccCenter (φ : Fin 2 → ℝ) (k : Fin 3) : sjsuB φ k = sjsuEccCenter k φ := rfl

theorem shiftPeriodic_sjsuB : ShiftPeriodic sjsuB := sjsuB_add_two_pi

theorem differentiable_sjsuB : Differentiable ℝ sjsuB :=
  (contDiff_sjsuB (n := 1)).differentiable one_ne_zero

/-- `sjsuBmin_k ≤ B_k(φ) ≤ sjsuBmax_k` for every `φ`. -/
theorem sjsuB_bounds (φ : Fin 2 → ℝ) (k : Fin 3) :
    (sjsuBmin k : ℝ) ≤ sjsuB φ k ∧ sjsuB φ k ≤ (sjsuBmax k : ℝ) :=
  tubeCenter_bounds_of_globalOK sjsuEcc_globalOK k φ

/-- The tube radius `ρ = 2·10⁻⁶` is below the centre: `ρ < sjsuBmin_k`. -/
theorem sjsu_rho_lt_bmin (k : Fin 3) : (2 / 10 ^ 6 : ℝ) < (sjsuBmin k : ℝ) := by
  have h : (2 / 10 ^ 6 : ℚ) < sjsuBmin k := by
    fin_cases k <;> simp [sjsuBmin, sjsuEccIbar, sjsuEccData] <;> norm_num
  have h' := (Rat.cast_lt (K := ℝ)).2 h
  push_cast at h'
  exact h'

/-! ### The Hamiltonian is smooth -/

/-- The body of `sjsu18O2` over an arbitrary term list is `C^n`. -/
theorem contDiff_polyRe {n : WithTop ℕ∞} (L : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ)) :
    ContDiff ℝ n (fun x : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      let z : Fin 3 → ℂ := fun j => ((x.2 j : ℂ) - Complex.I * (x.1 j : ℂ)) / (Real.sqrt 2 : ℂ)
      ((L.map fun t =>
          ((t.2.2.2.2.2.2 : ℚ) : ℂ) * z 0 ^ t.1 * star (z 0) ^ t.2.1 * z 1 ^ t.2.2.1 *
            star (z 1) ^ t.2.2.2.1 * z 2 ^ t.2.2.2.2.1 * star (z 2) ^ t.2.2.2.2.2.1).sum).re) := by
  have hz : ∀ j : Fin 3, ContDiff ℝ n (fun x : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ((x.2 j : ℂ) - Complex.I * (x.1 j : ℂ)) / (Real.sqrt 2 : ℂ)) := by
    intro j
    have h1 : ContDiff ℝ n (fun x : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (x.2 j : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop)
    have h2 : ContDiff ℝ n (fun x : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (x.1 j : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop)
    exact (h1.sub (contDiff_const.mul h2)).div_const _
  have hzs : ∀ j : Fin 3, ContDiff ℝ n (fun x : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      star (((x.2 j : ℂ) - Complex.I * (x.1 j : ℂ)) / (Real.sqrt 2 : ℂ))) := fun j =>
    Complex.conjCLE.contDiff.comp (hz j)
  have hsum : ContDiff ℝ n (fun x : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      let z : Fin 3 → ℂ := fun j => ((x.2 j : ℂ) - Complex.I * (x.1 j : ℂ)) / (Real.sqrt 2 : ℂ)
      (L.map fun t =>
          ((t.2.2.2.2.2.2 : ℚ) : ℂ) * z 0 ^ t.1 * star (z 0) ^ t.2.1 * z 1 ^ t.2.2.1 *
            star (z 1) ^ t.2.2.2.1 * z 2 ^ t.2.2.2.2.1 * star (z 2) ^ t.2.2.2.2.2.1).sum) := by
    induction L with
    | nil => simpa using contDiff_const
    | cons t L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (((((((contDiff_const.mul ((hz 0).pow _)).mul ((hzs 0).pow _)).mul
        ((hz 1).pow _)).mul ((hzs 1).pow _)).mul ((hz 2).pow _)).mul ((hzs 2).pow _))).add ih
  exact Complex.reCLM.contDiff.comp hsum

/-- **`SJSU18-O2` is smooth** (in particular `C²`, as the confinement theorem needs). -/
theorem contDiff_sjsu18O2 {n : WithTop ℕ∞} : ContDiff ℝ n sjsu18O2 :=
  contDiff_polyRe sjsu18O2Terms

end KAM.EffectiveStability.SJSU

end
