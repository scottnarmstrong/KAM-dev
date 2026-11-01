/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.NhatTaylor
public import KAM.Wave.Homological.TaylorSub
public import KAM.Wave.Homological.Lemma1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The frequency corrections of the step (blueprint-W `bpW:w5:step` (iii))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

For a Taylor element `R` put `ω̂ = Re [b]` and `Ω̂_j = Re [Q]_{jj}` (the real parts of the zeroth Fourier
coefficients; they are the coefficients of `N̂`, real when `R` is real). `stepOmegaHat_bound`,
`stepOmegaTail_bound` give the bounds `|ω̂| ≤ 2π ε`, `(j+2)^{p_+-p}|Ω̂_j| ≤ ε` from a `HomFieldBound` with
constant `ε`, and the same for the difference of two elements with the Lipschitz constant.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- `ω̂ = Re [b]`. -/
def stepOmegaHat (R : HomTaylor_gen a p pb s) : Fin 2 → ℝ := fun k => (homCoeff R.b 0 k).re

/-- `Ω̂_j = Re [Q]_{jj}`. -/
def stepOmegaTail (R : HomTaylor_gen a p pb s) : ℕ+ → ℝ :=
  fun j => (homNormalEntry_gen a p pb (homCoeff R.Q 0) j j).re

theorem stepOmegaHat_bound (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 < r)
    (hs : 0 < s) (R : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε R) :
    ‖stepOmegaHat R‖ ≤ 2 * Real.pi * ε := by
  have h := (homNhat_coeff_bounds_gen ha hp hpb hr hs R hX).1
  have hε : 0 ≤ 2 * Real.pi * ε := (norm_nonneg _).trans h
  refine (pi_norm_le_iff_of_nonneg hε).2 fun k => ?_
  have h1 : ‖homCoeff R.b 0 k‖ ≤ 2 * Real.pi * ε := (norm_le_pi_norm _ k).trans h
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans h1

theorem stepOmegaTail_bound (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {r ε : ℝ} (hr : 0 < r)
    (hs : 0 < s) (R : HomTaylor_gen a p pb s) (hX : HomFieldBound_gen ha hp hpb r ε R) (j : ℕ+) :
    ((j : ℝ) + 2) ^ (pb - p) * |stepOmegaTail R j| ≤ ε := by
  have h := (homNhat_coeff_bounds_gen ha hp hpb hr hs R hX).2.2 j
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) h
  exact Complex.abs_re_le_norm _

/-- The differences: `ω̂(R₁) - ω̂(R₂) = ω̂(R₁ - R₂)`. -/
theorem stepOmegaHat_sub (hs : 0 < s) (R₁ R₂ : HomTaylor_gen a p pb s) :
    stepOmegaHat R₁ - stepOmegaHat R₂ = stepOmegaHat (R₁.homSub R₂) := by
  funext k
  have := congrFun (homCoeff_sub_banach hs R₁.comp_b.1 R₂.comp_b.1 0) k
  simp only [stepOmegaHat, Pi.sub_apply, ← Complex.sub_re]
  rw [Pi.sub_apply] at this
  rw [← this]
  rfl

theorem stepOmegaTail_sub (hs : 0 < s) (R₁ R₂ : HomTaylor_gen a p pb s) (j : ℕ+) :
    stepOmegaTail R₁ j - stepOmegaTail R₂ j = stepOmegaTail (R₁.homSub R₂) j := by
  have := homCoeff_sub_banach hs R₁.comp_Q.1 R₂.comp_Q.1 0
  simp only [stepOmegaTail, ← Complex.sub_re, ← homNormalEntry_sub_gen]
  have e : homCoeff (R₁.homSub R₂).Q 0 = homCoeff R₁.Q 0 - homCoeff R₂.Q 0 := this
  rw [e]

end KAM.Wave
