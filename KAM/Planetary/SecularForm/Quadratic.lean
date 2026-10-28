/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.Constants

/-!
# Secular form: the quadratic part of the secular function

Blueprint P, Part 8, `bpP:p8:quadratic-form` (package S8-Q), with the proof cuts `stepP:p8:qf-pair`,
`qf-assembly` and `qf-diag2`.

`quadratic_form`: near `action D a`, the secular function of the fixed model is
`C₀(a(Λ)) + ξᵀ Q_h ξ + ηᵀ Q_h η + O(|(ξ, η)|⁴)`, the error real analytic and `O(|(ξ, η)|⁴)` locally
uniformly in `Λ`, with `Q_h = coeffs D (axis D Λ)`. The matrix is never assumed: the pair
decomposition (`secular_eq_sum_pair`) writes the secular function as the sum of the literal pair
averages `pairSlowSecular`, whose values, diagonal second derivatives (S8-D) and cross second
derivative (S8-X) are summed by `quad_pair_sum`; the remaining mixed second derivatives follow from
the reflection and quarter-turn symmetries (S8-Y, `hessian_pair_form`); the uniform bound is the
Schwarz lemma of order four on the complex line through `(ξ, Λ, η)` (`remainder_pointwise`).

The modules of the proof are in `Quadratic/`: `Marginal`, `PairSplit`, `PairIdentify`,
`PairLocal`, `Calculus`, `PairDiag`, `PairHessian`, `Algebra`, `Coeff`, `Jet`, `Schwarz`, `Uniform`
and `Constants`. The diagonalisation cut `stepP:p8:qf-diag2` is the matrix-level statement consumed
by S9-Q; it is not a separate analytic fact (the quadratic form is the sum `ξᵀ Q ξ + ηᵀ Q η`
exactly as stated).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

/-- Explicit local uniform O(u^4), and the same analytic remainder. -/
theorem quadratic_form (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r C : ℝ, 0 < r ∧ r < rho D a ∧ 0 < C ∧
    AnalyticOnNhd ℝ (fun x : Slow n => secular D false x - constantTerm D (axis D x.2.1) -
      quad (coeffs D (axis D x.2.1)) x.1 - quad (coeffs D (axis D x.2.1)) x.2.2)
      (realDisc D a r) ∧
    ∀ x ∈ realDisc D a r, |secular D false x - constantTerm D (axis D x.2.1) -
      quad (coeffs D (axis D x.2.1)) x.1 - quad (coeffs D (axis D x.2.1)) x.2.2| ≤
      C * ‖(x.1,x.2.2)‖^4 := by
  obtain ⟨r0, r, M1, MT, ME, hr, hrr0, hrho0, hSD, hreal, hAn, hM1, hK⟩ :=
    exists_remainder_constants D ha
  have hrr : 0 < r ^ 4 := by positivity
  refine ⟨r, |(M1 + MT + 2 * r ^ 2 * ME) / r ^ 4| + 1, hr, hrr0.trans hrho0, by positivity, ?_, ?_⟩
  · intro x hx
    have hxΛ : dist x.2.1 (action D a) < r := by
      rw [dist_pi_lt_iff hr]
      intro i; rw [Real.dist_eq]; exact (realDisc_coord D a hx i).2.1
    exact analyticAt_remainder D (hAn x (realDisc_mono D a hrr0.le hx)) (hK _ hxΛ).1
  · intro x hx
    have h := remainder_pointwise D ha hr hrr0 hrho0 hSD hreal hM1 hK hx
    have hn : 0 ≤ ‖(x.1, x.2.2)‖ ^ 4 := by positivity
    calc |secular D false x - constantTerm D (axis D x.2.1) -
          quad (coeffs D (axis D x.2.1)) x.1 - quad (coeffs D (axis D x.2.1)) x.2.2|
        = |quadRemainder D x| := rfl
      _ ≤ (M1 + MT + 2 * r ^ 2 * ME) / r ^ 4 * ‖(x.1, x.2.2)‖ ^ 4 := h
      _ ≤ |(M1 + MT + 2 * r ^ 2 * ME) / r ^ 4| * ‖(x.1, x.2.2)‖ ^ 4 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hn
      _ ≤ (|(M1 + MT + 2 * r ^ 2 * ME) / r ^ 4| + 1) * ‖(x.1, x.2.2)‖ ^ 4 :=
          mul_le_mul_of_nonneg_right (by linarith) hn

end SecularForm
end KAM.Planetary
end
