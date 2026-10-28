/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.DiagonalJet.Radial
public import KAM.Planetary.Poincare.Chart
public import KAM.Kepler.Equation

/-!
# Secular form: radius of the regular orbit map and the circular partner

Blueprint P, Part 8, `stepP:p8:qf-diag` (and `stepP:p8:qf-c0`): from the regular orbit map
`poincare` one gets `|q| = a (1 - v·e(F))` (the Kepler radius `a(1 - e cos u)`), a circular
planet (`ξ = η = 0`) has position `a e(λ)`, and the average of the inverse distance to a
circular planet of radius `b` over its longitude is `Φ(|q|, b)`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

private theorem planeSq_two (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem planeDot_two (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

/-- Algebra of the position vector of the regular orbit map: it has squared length `(1-x)²`. -/
theorem planeSq_orbit_vec {K : ℝ} {v : Fin 2 → ℝ} (F : ℝ) (hv : planeSq v = 1 - K ^ 2)
    (hK : 0 < K) :
    planeSq (K • orbitalUnit F - v + (planeDot v (orbitalUnit F) / (1 + K)) • v) =
      (1 - planeDot v (orbitalUnit F)) ^ 2 := by
  rw [planeSq_two] at hv
  rw [planeSq_two]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, orbitalUnit,
    Matrix.cons_val_zero, Matrix.cons_val_one, planeDot_two]
  have hK1 : (1 + K) ≠ 0 := by positivity
  have hc := Real.cos_sq_add_sin_sq F
  field_simp
  linear_combination
    (K ^ 4 + 2 * K ^ 3 + K ^ 2 * v 0 ^ 2 + K ^ 2 + v 0 ^ 4 + v 0 ^ 2 * v 1 ^ 2 - v 0 ^ 2) * hc +
    (K ^ 2 - 2 * K * Real.cos F * v 0 - 2 * K * Real.sin F * v 1 + 2 * K +
      2 * Real.cos F * Real.sin F * v 0 * v 1 - 2 * Real.cos F * v 0 - Real.sin F ^ 2 * v 0 ^ 2 +
      Real.sin F ^ 2 * v 1 ^ 2 - 2 * Real.sin F * v 1 + v 0 ^ 2 + 1) * hv

/-- `stepP:p8:qf-diag`: the radius of the regular orbit map is `a · J(F, v)` (`J = 1 - v·e(F)`). -/
theorem planeLength_poincare_fst {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ poincareDom) :
    planeLength (poincare m κ w).1 =
      w.2 0 ^ 2 / (m ^ 2 * κ) * keplerJac (poincareV w) (poincareF w) := by
  obtain ⟨-, hK, -, -, hsq, -, hJ⟩ := poincare_facts hw
  have hc : 0 < w.2 0 ^ 2 / (m ^ 2 * κ) := div_pos (pow_pos hw.1 2) (by positivity)
  have h := planeSq_orbit_vec (K := poincareK w) (v := poincareV w) (poincareF w) hsq hK
  unfold poincare
  simp only
  rw [planeLength_smul, abs_of_pos hc]
  congr 1
  unfold planeLength
  rw [h]
  unfold keplerJac at hJ ⊢
  exact Real.sqrt_sq hJ.le

end SecularForm
end KAM.Planetary
end
