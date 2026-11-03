/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChart.Symplectic
public import KAM.EffectiveStability.ChartChain

/-!
# The cotangent-lift chart of a Lagrangian graph torus (track B, B5-CHART)

For periodic `u, v` with `‖Du‖ ≤ κ < 1` and `(Dx)ᵀ Dv` symmetric (`x = id + u`), the map
`torusChartMap u v (φ, J) = (x φ, v φ + (Dx φ)^{-T} J)` is a `C²` lattice-equivariant symplectic
bijection of `(Fin n → ℝ) × (Fin n → ℝ)` with inverse `torusChartInvMap u v`, sending the zero
section to the graph `φ ↦ (x φ, v φ)`.

* `TorusChart.Inverse`: the base map `x`, its contraction inverse and `‖(Dx)⁻¹‖ ≤ 1 / (1 - κ)`.
* `TorusChart.Matrix`: the Jacobian matrix and its inverse transpose.
* `TorusChart.Map`: definitions, `C²`, equivariance, mutual inverses.
* `TorusChart.Algebra`, `.Deriv`, `.Symplectic`: the proof of `torusChartMap_symplectic`.
* `torusChart_isCanonical`: the bundled B1 chart premises on the whole space.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set

variable {n : ℕ} {u v : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}

/-- The cotangent-lift chart satisfies the B1 chart premises on the whole phase space. -/
theorem torusChart_isCanonical (h : TorusChartData u v κ) :
    IsCanonicalChart (torusChartMap u v) (torusChartInvMap u v) univ univ :=
  ⟨isOpen_univ, (torusChartMap_contDiff h).contDiffOn, mapsTo_univ _ _,
    fun w _ a b => torusChartMap_symplectic h w a b, fun w _ => torusChartInvMap_map h w⟩

/-- Smoke test: for `u = v = 0` the data are admissible. -/
theorem torusChartData_zero : TorusChartData (n := n) (fun _ => 0) (fun _ => 0) 0 where
  baseSmooth := contDiff_const
  baseContract := zero_lt_one
  baseBound := fun φ => by simp
  uPeriodic := fun _ _ => rfl
  vPeriodic := fun _ _ => rfl
  vSmooth := contDiff_const
  lagrangian := fun φ i j => by simp

/-- Smoke test: for `u = v = 0` the chart is the identity. -/
theorem torusChartMap_zero_data (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    torusChartMap (fun _ => 0) (fun _ => (0 : Fin n → ℝ)) w = w := by
  have hx : torusChartX (n := n) (fun _ => 0) = id := funext fun φ => by simp [torusChartX]
  have hJ : ∀ φ, torusChartJac (n := n) (fun _ => 0) φ = 1 := fun φ => by
    ext i j
    simp [torusChartJac, hx, Pi.single_apply, Matrix.one_apply]
  have hB : ∀ φ, torusChartInvT (n := n) (fun _ => 0) φ = 1 := fun φ => by
    simp [torusChartInvT, hJ]
  obtain ⟨φ, J⟩ := w
  simp [torusChartMap, hx, hB]

end KAM.EffectiveStability
