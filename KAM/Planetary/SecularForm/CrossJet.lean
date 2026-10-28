/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.CrossJet.Selection
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularForm.AnalyticGeometry

/-!
# Secular form: the cross jet of the pair average

Blueprint P, Part 8, `stepP:p8:qf-cross` (package S8-X). The mixed second derivative at
`ξ_i = ξ_j = 0` of the literal pair average `pairSlowSecular` is the Hermitian entry of the
quadratic form: `cross_hessian` states `∂_{ξ_i}∂_{ξ_j} S_{ij} = 2 · coeffs D a i j`, with the value
recomputed from the regular orbit map (`hasDerivAt_poincare_fst_xi`), differentiation under the
double angle average (`pairSlowSecular_mixed_jet`) and the Fourier selection
(`cross_double_average`). The matrix `coeffs` is never assumed.

This file is the public facade of the `CrossJet/` modules (`Variation`, `Parametric`,
`PairIntegrand`, `MixedKernel`, `PairAverage`, `Selection`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric KAM KAM.Kepler
open scoped Topology ContDiff
namespace KAM.Planetary
namespace SecularForm
variable {n : ℕ}

theorem crossKernel_smul (c p q : ℝ) (d x z : Fin 2 → ℝ) :
    crossKernel c d (p • x) (q • z) = c * p * q * crossKernel 1 d x z := by
  unfold crossKernel
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `stepP:p8:qf-cross`: the cross Hessian of the literal pair average at `ξ = 0` is twice the
off-diagonal coefficient `coeffs D a i j` (the first Laplace-coefficient identity is not used; the
value is recomputed from the orbit map). -/
theorem cross_hessian (D : Data n) {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i < j) :
    iteratedFDeriv ℝ 2 (fun y : Vec 2 => pairSlowSecular D i j (action D a i) (action D a j)
        (![y 0, 0], ![y 1, 0])) 0 ![Pi.single 0 1, Pi.single 1 1] = 2 * coeffs D a i j := by
  have hI := action_pos D ha i
  have hJ := action_pos D ha j
  have hai : a i < a j := ha.2 hij
  have hsep : action D a i ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) <
      action D a j ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) := by
    rw [action_sq_div D ha i, action_sq_div D ha j]; exact hai
  rw [pairSlowSecular_mixed_jet D i j hI hJ hsep]
  simp only [action_sq_div D ha i, action_sq_div D ha j]
  have hint : ∀ s t : ℝ, crossKernel (D.G * D.m i * D.m j)
      (a i • cvec s - a j • cvec t) ((a i / √(action D a i)) • uvec s)
      ((a j / √(action D a j)) • uvec t) =
      (D.G * D.m i * D.m j * (a i / √(action D a i)) * (a j / √(action D a j))) *
        crossU (a i) (a j) s t := by
    intro s t
    rw [crossKernel_smul]
    rfl
  have hc := cross_double_average (ha.1 i) hai
  simp only [intervalIntegral.integral_const_mul] at hc
  simp only [hint, intervalIntegral.integral_const_mul]
  have hcoef : coeffs D a i j = D.G * D.m i * D.m j * a i / (4 * a j ^ 2) *
      laplace_def (3 / 2) 2 (a i / a j) / (√(action D a i) * √(action D a j)) := by
    unfold coeffs qhat pairB
    simp only [ne_of_lt hij, ↓reduceIte, min_eq_left hij.le, max_eq_right hij.le]
  rw [hcoef]
  have hsI : 0 < √(action D a i) := Real.sqrt_pos.2 hI
  have hsJ : 0 < √(action D a j) := Real.sqrt_pos.2 hJ
  have haj := (ha.1 j)
  calc _ = (D.G * D.m i * D.m j * (a i / √(action D a i)) * (a j / √(action D a j))) *
        ((2 * π)⁻¹ * ((2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, ∫ t in (0:ℝ)..2 * π, crossU (a i) (a j) s
            t)) := by
        ring
    _ = _ := by
        rw [hc]
        field_simp
        ring

end SecularForm
end KAM.Planetary
