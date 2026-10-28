/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.PairSplit
public import KAM.Planetary.SecularForm.CrossJet.Parametric

/-!
# Quadratic part: the two-planet secular function is the literal pair average

Blueprint P, Part 8, `stepP:p8:qf-pair` (package S8-Q). Away from collisions the two-planet secular
function `secular (pairData D i j) false (pairSlow x i j)` is the iterated interval integral
`pairSlowSecular` of `DiagonalJet`/`CrossJet`; `pairSlowSecular` is symmetric under exchanging the
two planets.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

theorem secular_pair_eq (D : Data n) {x : Slow n} (hx : x ∈ slowDom D) {i j : Fin n}
    (hsep : ∀ s s' : ℝ, pairPos D x i s ≠ pairPos D x j s') :
    secular (pairData D i j) false (pairSlow x i j) =
      pairSlowSecular D i j (x.2.1 i) (x.2.1 j) (![x.1 i, x.2.2 i], ![x.1 j, x.2.2 j]) := by
  rw [secular_eq_avg]
  simp only [perturbation_pair_eq]
  unfold avg
  rw [smul_eq_mul, integral_cell_two (continuous_pairTerm D hx hsep).continuousOn]
  unfold pairSlowSecular
  simp only [intervalIntegral.integral_const_mul, pairTerm, pairPos, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h : (2 * π : ℝ) ^ (-((2 : ℕ) : ℤ)) = (2 * π)⁻¹ * (2 * π)⁻¹ := by
    rw [zpow_neg, zpow_natCast]; ring
  rw [h]
  ring

/-- Exchanging the two planets in the literal pair average. -/
theorem pairSlowSecular_swap (D : Data n) (i j : Fin n) {I J : ℝ} (u v : Fin 2 → ℝ)
    (hc : Continuous fun p : ℝ × ℝ => -D.G * D.m i * D.m j / planeLength
      ((poincare (D.m i) (D.G * D.m0) (![p.1, u 0], ![I, u 1])).1 -
        (poincare (D.m j) (D.G * D.m0) (![p.2, v 0], ![J, v 1])).1)) :
    pairSlowSecular D j i J I (v, u) = pairSlowSecular D i j I J (u, v) := by
  set f : ℝ × ℝ → ℝ := fun p => -D.G * D.m i * D.m j / planeLength
      ((poincare (D.m i) (D.G * D.m0) (![p.1, u 0], ![I, u 1])).1 -
        (poincare (D.m j) (D.G * D.m0) (![p.2, v 0], ![J, v 1])).1) with hf
  have hsw : ∀ s t : ℝ, -D.G * D.m j * D.m i / planeLength
      ((poincare (D.m j) (D.G * D.m0) (![s, v 0], ![J, v 1])).1 -
        (poincare (D.m i) (D.G * D.m0) (![t, u 0], ![I, u 1])).1) = f (t, s) := by
    intro s t
    simp only [hf]
    rw [planeLength_sub_comm]
    ring_nf
  unfold pairSlowSecular
  simp only [hsw]
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hcc : ContinuousOn (fun p : ℝ × ℝ => f (p.2, p.1)) (Icc 0 (2 * π) ×ˢ Icc 0 (2 * π)) :=
    (hc.comp continuous_swap).continuousOn
  have hint : Integrable (uncurry fun s t : ℝ => f (t, s))
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hcc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have key : ∫ s in Ioc 0 (2 * π), ∫ t in Ioc 0 (2 * π), f (t, s) =
      ∫ s in Ioc 0 (2 * π), ∫ t in Ioc 0 (2 * π), f (s, t) := integral_integral_swap hint
  simp only [intervalIntegral.integral_const_mul]
  congr 2
  simp only [intervalIntegral.integral_of_le h2π]
  exact key

end SecularForm
end KAM.Planetary
end
