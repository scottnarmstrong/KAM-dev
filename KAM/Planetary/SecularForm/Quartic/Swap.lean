/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.PairSymmetry

/-!
# Secular form: exchanging the two planets of a pair

Blueprint P, Part 8, `stepP:p8:q4-b`: for continuous kernels the two normalised integrals of the pair
average may be exchanged, so the pair average with the first planet circular is the pair average of
the exchanged pair with the second planet circular.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

/-- The two normalised integrals of a continuous kernel on the square may be exchanged. -/
theorem double_integral_swap {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc 0 (2 * π) ×ˢ Icc 0 (2 * π))) :
    (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π, g s t =
      (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, (2 * π)⁻¹ * ∫ t in (0:ℝ)..2 * π, g t s := by
  have hg' : ContinuousOn (fun p : ℝ × ℝ => g p.2 p.1) (Icc 0 (2 * π) ×ˢ Icc 0 (2 * π)) := by
    have := hg.comp continuous_swap.continuousOn (t := Icc 0 (2 * π) ×ˢ Icc 0 (2 * π))
      (s := Icc 0 (2 * π) ×ˢ Icc 0 (2 * π)) fun p hp => ⟨hp.2, hp.1⟩
    exact this
  have h1 := avg_pair (n := 2) (j := 0) (k := 1) (by decide) hg
  have h2 := avg_pair (n := 2) (j := 1) (k := 0) (by decide) (g := fun s t => g t s) hg'
  rw [← h1, ← h2]

/-- The kernel of the literal pair average. -/
def quarticPairKernel (D : Data n) (i j : Fin n) (I J : ℝ) (w : PairW) (s t : ℝ) : ℝ :=
  -D.G * D.m i * D.m j / planeLength
    ((poincare (D.m i) (D.G * D.m0) (![s, w.1 0], ![I, w.1 1])).1 -
      (poincare (D.m j) (D.G * D.m0) (![t, w.2 0], ![J, w.2 1])).1)

theorem pairSlowSecular_eq_kernel (D : Data n) (i j : Fin n) (I J : ℝ) (w : PairW) :
    pairSlowSecular D i j I J w = (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, (2 * π)⁻¹ *
      ∫ t in (0:ℝ)..2 * π, quarticPairKernel D i j I J w s t := rfl

theorem pairKernel_eq_quarticPairKernel (D : Data n) (i j : Fin n) (I J : ℝ) (w : PairW)
    (s t : ℝ) :
    pairKernel (pairData D i j) (pairEmb ((I, J), w)) 0 1 s t = quarticPairKernel D i j I J w s t := by
  simp [pairKernel, quarticPairKernel, ppos, blk, pairEmb_apply, pairData]

/-- Exchanging the two planets of a pair. -/
theorem pairSlowSecular_swap (D : Data n) (i j : Fin n) (I J : ℝ) (u : Fin 2 → ℝ)
    (hc : Continuous fun q : ℝ × ℝ => quarticPairKernel D i j I J (0, u) q.1 q.2) :
    pairSlowSecular D j i J I (u, 0) = pairSlowSecular D i j I J (0, u) := by
  have hk : ∀ s t, quarticPairKernel D j i J I (u, 0) s t = quarticPairKernel D i j I J (0, u) t s := by
    intro s t
    simp only [quarticPairKernel]
    have : ∀ x y : Fin 2 → ℝ, planeLength (x - y) = planeLength (y - x) := fun x y => by
      unfold planeLength planeSq
      congr 1
      refine Finset.sum_congr rfl fun k _ => by simp; ring
    rw [this]
    ring_nf
  rw [pairSlowSecular_eq_kernel, pairSlowSecular_eq_kernel]
  simp_rw [hk]
  exact (double_integral_swap (g := quarticPairKernel D i j I J (0, u))
    hc.continuousOn).symm

end SecularForm
end KAM.Planetary
end
