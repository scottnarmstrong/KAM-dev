/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Frozen.Planetary.Defs.OrbitalUnit

/-!
# Secular form: even jet of the circle mean of an analytic function

Blueprint P, Part 8, `stepP:p8:qf-diag` ("only even powers of `e cos u` survive and
`⟨cos²⟩ = 1/2`"): for `H` analytic at `0`, the mean `(2π)⁻¹ ∫₀^{2π} H(v·e(F)) dF` over the unit
circle equals `H(0) + H''(0) e²/4 + H⁗(0) e⁴/64 + O(e⁶)` with `e = |v|`
(`⟨cos⁴⟩ = 3/8`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

private theorem planeSq_two'' (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem planeDot_two'' (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

/-- `v · e(F) = |v| cos (F - θ)` for a fixed phase `θ`. -/
theorem planeDot_orbitalUnit_polar (v : Fin 2 → ℝ) :
    ∃ θ : ℝ, ∀ F : ℝ, planeDot v (orbitalUnit F) = planeLength v * Real.cos (F - θ) := by
  set z : ℂ := ⟨v 0, v 1⟩ with hz
  have hr : planeLength v = ‖z‖ := by
    rw [Complex.norm_def, Complex.normSq_apply, planeLength, planeSq_two'']
    simp [hz, sq]
  refine ⟨Complex.arg z, fun F => ?_⟩
  have h0 : v 0 = ‖z‖ * Real.cos (Complex.arg z) := by simp [hz]
  have h1 : v 1 = ‖z‖ * Real.sin (Complex.arg z) := by simp [hz]
  rw [planeDot_two'', hr, Real.cos_sub]
  simp only [orbitalUnit, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h0, h1]
  ring

/-- Means of the powers of the cosine over one period (`k ≤ 5`). -/
theorem integral_cos_pow_period (k : ℕ) (hk : k ≤ 5) :
    ∫ x in (0:ℝ)..2 * π, Real.cos x ^ k =
      if k = 0 then 2 * π else if k = 2 then π else if k = 4 then 3 * π / 4 else 0 := by
  have hrec : ∀ n : ℕ, ∫ x in (0:ℝ)..2 * π, Real.cos x ^ (n + 2) =
      ((n : ℝ) + 1) / ((n : ℝ) + 2) * ∫ x in (0:ℝ)..2 * π, Real.cos x ^ n := fun n => by
    rw [integral_cos_pow]; simp
  have h0 : ∫ x in (0:ℝ)..2 * π, Real.cos x ^ 0 = 2 * π := by simp
  have h1 : ∫ x in (0:ℝ)..2 * π, Real.cos x ^ 1 = 0 := by simp
  have h2 : ∫ x in (0:ℝ)..2 * π, Real.cos x ^ 2 = π := by
    have := hrec 0
    simp only [zero_add, Nat.cast_zero] at this
    rw [this, h0]; ring
  have h3 : ∫ x in (0:ℝ)..2 * π, Real.cos x ^ 3 = 0 := by
    simp
  have h4 : ∫ x in (0:ℝ)..2 * π, Real.cos x ^ 4 = 3 * π / 4 := by
    have := hrec 2
    rw [show (2 : ℕ) + 2 = 4 from rfl, h2] at this
    rw [this]; push_cast; ring
  have h5 : ∫ x in (0:ℝ)..2 * π, Real.cos x ^ 5 = 0 := by
    have := hrec 3
    rw [show (3 : ℕ) + 2 = 5 from rfl, h3] at this
    simpa using this
  interval_cases k <;> simp_all

/-- The `k`-th term of the power series of an analytic function at `0`, on the diagonal. -/
theorem powerSeries_diag {H : ℝ → ℝ} {p : FormalMultilinearSeries ℝ ℝ ℝ} {r : ENNReal}
    (hp : HasFPowerSeriesOnBall H p 0 r) (k : ℕ) (y : ℝ) :
    p k (fun _ => y) = iteratedDeriv k H 0 / k.factorial * y ^ k := by
  have h1 := hp.factorial_smul 1 k
  have h2 : p k (fun _ => y) = y ^ k * p k (fun _ => (1:ℝ)) := by
    simp [smul_eq_mul]
  rw [h2, iteratedDeriv_eq_iteratedFDeriv, ← h1, nsmul_eq_mul]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Taylor bound of order `6` for an analytic function at `0`, with continuity on the ball. -/
theorem analytic_taylor_bound {H : ℝ → ℝ} (hH : AnalyticAt ℝ H 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ y : ℝ, |y| < r → ContinuousAt H y ∧
      |H y - ∑ k ∈ Finset.range 6, iteratedDeriv k H 0 / k.factorial * y ^ k| ≤ C * |y| ^ 6 := by
  obtain ⟨p, r0, hp⟩ := id hH
  have hat : HasFPowerSeriesAt H p 0 := ⟨r0, hp⟩
  have hbig := hat.isBigO_sub_partialSum_pow 6
  obtain ⟨C, hCpos, hC⟩ := hbig.exists_pos
  have hev1 := hC.bound
  have hev2 : ∀ᶠ y in 𝓝 (0:ℝ), AnalyticAt ℝ H y := hH.eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
  refine ⟨r, C, hr, hCpos, fun y hy => ?_⟩
  have hy' : dist y 0 < r := by simpa using hy
  obtain ⟨h1, h2⟩ := hball hy'
  refine ⟨h2.continuousAt, ?_⟩
  have hs : p.partialSum 6 y = ∑ k ∈ Finset.range 6, iteratedDeriv k H 0 / k.factorial * y ^ k := by
    unfold FormalMultilinearSeries.partialSum
    exact Finset.sum_congr rfl fun k _ => powerSeries_diag hp k y
  rw [← hs]
  simpa [Real.norm_eq_abs, zero_add] using h1

end SecularForm
end KAM.Planetary
end
