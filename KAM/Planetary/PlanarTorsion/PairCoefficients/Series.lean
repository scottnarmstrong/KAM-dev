/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairCoefficients.Vanish

/-!
# Planar quartic torsion: power series on the unit interval (P11C, package T4)

Power series `∑ w q x ^ q` whose coefficients are bounded: analyticity on `(-1, 1)` and the split
into a finite head and a tail that is again such a series.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

/-- The power series `x ↦ ∑ w q x ^ q`. -/
def p11cSeries (w : ℕ → ℝ) (x : ℝ) : ℝ := ∑' q, w q * x ^ q

/-- Absolute summability of `w q r ^ q` for every `0 ≤ r < 1`. -/
def P11cGood (w : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun q => |w q| * r ^ q

theorem P11cGood.of_bound {w : ℕ → ℝ} (hw : ∀ q, |w q| ≤ 1) : P11cGood w := by
  intro r hr hr1
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    (summable_geometric_of_lt_one hr hr1)
  calc |w q| * r ^ q ≤ 1 * r ^ q := by gcongr; exact hw q
    _ = r ^ q := one_mul _

theorem P11cGood.shift {w : ℕ → ℝ} (hw : P11cGood w) (N : ℕ) : P11cGood fun q => w (q + N) := by
  intro r hr hr1
  have h := (summable_nat_add_iff N).2 (hw r hr hr1)
  have hr' : (r ^ N) ≠ 0 ∨ r = 0 := by
    by_cases h0 : r = 0
    · exact Or.inr h0
    · exact Or.inl (pow_ne_zero _ h0)
  rcases hr' with hN | rfl
  · refine ((h.mul_left (r ^ N)⁻¹).congr fun q => ?_)
    rw [pow_add]; field_simp
  · refine summable_of_ne_finset_zero (s := {0}) fun q hq => ?_
    simp at hq
    simp [zero_pow hq]

theorem P11cGood.summable {w : ℕ → ℝ} (hw : P11cGood w) {x : ℝ} (hx : |x| < 1) :
    Summable fun q => w q * x ^ q := by
  refine Summable.of_norm ((hw |x| (abs_nonneg x) hx).congr fun q => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]

theorem P11cGood.hasFPowerSeriesOnBall {w : ℕ → ℝ} (hw : P11cGood w) :
    HasFPowerSeriesOnBall (p11cSeries w) (FormalMultilinearSeries.ofScalars ℝ w) 0 1 := by
  refine ⟨?_, one_pos, fun {y} hy => ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    refine (hw r r.2 hr1).congr fun q => ?_
    simp
  · rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one] at hy
    have hy' : |y| < 1 := by simpa using hy
    have := (hw.summable hy').hasSum
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add, p11cSeries]
    exact this

theorem P11cGood.analyticAt {w : ℕ → ℝ} (hw : P11cGood w) {x : ℝ} (hx : |x| < 1) :
    AnalyticAt ℝ (p11cSeries w) x :=
  hw.hasFPowerSeriesOnBall.analyticAt_of_mem (by
    rw [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one]; simpa using hx)

theorem P11cGood.split {w : ℕ → ℝ} (hw : P11cGood w) {x : ℝ} (hx : |x| < 1) (N : ℕ) :
    p11cSeries w x =
      (∑ q ∈ Finset.range N, w q * x ^ q) + x ^ N * p11cSeries (fun q => w (q + N)) x := by
  unfold p11cSeries
  rw [← (hw.summable hx).sum_add_tsum_nat_add N, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun q => by rw [pow_add]; ring

end KAM.Planetary
