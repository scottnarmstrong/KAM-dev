/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.LogBounds

/-!
# Fast averaging: the parameter arithmetic (P11A-P5, `stepP:p11:af-o2`)

With `K = 6/(πσ) · log (1/(ε M))`, `α = γ/2 · K^{-τ}`, `s₁ = min r_C (γ/(4 L K^{τ+1}))` and
`d = (min (s₁ σ) r_z)^2` (the signed `p11d1`), the smallness `(S1)`
`2^12 (1+n) K ε M σ ≤ α d` holds for all small `ε`: `K ≤ c₃ log (1/ε)`, `s₁ ≥ c₁ K^{-(τ+1)}`,
`α d ≥ c K^{-(3τ+2)}`, and `ε log (1/ε)^{4(τ+1)} → 0` by `e4`.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

/-- Lower bound for the right-hand side of (S1) in terms of `P = K^{τ+1} ≥ 1`. -/
theorem fast_rhs_lower {γ τ L rC σ rz K : ℝ} (hγ : 0 < γ) (hL : 1 ≤ L)
    (hrC : 0 < rC) (hσ : 0 < σ) (hrz : 0 < rz) (hK : 1 ≤ K) (hτ : 0 < τ) :
    γ * (min (min rC (γ / (4 * L)) * σ) rz) ^ 2 / (2 * (K ^ (τ + 1)) ^ 3) ≤
      γ / 2 * K ^ (-τ) *
        (min (min rC (γ / (4 * L * K ^ (τ + 1))) * σ) rz) ^ 2 := by
  set P : ℝ := K ^ (τ + 1) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow hK (by linarith)
  have hP0 : 0 < P := by linarith
  set q : ℝ := 1 / P with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by rw [hq]; exact div_le_one_of_le₀ hP1 hP0.le
  have hKτ : q ≤ K ^ (-τ) := by
    rw [Real.rpow_neg (by linarith), hq, one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hK (by linarith))
  set c1 : ℝ := min rC (γ / (4 * L)) with hc1
  have hL0 : 0 < L := by linarith
  have hc10 : 0 < c1 := lt_min hrC (by positivity)
  set c2 : ℝ := min (c1 * σ) rz with hc2
  have hc20 : 0 < c2 := lt_min (by positivity) hrz
  have hs1 : c1 * q ≤ min rC (γ / (4 * L * P)) := by
    refine le_min ?_ ?_
    · calc c1 * q ≤ rC * 1 := mul_le_mul (min_le_left _ _) hq1 hq0.le hrC.le
        _ = rC := mul_one _
    · calc c1 * q ≤ γ / (4 * L) * q := mul_le_mul_of_nonneg_right (min_le_right _ _) hq0.le
        _ = γ / (4 * L * P) := by rw [hq]; field_simp
  have hd : c2 * q ≤ min (min rC (γ / (4 * L * P)) * σ) rz := by
    refine le_min ?_ ?_
    · calc c2 * q ≤ (c1 * σ) * q := mul_le_mul_of_nonneg_right (min_le_left _ _) hq0.le
        _ = (c1 * q) * σ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hs1 hσ.le
    · calc c2 * q ≤ rz * 1 := mul_le_mul (min_le_right _ _) hq1 hq0.le hrz.le
        _ = rz := mul_one _
  have hd2 : (c2 * q) ^ 2 ≤ (min (min rC (γ / (4 * L * P)) * σ) rz) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hd 2
  calc γ * c2 ^ 2 / (2 * P ^ 3) = γ / 2 * q * (c2 * q) ^ 2 := by rw [hq]; field_simp
    _ ≤ γ / 2 * K ^ (-τ) * (min (min rC (γ / (4 * L * P)) * σ) rz) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hKτ (by positivity)) hd2 (by positivity)
          (by positivity)

end KAM.Planetary

end
