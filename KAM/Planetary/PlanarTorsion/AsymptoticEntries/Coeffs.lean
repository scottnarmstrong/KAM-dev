/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.CoeffEq
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Inputs

/-!
# Planar quartic torsion: sizes of the quartic coefficients (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, step `stepP:p11b:as-c`): at `a = ![α, 1]` with
`g₀ = 1 / m₀`,
`c₁ = (3 g₀ m₂ / (32 m₁)) α (1 + O(α²))`, `c₂ = -(3 g₀ m₁ / (8 m₂)) α² (1 + O(α²))`,
`c₃ = -(9 g₀ / 16) α ^ (3/2) (1 + O(α²))`, `c₄ = O(α ^ (7/2))`, `c₅ = O(α ^ (9/4))`,
`c₆ = O(α ^ (11/4))`; the relative errors are kept in the absolute form
`leading + O(α ^ (leading exponent + 2))`.  Here `m₁, m₂` are `p.m 0, p.m 1`.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

/-- `A₂ - A₀ / 4 = -(3/32) α² + O(α⁴)`. -/
theorem p11cAe_X0 : (fun a => (p11c_pairCoeffs a 2 - p11c_pairCoeffs a 0 / 4) + 3 / 32 * a ^ 2)
    =O[𝓝[>] 0] fun a : ℝ => a ^ (4 : ℝ) := by
  have h1 : (fun a => p11c_pairCoeffs a 2) =O[𝓝[>] 0] fun a : ℝ => a ^ (4 : ℝ) :=
    p11cAe_lead_isBigO (c := 135 / 512) (r := 4) (s := 6) (by norm_num) (by simpa using p11cAe_p1)
  exact (h1.sub (p11cAe_A.const_mul_left (1 / 4))).congr_left fun a => by ring

/-- `A₃ - A₀ / 4 = (3/8) α² + O(α⁴)`. -/
theorem p11cAe_X1 : (fun a => (p11c_pairCoeffs a 3 - p11c_pairCoeffs a 0 / 4) - 3 / 8 * a ^ 2)
    =O[𝓝[>] 0] fun a : ℝ => a ^ (4 : ℝ) := by
  have h1 := p11cAe_p2
  exact (h1.sub (p11cAe_A.const_mul_left (1 / 4))).congr_left fun a => by ring

theorem p11cAe_X3 : (fun a => p11c_pairCoeffs a 5) =O[𝓝[>] 0] fun a : ℝ => a ^ (4 : ℝ) :=
  p11cAe_lead_isBigO (c := 315 / 128) (r := 4) (s := 6) (by norm_num) (by simpa using p11cAe_p4)

theorem p11cAe_A6 : (fun a => p11c_pairCoeffs a 6) =O[𝓝[>] 0] fun a : ℝ => a ^ (3 : ℝ) :=
  p11cAe_lead_isBigO' (c := 45 / 64) (r := 3) (s := 5) (by norm_num) (by simpa using p11cAe_p5)

theorem p11cAe_A7 : (fun a => p11c_pairCoeffs a 7) =O[𝓝[>] 0] fun a : ℝ => a ^ (3 : ℝ) :=
  p11cAe_lead_isBigO' (c := 75 / 32) (r := 3) (s := 5) (by norm_num) (by simpa using p11cAe_p6)

theorem p11cAe_A1 : (fun a => p11c_pairCoeffs a 1) =O[𝓝[>] 0] fun a : ℝ => a ^ (3 : ℝ) :=
  p11cAe_lead_isBigO' (c := 15 / 16) (r := 3) (s := 5) (by norm_num) (by simpa using p11cAe_B)

theorem p11cAe_X4 : (fun a => p11c_pairCoeffs a 6 - p11c_pairCoeffs a 1 / 8) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (3 : ℝ) := p11cAe_A6.sub (p11cAe_A1.const_mul_left (1 / 8)) |>.congr_left
  fun a => by ring

theorem p11cAe_X5 : (fun a => p11c_pairCoeffs a 7 - p11c_pairCoeffs a 1 / 8) =O[𝓝[>] 0]
    fun a : ℝ => a ^ (3 : ℝ) := p11cAe_A7.sub (p11cAe_A1.const_mul_left (1 / 8)) |>.congr_left
  fun a => by ring

/-- `bpP:p11b:asymptotics`, step `as-c`: sizes of the six quartic coefficients at `a = ![α, 1]`. -/
theorem as_c (p : PlanarData) (hp : p.Valid) :
    (fun α => p11c_coeffs p ![α, 1] 0 - 3 * p.m 1 / (32 * p.m0 * p.m 0) * α)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (3 : ℝ)) ∧
      (fun α => p11c_coeffs p ![α, 1] 1 + 3 * p.m 0 / (8 * p.m0 * p.m 1) * α ^ (2 : ℝ))
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) ∧
      (fun α => p11c_coeffs p ![α, 1] 2 + 9 / (16 * p.m0) * α ^ (3 / 2 : ℝ))
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) ∧
      (fun α => p11c_coeffs p ![α, 1] 3) =O[𝓝[>] 0] (fun α : ℝ => α ^ (7 / 2 : ℝ)) ∧
      (fun α => p11c_coeffs p ![α, 1] 4) =O[𝓝[>] 0] (fun α : ℝ => α ^ (9 / 4 : ℝ)) ∧
      (fun α => p11c_coeffs p ![α, 1] 5) =O[𝓝[>] 0] (fun α : ℝ => α ^ (11 / 4 : ℝ)) ∧
      (fun α => (p11c_pairCoeffs α 2 - p11c_pairCoeffs α 0 / 4) + 3 / 32 * α ^ 2)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) ∧
      (fun α => (p11c_pairCoeffs α 3 - p11c_pairCoeffs α 0 / 4) - 3 / 8 * α ^ 2)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) ∧
      (fun α => p11c_pairCoeffs α 4 - 9 / 16 * α ^ 2) =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) ∧
      (fun α => p11c_pairCoeffs α 5) =O[𝓝[>] 0] (fun α : ℝ => α ^ (4 : ℝ)) ∧
      (fun α => p11c_pairCoeffs α 6 - p11c_pairCoeffs α 1 / 8)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (3 : ℝ)) ∧
      (fun α => p11c_pairCoeffs α 7 - p11c_pairCoeffs α 1 / 8)
        =O[𝓝[>] 0] (fun α : ℝ => α ^ (3 : ℝ)) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hG := hp.1
  have hm0' := hp.2.1
  have hm0 := hp.2.2 0
  have hm1 := hp.2.2 1
  have hκ : p.kappa = p.G * p.m0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, p11cAe_X0, p11cAe_X1, p11cAe_p3, p11cAe_X3, p11cAe_X4,
    p11cAe_X5⟩
  · have h := (p11cAe_div (f := fun a => (p11c_pairCoeffs a 2 - p11c_pairCoeffs a 0 / 4) +
      3 / 32 * a ^ 2) (r := 3) (by rw [show (3 : ℝ) + 1 = 4 by norm_num]; exact p11cAe_X0)
      ).const_mul_left (-(p.G * p.m 1 / (p.m 0 * p.kappa)))
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    rw [p11cAe_c0_eq p hp ha, hκ]
    field_simp
    ring
  · have h := (p11cAe_congr_exp (r := 4) (s := 4) rfl p11cAe_X1).const_mul_left
      (-(p.G * p.m 0 / (p.m 1 * p.kappa)))
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    rw [p11cAe_c1_eq p hp ha, Real.rpow_two, hκ]
    field_simp
    ring
  · have h := p11cAe_congr_exp (s := 7 / 2) (by norm_num) ((p11cAe_mul p11cAe_p3
      (isBigO_refl (fun a : ℝ => a ^ (-(1 / 2) : ℝ)) (𝓝[>] 0))).const_mul_left
      (-(p.G / p.kappa)))
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    have e : a ^ (3 / 2 : ℝ) = a ^ 2 * a ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ha]; norm_num
    rw [p11cAe_c2_eq p hp ha, e, hκ]
    field_simp
    ring
  · have h := p11cAe_congr_exp (s := 7 / 2) (by norm_num) ((p11cAe_mul p11cAe_X3
      (isBigO_refl (fun a : ℝ => a ^ (-(1 / 2) : ℝ)) (𝓝[>] 0))).const_mul_left
      (-(p.G / p.kappa)))
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    rw [p11cAe_c3_eq p hp ha]
  · obtain ⟨K, hK⟩ := p11cAe_c4_eq p hp
    have h := p11cAe_congr_exp (s := 9 / 4) (by norm_num) ((p11cAe_mul p11cAe_X4
      (isBigO_refl (fun a : ℝ => a ^ (-(3 / 4) : ℝ)) (𝓝[>] 0))).const_mul_left K)
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    rw [hK a ha]
  · obtain ⟨K, hK⟩ := p11cAe_c5_eq p hp
    have h := p11cAe_congr_exp (s := 11 / 4) (by norm_num) ((p11cAe_mul p11cAe_X5
      (isBigO_refl (fun a : ℝ => a ^ (-(1 / 4) : ℝ)) (𝓝[>] 0))).const_mul_left K)
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [p11cAe_pos] with a ha
    rw [hK a ha]

end KAM.Planetary

end
