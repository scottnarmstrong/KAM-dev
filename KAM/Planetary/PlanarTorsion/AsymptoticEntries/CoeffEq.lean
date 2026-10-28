/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Leading
public import KAM.Planetary.PlanarTorsion.Quartic.Defs

/-!
# Planar quartic torsion: the quartic coefficients at hierarchical axes (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, step `stepP:p11b:as-c`): exact formulas for
`p11c_coeffs p ![α, 1]` as constants times the pair-coefficient combinations
`A₂ - A₀/4`, `A₃ - A₀/4`, `A₄`, `A₅`, `A₆ - A₁/8`, `A₇ - A₁/8` times a power of `α`
(`p11cAe_c0_eq` … `p11cAe_c5_eq`).  Here `Λ₁ = m₁ √(κ α)` and `Λ₂ = m₂ √κ`.
-/

@[expose] public noncomputable section
open Set Filter Asymptotics Real
open scoped Topology
namespace KAM.Planetary

variable (p : PlanarData)

theorem p11cAe_act0 {α : ℝ} (hα : 0 < α) (hk : 0 < p.kappa) :
    p.actions ![α, 1] 0 = p.m 0 * (√p.kappa * √α) := by
  simp only [PlanarData.actions, Matrix.cons_val_zero]
  rw [Real.sqrt_mul hk.le]

theorem p11cAe_act1 (α : ℝ) :
    p.actions ![α, 1] 1 = p.m 1 * √p.kappa := by
  simp [PlanarData.actions]

theorem p11cAe_sqrt_rpow {α : ℝ} (hα : 0 < α) (s : ℝ) : (√α) ^ s = α ^ (s / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hα.le]
  ring_nf

theorem p11cAe_c0_eq (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    p11c_coeffs p ![α, 1] 0 = -(p.G * p.m 1 / (p.m 0 * p.kappa)) *
      ((p11c_pairCoeffs α 2 - p11c_pairCoeffs α 0 / 4) / α) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm0 := hp.2.2 0
  have h1 : (p.m 0 * (√p.kappa * √α)) ^ 2 = p.m 0 ^ 2 * p.kappa * α := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hk.le, Real.sq_sqrt hα.le]; ring
  simp only [p11c_coeffs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_one,
    p11cAe_act0 p hα hk, h1]
  field_simp

theorem p11cAe_c1_eq (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    p11c_coeffs p ![α, 1] 1 = -(p.G * p.m 0 / (p.m 1 * p.kappa)) *
      (p11c_pairCoeffs α 3 - p11c_pairCoeffs α 0 / 4) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm1 := hp.2.2 1
  have h1 : (p.m 1 * √p.kappa) ^ 2 = p.m 1 ^ 2 * p.kappa := by
    rw [mul_pow, Real.sq_sqrt hk.le]
  simp only [p11c_coeffs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_one,
    p11cAe_act1 p α, h1]
  field_simp

theorem p11cAe_act_mul (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    p.actions ![α, 1] 0 * p.actions ![α, 1] 1 = p.m 0 * p.m 1 * p.kappa * √α := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  rw [p11cAe_act0 p hα hk, p11cAe_act1 p α]
  have : √p.kappa * √p.kappa = p.kappa := Real.mul_self_sqrt hk.le
  calc _ = p.m 0 * p.m 1 * (√p.kappa * √p.kappa) * √α := by ring
    _ = _ := by rw [this]

theorem p11cAe_c2_eq (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    p11c_coeffs p ![α, 1] 2 = -(p.G / p.kappa) * (p11c_pairCoeffs α 4 * α ^ (-(1 / 2) : ℝ)) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm0 := hp.2.2 0
  have hm1 := hp.2.2 1
  have hsa : 0 < √α := Real.sqrt_pos.2 hα
  simp only [p11c_coeffs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_one,
    p11cAe_act_mul p hp hα, Matrix.cons_val]
  rw [Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow]
  field_simp

theorem p11cAe_c3_eq (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    p11c_coeffs p ![α, 1] 3 = -(p.G / p.kappa) * (p11c_pairCoeffs α 5 * α ^ (-(1 / 2) : ℝ)) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm0 := hp.2.2 0
  have hm1 := hp.2.2 1
  have hsa : 0 < √α := Real.sqrt_pos.2 hα
  simp only [p11c_coeffs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_one,
    p11cAe_act_mul p hp hα, Matrix.cons_val]
  rw [Real.rpow_neg hα.le, ← Real.sqrt_eq_rpow]
  field_simp

theorem p11cAe_den (hp : p.Valid) {α : ℝ} (hα : 0 < α) (s t : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      p.actions ![α, 1] 0 ^ s * p.actions ![α, 1] 1 ^ t = K * α ^ (s / 2) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm0 := hp.2.2 0
  have hm1 := hp.2.2 1
  have hsk : 0 < √p.kappa := Real.sqrt_pos.2 hk
  refine ⟨p.m 0 ^ s * (√p.kappa) ^ s * (p.m 1 ^ t * (√p.kappa) ^ t), by positivity, ?_⟩
  rw [p11cAe_act0 p hα hk, p11cAe_act1 p α, Real.mul_rpow hm0.le (by positivity),
    Real.mul_rpow hsk.le (Real.sqrt_nonneg _), Real.mul_rpow hm1.le hsk.le,
    p11cAe_sqrt_rpow hα]
  ring

theorem p11cAe_c_rpow (hp : p.Valid) {α : ℝ} (hα : 0 < α) (s t : ℝ) (X : ℝ) :
    ∃ K : ℝ, -p.G * p.m 0 * p.m 1 / ![α, 1] 1 * X /
      (p.actions ![α, 1] 0 ^ s * p.actions ![α, 1] 1 ^ t) = K * (X * α ^ (-(s / 2))) := by
  obtain ⟨K, hK, hKe⟩ := p11cAe_den p hp hα s t
  refine ⟨-p.G * p.m 0 * p.m 1 / K, ?_⟩
  have hpos : 0 < α ^ (s / 2) := Real.rpow_pos_of_pos hα _
  have h1 : (![α, 1] 1 : ℝ) = 1 := by simp
  rw [hKe, Real.rpow_neg hα.le, h1, div_one]
  field_simp

theorem p11cAe_c4_eq (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, p11c_coeffs p ![α, 1] 4 = K *
      ((p11c_pairCoeffs α 6 - p11c_pairCoeffs α 1 / 8) * α ^ (-(3 / 4) : ℝ)) := by
  obtain ⟨K, hK⟩ := p11cAe_c_rpow p hp hα (3 / 2) (1 / 2) (p11c_pairCoeffs α 6 -
    p11c_pairCoeffs α 1 / 8)
  refine ⟨K, ?_⟩
  rw [show (-(3 / 4) : ℝ) = -((3 / 2 : ℝ) / 2) by norm_num, ← hK]
  simp only [p11c_coeffs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_one,
    Matrix.cons_val]

theorem p11cAe_c5_eq (hp : p.Valid) {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, p11c_coeffs p ![α, 1] 5 = K *
      ((p11c_pairCoeffs α 7 - p11c_pairCoeffs α 1 / 8) * α ^ (-(1 / 4) : ℝ)) := by
  obtain ⟨K, hK⟩ := p11cAe_c_rpow p hp hα (1 / 2) (3 / 2) (p11c_pairCoeffs α 7 -
    p11c_pairCoeffs α 1 / 8)
  refine ⟨K, ?_⟩
  rw [show (-(1 / 4) : ℝ) = -((1 / 2 : ℝ) / 2) by norm_num, ← hK]
  simp only [p11c_coeffs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, div_one,
    Matrix.cons_val]

end KAM.Planetary

end
