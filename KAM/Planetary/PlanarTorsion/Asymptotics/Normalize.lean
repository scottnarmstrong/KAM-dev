/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries
public import KAM.Planetary.PlanarTorsion.Asymptotics.Homogeneity

/-!
# Planar quartic torsion: normalisation of the physical scales (P11C, package T19)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, uniformity clause): for valid data `p` with mass
ratio `p.m 0 / p.m 1 = r` the matrix `p11c_Q p ![α, 1]` is a positive multiple of the matrix of
the normalised data `p11cAs_unit r` (`G = m₀ = 1`, masses `(r, 1)`), the spectral projector
coincides with it, the six quartic coefficients are multiplied by `(p.m0)⁻¹` and so
`p11c_beta p ![α, 1] = (p.m0)⁻¹ • p11c_beta (p11cAs_unit r) ![α, 1]`.
-/

@[expose] public noncomputable section
open Set Real
namespace KAM.Planetary

/-- The normalised data of mass ratio `r`: `G = m₀ = 1`, planet masses `(r, 1)`. -/
def p11cAs_unit (r : ℝ) : PlanarData := ⟨1, 1, ![r, 1]⟩

theorem p11cAs_unit_valid {r : ℝ} (hr : 0 < r) : (p11cAs_unit r).Valid := by
  refine ⟨one_pos, one_pos, fun i => ?_⟩
  fin_cases i <;> simp [p11cAs_unit, hr]

theorem p11cAs_unit_kappa (r : ℝ) : (p11cAs_unit r).kappa = 1 := by
  simp [PlanarData.kappa, p11cAs_unit]

theorem p11cAs_Q_ratio (p : PlanarData) (hp : p.Valid) {r : ℝ} (hr : 0 < r)
    (hm : p.m 0 / p.m 1 = r) {α : ℝ} (hα : 0 < α) :
    p11c_Q p ![α, 1] = (p.G * p.m 1 / √p.kappa) • p11c_Q (p11cAs_unit r) ![α, 1] := by
  have hu := p11cAs_unit_valid hr
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm1 := hp.2.2 1
  have hm0 : p.m 0 = r * p.m 1 := by field_simp at hm; linarith
  have hsk : 0 < √p.kappa := Real.sqrt_pos.2 hk
  have hsr : √(p.m 0 * p.m 1 * p.kappa) = √r * p.m 1 * √p.kappa := by
    rw [hm0, show r * p.m 1 * p.m 1 * p.kappa = r * p.m 1 ^ 2 * p.kappa by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul hr.le, Real.sqrt_sq hm1.le]
  have hsrp : 0 < √r := Real.sqrt_pos.2 hr
  have h01 : p11c_Q p ![α, 1] 0 1 =
      p.G * p.m 1 / √p.kappa * p11c_Q (p11cAs_unit r) ![α, 1] 0 1 := by
    rw [p11cAe_Q01 p hp hα, p11cAe_Q01 _ hu hα, p11cAs_unit_kappa, hsr]
    simp [p11cAs_unit]
    rw [hm0]
    field_simp
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Matrix.smul_apply, smul_eq_mul]
    rw [p11cAe_Q00 p hp hα, p11cAe_Q00 _ hu hα, p11cAs_unit_kappa]
    simp [p11cAs_unit]
    field_simp
  · simpa using h01
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.smul_apply, smul_eq_mul]
    rw [p11c_Q_symm, p11c_Q_symm (p11cAs_unit r)]
    exact h01
  · simp only [Fin.mk_one, Matrix.smul_apply, smul_eq_mul]
    rw [p11cAe_Q11 p hp hα, p11cAe_Q11 _ hu hα, p11cAs_unit_kappa]
    simp [p11cAs_unit]
    rw [hm0]
    field_simp

theorem p11cAs_act_rpow (p : PlanarData) (hp : p.Valid) {α : ℝ} (hα : 0 < α) {e f : ℝ}
    (hef : e + f = 2) : p.actions ![α, 1] 0 ^ e * p.actions ![α, 1] 1 ^ f =
      p.m 0 ^ e * p.m 1 ^ f * p.kappa * α ^ (e / 2) := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm0 := hp.2.2 0
  have hm1 := hp.2.2 1
  have hsk : 0 < √p.kappa := Real.sqrt_pos.2 hk
  rw [p11cAe_act0 p hα hk, p11cAe_act1 p α, Real.mul_rpow hm0.le (by positivity),
    Real.mul_rpow hsk.le (Real.sqrt_nonneg _), Real.mul_rpow hm1.le hsk.le,
    p11cAe_sqrt_rpow hα, show p.m 0 ^ e * (√p.kappa ^ e * α ^ (e / 2)) *
      (p.m 1 ^ f * √p.kappa ^ f) = p.m 0 ^ e * p.m 1 ^ f * (√p.kappa ^ e * √p.kappa ^ f) *
      α ^ (e / 2) by ring, ← Real.rpow_add hsk, hef, Real.rpow_two, Real.sq_sqrt hk.le]

theorem p11cAs_mass_rpow {r t : ℝ} (hr : 0 < r) (ht : 0 < t) {e f : ℝ} (hef : e + f = 2) :
    (r * t) ^ e * t ^ f = r ^ e * t ^ 2 := by
  rw [Real.mul_rpow hr.le ht.le, mul_assoc, ← Real.rpow_add ht, hef, Real.rpow_two, sq]

theorem p11cAs_coeffs_ratio (p : PlanarData) (hp : p.Valid) {r : ℝ} (hr : 0 < r)
    (hm : p.m 0 / p.m 1 = r) {α : ℝ} (hα : 0 < α) :
    p11c_coeffs p ![α, 1] = (p.m0)⁻¹ • p11c_coeffs (p11cAs_unit r) ![α, 1] := by
  have hu := p11cAs_unit_valid hr
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hm1 := hp.2.2 1
  have hG := hp.1
  have hm0' := hp.2.1
  have hm0 : p.m 0 = r * p.m 1 := by field_simp at hm; linarith
  have hκ : p.kappa = p.G * p.m0 := rfl
  have h4 := p11cAs_act_rpow p hp hα (e := 3 / 2) (f := 1 / 2) (by norm_num)
  have h5 := p11cAs_act_rpow p hp hα (e := 1 / 2) (f := 3 / 2) (by norm_num)
  have h4u := p11cAs_act_rpow _ hu hα (e := 3 / 2) (f := 1 / 2) (by norm_num)
  have h5u := p11cAs_act_rpow _ hu hα (e := 1 / 2) (f := 3 / 2) (by norm_num)
  have m4 := p11cAs_mass_rpow hr hm1 (e := 3 / 2) (f := 1 / 2) (by norm_num)
  have m5 := p11cAs_mass_rpow hr hm1 (e := 1 / 2) (f := 3 / 2) (by norm_num)
  have hp1 : 0 < r ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
  have hp2 : 0 < r ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
  have hpa : 0 < α ^ ((3 / 2 : ℝ) / 2) := Real.rpow_pos_of_pos hα _
  have hpb : 0 < α ^ ((1 / 2 : ℝ) / 2) := Real.rpow_pos_of_pos hα _
  have hk1 : ({ G := 1, m0 := 1, m := ![r, 1] } : PlanarData).kappa = 1 := p11cAs_unit_kappa r
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Pi.smul_apply, smul_eq_mul]
    rw [p11cAe_c0_eq p hp hα, p11cAe_c0_eq _ hu hα, p11cAs_unit_kappa, hm0]
    simp only [p11cAs_unit, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hκ]
    field_simp
  · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
    rw [p11cAe_c1_eq p hp hα, p11cAe_c1_eq _ hu hα, p11cAs_unit_kappa, hm0]
    simp only [p11cAs_unit, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hκ]
    field_simp
  · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    rw [p11cAe_c2_eq p hp hα, p11cAe_c2_eq _ hu hα, p11cAs_unit_kappa]
    simp only [p11cAs_unit]
    rw [hκ]
    field_simp
  · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    rw [p11cAe_c3_eq p hp hα, p11cAe_c3_eq _ hu hα, p11cAs_unit_kappa]
    simp only [p11cAs_unit]
    rw [hκ]
    field_simp
  · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul, p11c_coeffs,
      Matrix.cons_val, h4, h4u]
    simp only [p11cAs_unit, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.one_rpow, div_one]
    rw [hm0, m4, hκ, hk1]
    field_simp
  · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul, p11c_coeffs,
      Matrix.cons_val, h5, h5u]
    simp only [p11cAs_unit, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.one_rpow, div_one]
    rw [hm0, m5, hκ, hk1]
    field_simp

theorem p11cAs_beta_ratio (p : PlanarData) (hp : p.Valid) {r : ℝ} (hr : 0 < r)
    (hm : p.m 0 / p.m 1 = r) {α : ℝ} (hα : 0 < α) :
    p11c_beta p ![α, 1] = (p.m0)⁻¹ • p11c_beta (p11cAs_unit r) ![α, 1] := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hμ : 0 < p.G * p.m 1 / √p.kappa :=
    div_pos (mul_pos hp.1 (hp.2.2 1)) (Real.sqrt_pos.2 hk)
  rw [p11c_beta, p11c_beta, p11cAs_projector_of_Q p _ _ _ hμ (p11cAs_Q_ratio p hp hr hm hα),
    p11cAs_coeffs_ratio p hp hr hm hα, p11cAs_beta_def_smul]

end KAM.Planetary

end
