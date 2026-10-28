/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Beta

/-!
# Planar quartic torsion: homogeneity of `beta` (P11C, package T19)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, homogeneity clause): under `a ↦ s • a`
the matrix `p11c_Q` is multiplied by `(s √s)⁻¹`, hence the spectral projector is unchanged, the six
quartic coefficients are multiplied by `s ^ (-2)`, and so is `p11c_beta` (`beta_def` is linear in
the coefficients).
-/

@[expose] public noncomputable section
open Set Real
namespace KAM.Planetary

theorem p11cAs_projector_of_Q (p p' : PlanarData) (a a' : Fin 2 → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (h : p11c_Q p a = μ • p11c_Q p' a') :
    p11c_projector p a = p11c_projector p' a' := by
  have hs : p11c_sigma p a = μ • p11c_sigma p' a' := by
    have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    simp only [Matrix.smul_apply, smul_eq_mul] at h00 h11 h01 h10
    have hR : √((p11c_Q p a 0 0 - p11c_Q p a 1 1) ^ 2 + 4 * p11c_Q p a 0 1 ^ 2) =
        μ * √((p11c_Q p' a' 0 0 - p11c_Q p' a' 1 1) ^ 2 + 4 * p11c_Q p' a' 0 1 ^ 2) := by
      rw [← Real.sqrt_sq hμ.le, ← Real.sqrt_mul (sq_nonneg _), h00, h11, h01]
      congr 1
      ring
    funext i
    fin_cases i <;>
    · simp only [p11c_sigma, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one]
      rw [hR, h00, h11]
      ring
  have hs0 : p11c_sigma p a 0 - p11c_sigma p a 1 =
      μ * (p11c_sigma p' a' 0 - p11c_sigma p' a' 1) := by
    rw [hs]; simp; ring
  unfold p11c_projector
  rw [hs0, hs, h, Pi.smul_apply, smul_eq_mul, mul_smul (μ : ℝ) (p11c_sigma p' a' 1) 1,
    ← smul_sub, smul_smul, mul_inv, mul_assoc, mul_comm, mul_assoc, mul_inv_cancel₀ hμ.ne',
    mul_one]

theorem p11cAs_Q_smul (p : PlanarData) (hp : p.Valid) (a : Fin 2 → ℝ) (ha : a ∈ p11c_axes)
    {s : ℝ} (hs : 0 < s) : p11c_Q p (s • a) = (s * √s)⁻¹ • p11c_Q p a := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have h0 := ha.1
  have h1 := h0.trans ha.2
  have hss : √s * √s = s := Real.mul_self_sqrt hs.le
  have hsp : 0 < √s := Real.sqrt_pos.2 hs
  have hq : s * a 0 / (s * a 1) = a 0 / a 1 := mul_div_mul_left _ _ hs.ne'
  have hI : ∀ i, p.actions (s • a) i = √s * p.actions a i := fun i => by
    simp only [PlanarData.actions, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm p.kappa, mul_assoc, Real.sqrt_mul hs.le]; ring
  have hm0 := hp.2.2 0
  have hm1 := hp.2.2 1
  have hI0 : 0 < p.actions a 0 := by
    simp only [PlanarData.actions]; positivity
  have hI1 : 0 < p.actions a 1 := by
    simp only [PlanarData.actions]; positivity
  have hIs : √(√s * p.actions a 0 * (√s * p.actions a 1)) =
      √s * √(p.actions a 0 * p.actions a 1) := by
    rw [show √s * p.actions a 0 * (√s * p.actions a 1) =
      s * (p.actions a 0 * p.actions a 1) by
        linear_combination (p.actions a 0 * p.actions a 1) * hss,
      Real.sqrt_mul hs.le]
  have hJ : 0 < √(p.actions a 0 * p.actions a 1) := Real.sqrt_pos.2 (mul_pos hI0 hI1)
  generalize √s = u at hss hsp hI hIs ⊢
  subst hss
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp only [p11c_Q, hI, hIs, Pi.smul_apply, smul_eq_mul, hq, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one]
    field_simp

theorem p11cAs_coeffs_smul (p : PlanarData) (hp : p.Valid) (a : Fin 2 → ℝ)
    (ha : a ∈ p11c_axes) {s : ℝ} (hs : 0 < s) :
    p11c_coeffs p (s • a) = (s ^ 2)⁻¹ • p11c_coeffs p a := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have h0 := ha.1
  have h1 := h0.trans ha.2
  have hss : √s * √s = s := Real.mul_self_sqrt hs.le
  have hsp : 0 < √s := Real.sqrt_pos.2 hs
  have hq : s * a 0 / (s * a 1) = a 0 / a 1 := mul_div_mul_left _ _ hs.ne'
  have hI : ∀ i, p.actions (s • a) i = √s * p.actions a i := fun i => by
    simp only [PlanarData.actions, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm p.kappa, mul_assoc, Real.sqrt_mul hs.le]; ring
  have hm0 := hp.2.2 0
  have hm1 := hp.2.2 1
  have hI0 : 0 < p.actions a 0 := by
    simp only [PlanarData.actions]; positivity
  have hI1 : 0 < p.actions a 1 := by
    simp only [PlanarData.actions]; positivity
  have hr : ∀ e f : ℝ, e + f = 2 → (√s * p.actions a 0) ^ e * (√s * p.actions a 1) ^ f =
      s * (p.actions a 0 ^ e * p.actions a 1 ^ f) := fun e f hef => by
    rw [Real.mul_rpow hsp.le hI0.le, Real.mul_rpow hsp.le hI1.le,
      show √s ^ e * p.actions a 0 ^ e * (√s ^ f * p.actions a 1 ^ f) =
        (√s ^ e * √s ^ f) * (p.actions a 0 ^ e * p.actions a 1 ^ f) by ring,
      ← Real.rpow_add hsp, hef, Real.rpow_two, sq, hss]
  have hr32 := hr (3 / 2) (1 / 2) (by norm_num)
  have hr12 := hr (1 / 2) (3 / 2) (by norm_num)
  have hJ : 0 < p.actions a 0 ^ (3 / 2 : ℝ) * p.actions a 1 ^ (1 / 2 : ℝ) := by positivity
  have hJ' : 0 < p.actions a 0 ^ (1 / 2 : ℝ) * p.actions a 1 ^ (3 / 2 : ℝ) := by positivity
  generalize √s = u at hss hsp hI hr32 hr12
  subst hss
  funext i
  fin_cases i <;>
  · simp only [p11c_coeffs, hI, hq, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.isValue, hr32, hr12]
    field_simp

theorem p11cAs_beta_def_smul (ν : ℝ) (c : Fin 6 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) :
    beta_def (ν • c) P = ν • beta_def c P := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [beta_def] <;> ring

theorem p11cAs_beta_smul (p : PlanarData) (hp : p.Valid) (a : Fin 2 → ℝ) (ha : a ∈ p11c_axes)
    {s : ℝ} (hs : 0 < s) : p11c_beta p (s • a) = (s ^ (-2 : ℤ)) • p11c_beta p a := by
  have hμ : 0 < (s * √s)⁻¹ := inv_pos.2 (mul_pos hs (Real.sqrt_pos.2 hs))
  rw [p11c_beta, p11c_beta, p11cAs_projector_of_Q p p (s • a) a hμ (p11cAs_Q_smul p hp a ha hs),
    p11cAs_coeffs_smul p hp a ha hs, p11cAs_beta_def_smul, zpow_neg, zpow_ofNat]

end KAM.Planetary

end