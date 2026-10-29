/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Power-rate algebra on `(0, 1]` (P11C-Q3)

Elementary monotonicity and product rules for `u ^ e` with `u ∈ (0, 1]`, used to chain the
polynomial rate bounds of `qb_poly` (the fragments `ab_gamma`, `ab_T0`, `ab_t0`, `ab_lam`).
-/

@[expose] public noncomputable section
open Set Real
namespace KAM.Planetary

theorem qbPoly_pow_anti {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {e f : ℝ} (h : e ≤ f) :
    u ^ f ≤ u ^ e :=
  Real.rpow_le_rpow_of_exponent_ge hu0 hu1 h

theorem qbPoly_negpow_mono {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {e f : ℝ} (h : e ≤ f) :
    u ^ (-e) ≤ u ^ (-f) :=
  Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (neg_le_neg h)

theorem qbPoly_negpow_ge_one {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {e : ℝ} (he : 0 ≤ e) :
    1 ≤ u ^ (-e) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by linarith)

theorem qbPoly_pow_le_one {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) {e : ℝ} (he : 0 ≤ e) :
    u ^ e ≤ 1 :=
  Real.rpow_le_one hu0.le hu1 he

/-- Product of two upper rate bounds. -/
theorem qbPoly_ub_mul {x y A B w z : ℝ} (hy : 0 ≤ y) (hAw : 0 ≤ A * w) (hx : x ≤ A * w)
    (hy' : y ≤ B * z) : x * y ≤ (A * B) * (w * z) := by
  calc x * y ≤ (A * w) * (B * z) := mul_le_mul hx hy' hy hAw
    _ = (A * B) * (w * z) := by ring

/-- Product of two lower rate bounds. -/
theorem qbPoly_lb_mul {x y A B w z : ℝ} (hA : 0 ≤ A * w) (hB : 0 ≤ B * z) (hx : A * w ≤ x)
    (hy : B * z ≤ y) : (A * B) * (w * z) ≤ x * y := by
  calc (A * B) * (w * z) = (A * w) * (B * z) := by ring
    _ ≤ x * y := mul_le_mul hx hy hB (hA.trans hx)

theorem qbPoly_pow_add {u : ℝ} (hu0 : 0 < u) (e f : ℝ) : u ^ (e + f) = u ^ e * u ^ f :=
  Real.rpow_add hu0 e f

end KAM.Planetary
