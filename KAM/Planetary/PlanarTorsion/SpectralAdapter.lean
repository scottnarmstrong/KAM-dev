/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Setting
public import KAM.Planetary.PlanarTorsion.LaplaceReduction
public import KAM.Planetary.SecularForm.Quadratic

/-!
# Planar quartic torsion: the physical quadratic form and its spectral data (P11C, package T12)

Blueprint P, Part 11b (`bpP:p11b:sec-beta#data`): the explicit physical matrix `p11c_Q`, its sorted
eigenvalues `p11c_sigma` and its spectral projector `p11c_projector`, together with
`quadratic_physical_bridge`: the second homogeneous jet at `z = 0` of the actual secular average
`p11c_secular (p11c_hatFix p)` at the actions of the axes `a` equals the two quadratic blocks of
`p11c_Q p a`.

The matrix is never assumed.  `p11c_Q_eq_coeffs` identifies `p11c_Q` with the Part-8 matrix
`SecularForm.coeffs` (via `p11c_laplace_eq_laplace_def`), and the bridge subtracts the polynomial
part given by Part 8's `quadratic_form` from the secular average: the remainder is analytic at `0`
and `O(‖z‖⁴)`, so its second iterated derivative vanishes (`p11c_iteratedFDeriv_two_of_isBigO`).
-/

@[expose] public noncomputable section
open Set Metric Real Function Filter Asymptotics
open scoped Topology
namespace KAM.Planetary
open KAM KAM.Kepler

/- Coefficients and global spectral projector are explicit and independent of a chosen eigenbasis. -/
def p11c_Q (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let I := p.actions a
  let alpha := a 0 / a 1
  let A := p.G * p.m 0 * p.m 1 / (4 * a 1) * alpha * p11c_laplace (3 / 2) 1 alpha
  let B := p.G * p.m 0 * p.m 1 / (4 * a 1) * alpha * p11c_laplace (3 / 2) 2 alpha
  !![-A / I 0, B / sqrt (I 0 * I 1); B / sqrt (I 0 * I 1), -A / I 1]

def p11c_sigma (p : PlanarData) (a : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let Q := p11c_Q p a
  let R := sqrt ((Q 0 0 - Q 1 1) ^ 2 + 4 * Q 0 1 ^ 2)
  ![(Q 0 0 + Q 1 1 - R) / 2, (Q 0 0 + Q 1 1 + R) / 2]

def p11c_projector (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (p11c_sigma p a 0 - p11c_sigma p a 1)⁻¹ • (p11c_Q p a - p11c_sigma p a 1 • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-! ### The Laplace adapter -/

theorem p11c_laplace_eq_laplace_def (s : ℝ) (k : ℤ) (a : ℝ) :
    p11c_laplace s k a = SecularForm.laplace_def s k a := by
  unfold p11c_laplace SecularForm.laplace_def
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hk : 0 ≤ 1 + a ^ 2 - 2 * a * cos t := by nlinarith [sq_nonneg (a - cos t), sin_sq_add_cos_sq t]
  rw [Real.rpow_neg hk, div_eq_mul_inv, mul_comm]

/-! ### Identification of `p11c_Q` with the Part-8 matrix -/

/-- The Part-8 data attached to valid physical data in two degrees of freedom. -/
def p11cSecularData (p : PlanarData) (hp : p.Valid) : SecularForm.Data 2 where
  G := p.G
  m0 := p.m0
  m := p.m
  hG := hp.1
  hm0 := hp.2.1
  hm := hp.2.2
  hn := by norm_num

theorem p11c_axes_mem {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) : a ∈ SecularForm.axes 2 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact ha.1
    · exact ha.1.trans ha.2
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact ha.2 | (exfalso; revert hij; decide)

theorem p11c_Q_eq_coeffs (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    p11c_Q p a = SecularForm.coeffs (p11cSecularData p hp) a := by
  have h0 : 0 < a 0 := ha.1
  have h1 : 0 < a 1 := h0.trans ha.2
  have hI : ∀ i, 0 < p.actions a i := by
    intro i
    have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
    have := hp.2.2 i
    unfold PlanarData.actions
    have : 0 < a i := by fin_cases i <;> simp [h0, h1]
    positivity
  have e : ∀ i j, √(SecularForm.action (p11cSecularData p hp) a i) *
      √(SecularForm.action (p11cSecularData p hp) a j) = √(p.actions a i * p.actions a j) :=
    fun i j => (Real.sqrt_mul (hI i).le _).symm
  have e0 := hI 0
  have e1 := hI 1
  have h00 : √(p.actions a 0 * p.actions a 0) = p.actions a 0 := Real.sqrt_mul_self e0.le
  have h11 : √(p.actions a 1 * p.actions a 1) = p.actions a 1 := Real.sqrt_mul_self e1.le
  have hc : ∀ i j, SecularForm.coeffs (p11cSecularData p hp) a i j =
      SecularForm.qhat (p11cSecularData p hp) a i j / √(p.actions a i * p.actions a j) := by
    intro i j; rw [SecularForm.coeffs, e]
  ext i j
  rw [hc]
  fin_cases i <;> fin_cases j <;>
    simp [p11c_Q, SecularForm.qhat, SecularForm.pairA, SecularForm.pairB, h00, h11,
      p11c_laplace_eq_laplace_def, Fin.sum_univ_two, p11cSecularData, mul_comm (p.actions a 1)]
  all_goals field_simp

end KAM.Planetary

end
