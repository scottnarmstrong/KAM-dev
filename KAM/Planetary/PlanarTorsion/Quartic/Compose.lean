/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Quartic.Reduce
public import KAM.Planetary.PlanarTorsion.Quartic.Algebra

/-!
# Planar quartic torsion: the pair jet at the eccentricity vector (P11C, package T6)

Blueprint P, Part 11b (`stepP:p11b:qe-conv`).  In the variables `a_i = |u_i|²/I_i`,
`d = u₁·u₂/√(I₁I₂)`, `σ = √(1 - a₁/4)√(1 - a₂/4)` the squared lengths and the scalar product of
the eccentricity vectors `qeV I u` are exactly `a_i - a_i²/4` and `d σ`, so `p11c_pairJet` at
`qeV I u` is the constant plus `qeJetExpr` (`qe_pairJet_qeV`).
-/

@[expose] public noncomputable section
open Set Real Function Filter
open scoped Topology
namespace KAM.Planetary

/-- `a_i = |u_i|²/I_i`. -/
def qeA (I : Fin 2 → ℝ) (u : Phase 2) (i : Fin 2) : ℝ := (u.1 i ^ 2 + u.2 i ^ 2) / I i

/-- `d = u₁·u₂/√(I₁I₂)`. -/
def qeD (I : Fin 2 → ℝ) (u : Phase 2) : ℝ := p11c_pairDot u / (√(I 0) * √(I 1))

/-- `σ = √(1 - a₁/4)√(1 - a₂/4)`. -/
def qeSig (I : Fin 2 → ℝ) (u : Phase 2) : ℝ :=
  √(1 - qeA I u 0 / 4) * √(1 - qeA I u 1 / 4)

theorem qeScale_eq {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) (u : Phase 2) (i : Fin 2) :
    qeScale I u i = √(1 - qeA I u i / 4) / √(I i) := by
  have : (1 - (u.1 i ^ 2 + u.2 i ^ 2) / 2 / (2 * I i)) = 1 - qeA I u i / 4 := by
    have := (hI i).ne'
    unfold qeA
    field_simp
    ring
  unfold qeScale
  rw [this]
  exact Real.sqrt_div' _ (hI i).le

theorem qeScale_sq {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) {u : Phase 2} (i : Fin 2)
    (h : qeA I u i ≤ 4) : qeScale I u i ^ 2 = (1 - qeA I u i / 4) / I i := by
  rw [qeScale_eq hI, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (hI i).le]

theorem qeV_sq {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) {u : Phase 2} (i : Fin 2)
    (h : qeA I u i ≤ 4) :
    (qeV I u).1 i ^ 2 + (qeV I u).2 i ^ 2 = qeA I u i - qeA I u i ^ 2 / 4 := by
  have h1 := qeScale_sq hI i h
  have hi := (hI i).ne'
  have : (qeV I u).1 i ^ 2 + (qeV I u).2 i ^ 2 = qeScale I u i ^ 2 * (u.1 i ^ 2 + u.2 i ^ 2) := by
    simp only [qeV]; ring
  rw [this, h1]
  unfold qeA
  field_simp

theorem qeV_dot {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) (u : Phase 2) :
    p11c_pairDot (qeV I u) = qeD I u * qeSig I u := by
  have h0 := qeScale_eq hI u 0
  have h1 := qeScale_eq hI u 1
  have e0 := (Real.sqrt_pos.2 (hI 0)).ne'
  have e1 := (Real.sqrt_pos.2 (hI 1)).ne'
  simp only [p11c_pairDot, qeV, qeD, qeSig]
  rw [h0, h1]
  field_simp

theorem qeV_slowLength_sq {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) {u : Phase 2}
    (h0 : qeA I u 0 ≤ 4) (h1 : qeA I u 1 ≤ 4) :
    p11c_slowLength (qeV I u) ^ 2 =
      (qeA I u 0 - qeA I u 0 ^ 2 / 4) + (qeA I u 1 - qeA I u 1 ^ 2 / 4) := by
  unfold p11c_slowLength
  rw [Real.sq_sqrt (by positivity), Fin.sum_univ_two, ← qeV_sq hI 0 h0, ← qeV_sq hI 1 h1]

/-- The pair jet at the eccentricity vector, in the variables `(a₁, a₂, d, σ)`. -/
theorem qe_pairJet_qeV {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) (α : ℝ) {u : Phase 2}
    (h0 : qeA I u 0 ≤ 4) (h1 : qeA I u 1 ≤ 4) :
    p11c_pairJet α (qeV I u) = p11c_laplace (1 / 2) 0 α +
      qeJetExpr (p11c_pairCoeffs α) (qeA I u 0) (qeA I u 1) (qeD I u) (qeSig I u) := by
  have hX := qeV_sq hI 0 h0
  have hY := qeV_sq hI 1 h1
  have hZ := qeV_dot hI u
  have hS := qeV_slowLength_sq hI h0 h1
  unfold p11c_pairJet p11c_quartic qeJetExpr
  simp only [hS, hZ]
  simp only [Fin.castAdd, Fin.castLE]
  rw [hX, hY]
  simp
  ring

/-- The quartic with the six explicit coefficients, in the variables `(a₁, a₂, d)`. -/
theorem qe_quartic_coeffs {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) (pref : ℝ) (co : Fin 8 → ℝ)
    (u : Phase 2) :
    p11c_quartic ![pref * (co 2 - co 0 / 4) / (I 0 ^ 2), pref * (co 3 - co 0 / 4) / (I 1 ^ 2),
      pref * co 4 / (I 0 * I 1), pref * co 5 / (I 0 * I 1),
      pref * (co 6 - co 1 / 8) / (I 0 ^ (3 / 2 : ℝ) * I 1 ^ (1 / 2 : ℝ)),
      pref * (co 7 - co 1 / 8) / (I 0 ^ (1 / 2 : ℝ) * I 1 ^ (3 / 2 : ℝ))] u =
      pref * (qePolyExpr co (qeA I u 0) (qeA I u 1) (qeD I u) -
        co 0 * (qeA I u 0 + qeA I u 1) - co 1 * qeD I u) := by
  have h32 : ∀ i, I i ^ (3 / 2 : ℝ) = I i * √(I i) := by
    intro i
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (hI i), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have h12 : ∀ i, I i ^ (1 / 2 : ℝ) = √(I i) := fun i => (Real.sqrt_eq_rpow (I i)).symm
  have hs0 := Real.sqrt_pos.2 (hI 0)
  have hs1 := Real.sqrt_pos.2 (hI 1)
  have hI0 : I 0 = √(I 0) ^ 2 := (Real.sq_sqrt (hI 0).le).symm
  have hI1 : I 1 = √(I 1) ^ 2 := (Real.sq_sqrt (hI 1).le).symm
  unfold p11c_quartic qePolyExpr qeA qeD p11c_pairDot
  simp only [h32, h12, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  generalize √(I 0) = x at hs0 hI0 ⊢
  generalize √(I 1) = y at hs1 hI1 ⊢
  rw [hI0, hI1]
  have hx : x ≠ 0 := hs0.ne'
  have hy : y ≠ 0 := hs1.ne'
  field_simp
  ring

end KAM.Planetary

end
