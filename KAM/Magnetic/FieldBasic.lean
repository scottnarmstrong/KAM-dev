/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Magnetic.Defs.MagField
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The magnetic field `magField` in closed form

Unfrozen helper code.

* `magH0'`, `hasDerivAt_magH0`: `h'(p) = 1 - (3/2) p + p² - p³/4`.
* `magVq`, `hasDerivAt_magV`: the force `∂_q V` as a trigonometric polynomial.
* `magField_eq`: `magField x = (h'(p), -∂_q V(q, φ), 1)`.
* `magField_contDiff`: the field is `C¹` (it is not globally Lipschitz: `h'` is cubic).
* `magVq_abs_le`: the force is bounded by `magForceBound`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Magnetic

/-- `h'(p) = 1 - (3/2) p + p² - p³/4`. -/
def magH0' (p : ℝ) : ℝ := 1 - 3 / 2 * p + p ^ 2 - p ^ 3 / 4

theorem hasDerivAt_magH0 (p : ℝ) : HasDerivAt magH0 (magH0' p) p := by
  have h := ((((hasDerivAt_id p).sub ((hasDerivAt_pow 2 p).const_mul (3 / 4))).add
    ((hasDerivAt_pow 3 p).const_mul (1 / 3))).sub ((hasDerivAt_pow 4 p).const_mul (1 / 16)))
  have e : magH0 = fun p => id p - 3 / 4 * p ^ 2 + 1 / 3 * p ^ 3 - 1 / 16 * p ^ 4 := by
    funext p; simp [magH0]
  rw [e]
  convert h using 1
  simp [magH0']
  ring

/-- The constant `(1427/3200) ε²` of the quadratic control term. -/
def magCtl : ℝ := 1427 / 3200 * magEps ^ 2

/-- The force `∂_q V(q, φ)`. -/
def magVq (q φ : ℝ) : ℝ :=
  -(2 * π) * (magEps * (2 * sin (2 * π * (2 * q - φ)) + 3 * sin (2 * π * (3 * q - 2 * φ))) +
    magCtl * (2 * (32000 / 2777 * cos (2 * π * (2 * q - φ)) -
      96000 / 7669 * cos (2 * π * (3 * q - 2 * φ)))) *
      (2 * (32000 / 2777) * sin (2 * π * (2 * q - φ)) -
        3 * (96000 / 7669) * sin (2 * π * (3 * q - 2 * φ))))

theorem hasDerivAt_magV (q φ : ℝ) : HasDerivAt (fun s => magV s φ) (magVq q φ) q := by
  have ha : HasDerivAt (fun s : ℝ => 2 * π * (2 * s - φ)) (2 * π * 2) q := by
    simpa using (((hasDerivAt_id q).const_mul 2).sub_const φ).const_mul (2 * π)
  have hb : HasDerivAt (fun s : ℝ => 2 * π * (3 * s - 2 * φ)) (2 * π * 3) q := by
    simpa using (((hasDerivAt_id q).const_mul 3).sub_const (2 * φ)).const_mul (2 * π)
  have hca := ha.cos
  have hcb := hb.cos
  have hA := (hca.const_mul (32000 / 2777)).sub (hcb.const_mul (96000 / 7669))
  have h := ((hca.add hcb).const_mul magEps).add ((hA.pow 2).const_mul magCtl)
  unfold magV
  convert h using 1
  · funext s; simp [magCtl]
  · simp only [magVq, magCtl, Pi.sub_apply]
    push_cast
    ring

theorem magField_eq (x : ℝ × ℝ × ℝ) :
    magField x = (magH0' x.2.1, -magVq x.1 x.2.2, 1) := by
  simp [magField, (hasDerivAt_magH0 _).deriv, (hasDerivAt_magV _ _).deriv]

theorem magField_contDiff : ContDiff ℝ 1 magField := by
  have h : magField = fun x => (magH0' x.2.1, -magVq x.1 x.2.2, 1) := funext magField_eq
  rw [h]
  unfold magH0' magVq
  fun_prop

/-- A bound on the force: `2π (5 ε + 2 c (k₁ + k₂)(2 k₁ + 3 k₂))`, `c = (1427/3200) ε²`. -/
def magForceBound : ℝ :=
  2 * π * (5 * magEps + magCtl * (2 * (32000 / 2777 + 96000 / 7669)) *
    (2 * (32000 / 2777) + 3 * (96000 / 7669)))

private theorem abs_le_one_bounds {x : ℝ} (h : |x| ≤ 1) : -1 ≤ x ∧ x ≤ 1 := abs_le.1 h

theorem magVq_abs_le (q φ : ℝ) : |magVq q φ| ≤ magForceBound := by
  have hε : magEps = 3 / 2500 := rfl
  have hc : (0 : ℝ) ≤ magCtl := by unfold magCtl; positivity
  set sa := sin (2 * π * (2 * q - φ))
  set sb := sin (2 * π * (3 * q - 2 * φ))
  set ca := cos (2 * π * (2 * q - φ))
  set cb := cos (2 * π * (3 * q - 2 * φ))
  obtain ⟨sa1, sa2⟩ := abs_le_one_bounds (abs_sin_le_one (2 * π * (2 * q - φ)))
  obtain ⟨sb1, sb2⟩ := abs_le_one_bounds (abs_sin_le_one (2 * π * (3 * q - 2 * φ)))
  obtain ⟨ca1, ca2⟩ := abs_le_one_bounds (abs_cos_le_one (2 * π * (2 * q - φ)))
  obtain ⟨cb1, cb2⟩ := abs_le_one_bounds (abs_cos_le_one (2 * π * (3 * q - 2 * φ)))
  have h1 : |magEps * (2 * sa + 3 * sb)| ≤ 5 * magEps := by
    rw [hε, abs_le]; constructor <;> linarith
  have h2 : |2 * (32000 / 2777 * ca - 96000 / 7669 * cb)| ≤
      2 * (32000 / 2777 + 96000 / 7669) := by
    rw [abs_le]; constructor <;> linarith
  have h3 : |2 * (32000 / 2777) * sa - 3 * (96000 / 7669) * sb| ≤
      2 * (32000 / 2777) + 3 * (96000 / 7669) := by
    rw [abs_le]; constructor <;> linarith
  have h4 : |magCtl * (2 * (32000 / 2777 * ca - 96000 / 7669 * cb)) *
      (2 * (32000 / 2777) * sa - 3 * (96000 / 7669) * sb)| ≤
      magCtl * (2 * (32000 / 2777 + 96000 / 7669)) *
        (2 * (32000 / 2777) + 3 * (96000 / 7669)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hc) h3 (abs_nonneg _) (by positivity)
  unfold magVq magForceBound
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h4)) (by positivity)

theorem magForceBound_nonneg : 0 ≤ magForceBound := (abs_nonneg _).trans (magVq_abs_le 0 0)

end KAM.Magnetic

end
