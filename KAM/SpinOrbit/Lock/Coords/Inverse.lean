/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.Coords.Maps
public import KAM.SpinOrbit.Lock.Confine
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# SO-LOCK coordinates: action and inverse

* `libAction_lockToPhysicalR`: the action coordinate `I ≥ 0` is the elliptic libration action of
  the physical image;
* `lockToPhysicalR_surj`: every physical point off the centre curve (`libAction > 0`) is hit,
  with action `libAction` and angle `arg(Y/√Ω + i√Ω X)/2π`.
-/

public section

open Real

namespace KAM.SpinOrbit.Lock

/-- The action is the elliptic libration action of the image. -/
theorem libAction_lockToPhysicalR {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 ≤ z.2 0) :
    libAction Ω c (lockToPhysicalR Ω c z) = z.2 0 := by
  have hπ := Real.pi_pos
  have h1 : Real.sqrt (z.2 0 / (π * Ω)) ^ 2 = z.2 0 / (π * Ω) :=
    Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt (z.2 0 * Ω / π) ^ 2 = z.2 0 * Ω / π := Real.sq_sqrt (by positivity)
  have hsc := Real.sin_sq_add_cos_sq (2 * π * z.1 0)
  simp only [libAction, lockToPhysicalR, lockX, lockY]
  have e1 : z.1 1 + c (z.1 1) + Real.sqrt (z.2 0 / (π * Ω)) * Real.sin (2 * π * z.1 0) - z.1 1 -
      c (z.1 1) = Real.sqrt (z.2 0 / (π * Ω)) * Real.sin (2 * π * z.1 0) := by ring
  have e2 : 1 + deriv c (z.1 1) + Real.sqrt (z.2 0 * Ω / π) * Real.cos (2 * π * z.1 0) - 1 -
      deriv c (z.1 1) = Real.sqrt (z.2 0 * Ω / π) * Real.cos (2 * π * z.1 0) := by ring
  rw [e1, e2, mul_pow, mul_pow, h1, h2]
  generalize Real.sin (2 * π * z.1 0) = s at hsc ⊢
  generalize Real.cos (2 * π * z.1 0) = co at hsc ⊢
  field_simp
  linear_combination z.2 0 * hsc

/-- The inverse on the punctured plane: every physical point off the centre curve is hit, with
action `libAction` and angle `arg(Y/√Ω + i√Ω X)/2π`. -/
theorem lockToPhysicalR_surj {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ) (x : ℝ × ℝ × ℝ)
    (hx : 0 < libAction Ω c x) :
    lockToPhysicalR Ω c
      (![Complex.arg ((((x.2.1 - 1 - deriv c x.2.2) / √Ω : ℝ) : ℂ) +
          ((√Ω * (x.1 - x.2.2 - c x.2.2) : ℝ) : ℂ) * Complex.I) / (2 * π), x.2.2],
       ![libAction Ω c x, 0]) = x := by
  obtain ⟨q, p, φ⟩ := x
  set X := q - φ - c φ with hX
  set Y := p - 1 - deriv c φ with hY
  have hπ := Real.pi_pos
  have hsΩ : 0 < √Ω := Real.sqrt_pos.2 hΩ
  have hsΩ2 : √Ω ^ 2 = Ω := Real.sq_sqrt hΩ.le
  set w : ℂ := ((Y / √Ω : ℝ) : ℂ) + ((√Ω * X : ℝ) : ℂ) * Complex.I with hw
  have hwre : w.re = Y / √Ω := by simp [hw]
  have hwim : w.im = √Ω * X := by simp [hw]
  have hL : libAction Ω c (q, p, φ) = π * ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← sq, ← sq, hwre, hwim]
    simp only [libAction]
    rw [← hX, ← hY]
    field_simp
    have h4 : √Ω ^ 4 = Ω ^ 2 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hsΩ2]
    rw [hsΩ2, h4]
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [hL, h0] at hx
    simp at hx
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hsq1 : Real.sqrt (π * ‖w‖ ^ 2 / (π * Ω)) = ‖w‖ / √Ω := by
    rw [show π * ‖w‖ ^ 2 / (π * Ω) = ‖w‖ ^ 2 / Ω by field_simp, Real.sqrt_div' _ hΩ.le,
      Real.sqrt_sq hn.le]
  have hsq2 : Real.sqrt (π * ‖w‖ ^ 2 * Ω / π) = ‖w‖ * √Ω := by
    rw [show π * ‖w‖ ^ 2 * Ω / π = ‖w‖ ^ 2 * Ω by field_simp, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hn.le]
  have harg : 2 * π * (Complex.arg w / (2 * π)) = Complex.arg w := by field_simp
  simp only [lockToPhysicalR, lockX, lockY, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hL, harg, hsq1, hsq2, Complex.sin_arg, Complex.cos_arg hw0, hwre, hwim]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp only
    field_simp
    rw [hX]; ring
  · simp only
    field_simp
    rw [hY]; ring

end KAM.SpinOrbit.Lock

end
