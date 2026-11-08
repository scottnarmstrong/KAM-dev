/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.HamExpr
public import KAM.Application.RealTorus
public import KAM.Certificate.PhaseBasis
public import KAM.Frozen.Magnetic.Defs.MagHamC
public import KAM.Frozen.Magnetic.Defs.MagField
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The magnetic Hamiltonian: expression, complex form and real field

* `magHamExpr_eval`: the certificate expression `magHamExpr` denotes the frozen `magHamC`;
* `magHamC_clock`: `∂_J magHamC ≡ 1` (the clock `φ = θ₁`);
* `realHam_magHamC`: on real arguments `magHamC` is `J + magH0 p + magV q φ`;
* `magProj_hamiltonianVectorField`: the real Hamiltonian field of `realHam magHamC`, projected to
  `(q, p, φ)`, is the frozen field-line field `magField`.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic

open KAM KAM.Certificate KAM.Application

/-! ### The expression and the complex Hamiltonian -/

theorem magHamExpr_eval_apply (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : magHamExpr.eval z = magHamC z := by
  have ha : modePhase 2 [2, -1] z.1 = 2 * (Real.pi : ℂ) * (2 * z.1 0 - z.1 1) := by
    simp [modePhase, certKeyFun, Fin.sum_univ_two]; ring
  have hb : modePhase 2 [3, -2] z.1 = 2 * (Real.pi : ℂ) * (3 * z.1 0 - 2 * z.1 1) := by
    simp [modePhase, certKeyFun, Fin.sum_univ_two]; ring
  simp only [magHamExpr, magHExpr, magVExpr, HamExpr.eval, ha, hb, magHamC, magEps]
  push_cast
  ring

/-- The certificate expression `magHamExpr` denotes the frozen Hamiltonian `magHamC`. -/
theorem magHamExpr_eval : magHamExpr.eval = magHamC := funext magHamExpr_eval_apply

theorem differentiable_magHamC : Differentiable ℂ magHamC := by
  unfold magHamC
  fun_prop

/-- **The clock**: `magHamC` is affine of slope `1` in the dummy action `J`, so
`∂_J magHamC ≡ 1`. -/
theorem magHamC_clock (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ magHamC z (phaseBasis (.inr 1)) = 1 := by
  have hline : HasDerivAt (fun t : ℂ => z + t • phaseBasis (.inr 1)) (phaseBasis (.inr 1)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (phaseBasis (.inr 1) :
      (Fin 2 → ℂ) × (Fin 2 → ℂ))).const_add z
  have hd' : HasFDerivAt magHamC (fderiv ℂ magHamC z) (z + (0 : ℂ) • phaseBasis (.inr 1)) := by
    simpa using (differentiable_magHamC z).hasFDerivAt
  have h1 := hd'.comp_hasDerivAt (x := (0 : ℂ)) hline
  have h2 : HasDerivAt (fun t : ℂ => magHamC (z + t • phaseBasis (.inr 1))) 1 0 := by
    have e : (fun t : ℂ => magHamC (z + t • phaseBasis (.inr 1))) =
        fun t => magHamC z + t := by
      funext t
      simp only [magHamC, phaseBasis_inr, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_zero,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp
      ring
    rw [e]
    simpa using (hasDerivAt_id (0 : ℂ)).const_add (magHamC z)
  exact h1.unique h2

/-! ### The real form -/

/-- The real Hamiltonian `J + magH0 p + magV q φ` on `((q, φ), (p, J))`. -/
def magHamR (y : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  y.2 1 + magH0 (y.2 0) + magV (y.1 0) (y.1 1)

theorem magHamC_ofReal (y : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    magHamC (realInclusion₂ 2 y) = (magHamR y : ℂ) := by
  simp only [realInclusion₂_apply, magHamC, magHamR, magH0, magV, magEps, realInclusion_eq_ofReal]
  push_cast
  ring

/-- On real arguments `magHamC` is `J + magH0 p + magV q φ`. -/
theorem realHam_magHamC : realHam magHamC = magHamR := by
  funext y
  rw [realHam, magHamC_ofReal, Complex.ofReal_re]

theorem differentiable_magH0 : Differentiable ℝ magH0 := by
  unfold magH0
  fun_prop

theorem differentiable_magV : Differentiable ℝ fun x : ℝ × ℝ => magV x.1 x.2 := by
  unfold magV
  fun_prop

theorem differentiable_magHamR : Differentiable ℝ magHamR := by
  have h1 : Differentiable ℝ fun y : (Fin 2 → ℝ) × (Fin 2 → ℝ) => magH0 (y.2 0) :=
    differentiable_magH0.comp (by fun_prop)
  have h2 : Differentiable ℝ fun y : (Fin 2 → ℝ) × (Fin 2 → ℝ) => magV (y.1 0) (y.1 1) :=
    differentiable_magV.comp (f := fun y : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (y.1 0, y.1 1))
      (by fun_prop)
  unfold magHamR
  exact ((differentiable_apply 1).comp differentiable_snd).add h1 |>.add h2

/-- The derivative of a differentiable function in a direction is the derivative along the line. -/
theorem fderiv_apply_of_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    {y v : E} (hd : DifferentiableAt ℝ F y) {d : ℝ}
    (hl : HasDerivAt (fun t : ℝ => F (y + t • v)) d 0) : fderiv ℝ F y v = d := by
  have hline : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hd' : HasFDerivAt F (fderiv ℝ F y) (y + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  exact (hd'.comp_hasDerivAt (x := (0 : ℝ)) hline).unique hl

/-- The projection `((q, φ), (p, J)) ↦ (q, p, φ)`. -/
def magProj : ((Fin 2 → ℝ) × (Fin 2 → ℝ)) →L[ℝ] ℝ × ℝ × ℝ :=
  ((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)).prod
      ((ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.fst ℝ _ _)))

@[simp] theorem magProj_apply (y : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    magProj y = (y.1 0, y.2 0, y.1 1) := rfl

/-- **The field-line field is the projected Hamiltonian field**: `X_H = (∂_I H, -∂_θ H)` of
`realHam magHamC`, read on `(q, p, φ)`, is `magField`. -/
theorem magProj_hamiltonianVectorField (y : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    magProj (hamiltonianVectorField (realHam magHamC) y) = magField (magProj y) := by
  rw [realHam_magHamC]
  have hd := differentiable_magHamR y
  have hp : fderiv ℝ magHamR y (0, Pi.single 0 1) = deriv magH0 (y.2 0) := by
    refine fderiv_apply_of_line hd ?_
    have e : (fun t : ℝ => magHamR (y + t • ((0 : Fin 2 → ℝ), (Pi.single 0 1 : Fin 2 → ℝ)))) =
        fun t => y.2 1 + magH0 (y.2 0 + t) + magV (y.1 0) (y.1 1) := by
      funext t; simp [magHamR]
    rw [e]
    have h := (differentiable_magH0 (y.2 0 + 0)).hasDerivAt.comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add (y.2 0))
    simp only [add_zero, mul_one] at h
    simpa using (h.const_add (y.2 1)).add_const (magV (y.1 0) (y.1 1))
  have hq : fderiv ℝ magHamR y (Pi.single 0 1, 0) = deriv (fun s => magV s (y.1 1)) (y.1 0) := by
    refine fderiv_apply_of_line hd ?_
    have e : (fun t : ℝ => magHamR (y + t • ((Pi.single 0 1 : Fin 2 → ℝ), (0 : Fin 2 → ℝ)))) =
        fun t => y.2 1 + magH0 (y.2 0) + magV (y.1 0 + t) (y.1 1) := by
      funext t; simp [magHamR]
    rw [e]
    have hdV : DifferentiableAt ℝ (fun s => magV s (y.1 1)) (y.1 0 + 0) :=
      (differentiable_magV.comp (f := fun s : ℝ => (s, y.1 1)) (by fun_prop)) _
    have h := hdV.hasDerivAt.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (y.1 0))
    simp only [add_zero, mul_one] at h
    exact h.const_add _
  have hJ : fderiv ℝ magHamR y (0, Pi.single 1 1) = 1 := by
    refine fderiv_apply_of_line hd ?_
    have e : (fun t : ℝ => magHamR (y + t • ((0 : Fin 2 → ℝ), (Pi.single 1 1 : Fin 2 → ℝ)))) =
        fun t => (y.2 1 + magH0 (y.2 0) + magV (y.1 0) (y.1 1)) + t := by
      funext t; simp [magHamR]; ring
    rw [e]
    simpa using (hasDerivAt_id (0 : ℝ)).const_add _
  simp only [magProj_apply, hamiltonianVectorField, magField, hp, hq, hJ]

end KAM.Magnetic

end
