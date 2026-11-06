/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.PolarForm
public import KAM.EffectiveStability.SJSU.Ham.Center
public import KAM.EffectiveStability.Tube.Poly.HTildeBounds
public import KAM.EffectiveStability.Tube.Chart.Observable

/-!
# Rates of tube observables along `SJSU18-O2` (T2-CONF, N5a)

N2's composite rate formula instantiated for `SJSU18-O2`, the rotation `V′` and the shift `B`: for
an observable `f` of `(u, φ)`, `2π`-periodic in `φ`, and a phase point `x` whose rotated modes are
all nonzero, the rate of `x ↦ f (tubeChart V′ B x)` along `X_H` is the reduced bracket of `f` and
`h̃ = sjsuHTilde B` at the chart image (`sjsu18O2_rate`). Every chart hypothesis of N2 is discharged
here; only the regularity and periodicity of `f` remain.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube Matrix Real

/-- N2's chart identity for `SJSU18-O2` on positive actions. -/
theorem sjsu18O2_chart (y : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (hy : y ∈ actionPos 3) :
    sjsu18O2 (rotMap sjsuV (polar y)) = sjsuHTilde sjsuB (shiftChart sjsuB y) :=
  sjsu18O2_rotMap_polar sjsuB y fun j => (hy j).le

/-- `h̃` is differentiable at the chart image of a point with positive actions. -/
theorem differentiableAt_sjsuHTilde_shiftChart (y : (Fin 3 → ℝ) × (Fin 3 → ℝ))
    (hy : y ∈ actionPos 3) : DifferentiableAt ℝ (sjsuHTilde sjsuB) (shiftChart sjsuB y) :=
  differentiableAt_hTildeOf sjsuE sjsuN sjsuHwAll sjsuB
    (contDiff_sjsuB (n := 1).differentiable one_ne_zero _)
    (fun j => by simpa [shiftChart] using hy j)

/-- **The rate formula for `SJSU18-O2`.** -/
theorem sjsu18O2_rate (f : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ)
    (hfper : ∀ (u : Fin 3 → ℝ) (φ : Fin 2 → ℝ) (m : Fin 2 → ℤ),
      f (u, φ + fun a => 2 * π * m a) = f (u, φ))
    {x : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    (hx : ∀ j, 0 < (rotMap sjsuVᵀ x).1 j ^ 2 + (rotMap sjsuVᵀ x).2 j ^ 2)
    (hf : DifferentiableAt ℝ f (tubeChart sjsuV sjsuB x)) :
    fderiv ℝ (fun x => f (tubeChart sjsuV sjsuB x)) x (KAM.hamiltonianVectorField sjsu18O2 x) =
      reducedBracket f (sjsuHTilde sjsuB) (tubeChart sjsuV sjsuB x) :=
  fderiv_comp_tubeChart_apply_hamiltonianVectorField sjsuV_orth sjsuB_add_two_pi hfper
    sjsu18O2_chart hx hf
    (differentiableAt_sjsuHTilde_shiftChart _ (polarInv_mem_actionPos hx))
    (contDiff_sjsuB (n := 1).differentiable one_ne_zero _)
    (sjsuB_symm _)

end KAM.EffectiveStability.SJSU

end
