/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.LaplaceIdentities
public import KAM.Planetary.Poincare.Chart
public import KAM.Kepler.Equation

/-!
# Secular form: quartic data, definitions

Blueprint P, Part 8, `bpP:p8:quartic`: the six quartic invariant monomials, the exact radial
coefficient `radialR1`, and the dimensionless separated pair average (`unitPosition`,
`separatedDomain`, `dimensionlessPair`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

def quarticMonomials (u v : Fin 2 → ℝ) : Fin 6 → ℝ :=
  ![planeSq u^2, planeSq v^2, planeSq u*planeSq v, planeDot u v^2,
    planeSq u*planeDot u v, planeSq v*planeDot u v]

def radialR1 (a b : ℝ) : ℝ := -iteratedDeriv 4 (radialH a b) 0 / 32 +
  iteratedDeriv 2 (radialH a b) 0 / 8

/-- Exact dimensionless separated pair average. -/
def unitPosition (t : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let F := keplerLong t v
  let k := √(1-planeSq v)
  k • orbitalUnit F - v + (planeDot v (orbitalUnit F)/(1+k)) • v

def separatedDomain : Set (ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
  {z | 0 < z.1 ∧ z.1 < 1 ∧ planeLength z.2.1 < 1/4 ∧ planeLength z.2.2 < 1/4 ∧
    z.1*(1+planeLength z.2.1) < 1-planeLength z.2.2}

def dimensionlessPair (z : ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  (2*π)⁻¹ * ∫ s in (0:ℝ)..2*π, (2*π)⁻¹ * ∫ t in (0:ℝ)..2*π,
    (planeLength (z.1 • unitPosition s z.2.1 - unitPosition t z.2.2))⁻¹

end SecularForm
end KAM.Planetary
end
