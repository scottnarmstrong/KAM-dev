/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.AMDBox
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.Slow
public import KAM.Planetary.Newtonian.Models
public import KAM.Planetary.Poincare.Product

/-!
# Enlarged analytic data: the setting of the exponential-safety package

Blueprint P, Part 14 (`bpP:p14:sec-domain#data`): the chart AMD `chartAMD`, the Poincaré chart's
collision-free domain `chartSafe`, the fast action box `fastBox`, the slow ball `slowBall`, the
enlarged and working cylinders, the enlargement data `EnlargedData`, and the complexified Kepler
part `planetaryKeplerC`.  Definitions only: no conclusion is stated as a hypothesis.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {n : ℕ}

/-- The chart AMD `∑ (ξ_i² + η_i²) / 2` of a point of `Phase (n + n)`. -/
def chartAMD (w : Phase (n + n)) : ℝ :=
  ∑ i, ((slow w.1 i)^2 + (slow w.2 i)^2) / 2

/-- The part of the Poincaré chart domain mapping into the collision-free domain. -/
def chartSafe (m : Fin n → ℝ) : Set (Phase (n + n)) :=
  poincareProdDom n ∩ poincareProd m 1 ⁻¹' collisionFreeDomain n

/-- The open max-norm action box enlarged by `kappa`. -/
def fastBox (B : AMDBox n) (kappa : ℝ) : Set (Fin n → ℝ) :=
  {I | ∀ i, B.lower i - kappa < I i ∧ I i < B.upper i + kappa}

/-- The quadratic slow ball. -/
def slowBall (n : ℕ) (A : ℝ) : Set (Phase n) :=
  {y | ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) / 2 < A}

/-- The enlarged cylinder in chart coordinates. -/
def enlargedCylinder (B : AMDBox n) (kappa A : ℝ) : Set (Phase (n + n)) :=
  {w | (∀ i, B.lower i - 2 * kappa ≤ fast w.2 i ∧
    fast w.2 i ≤ B.upper i + 2 * kappa) ∧ chartAMD w ≤ A}

/-- The working cylinder in chart coordinates. -/
def workingCylinder (B : AMDBox n) (kappa A : ℝ) : Set (Phase (n + n)) :=
  {w | fast w.2 ∈ fastBox B kappa ∧ (slow w.1, slow w.2) ∈ slowBall n A}

/-- The enlargement data: source inequalities only. -/
structure EnlargedData (B : AMDBox n) (kappa e A : ℝ) : Prop where
  kappa_pos : 0 < kappa
  ecc_lt : B.ecc < e
  ecc_one : e < 1
  amd_lt : B.outerAMD < A
  small : ∀ i, kappa ≤ B.lower i / 8
  deficit : ∀ i, A < (B.lower i - 2 * kappa) * (1 - Real.sqrt (1 - e^2))
  radii : ∀ i, B.distance / 2 ≤ ((B.lower i - 2 * kappa) / B.mass i)^2 * (1-e)
  gaps : ∀ i j, i < j → ((B.upper i + 2 * kappa) / B.mass i)^2 * (1+e) +
    B.distance / 2 ≤ ((B.lower j - 2 * kappa) / B.mass j)^2 * (1-e)

/-- The complexified Kepler part `-∑ m_i³ / (2 I_i²)`. -/
def planetaryKeplerC (m : Fin n → ℝ) (I : Fin n → ℂ) : ℂ :=
  -∑ i, (m i : ℂ)^3 / (2 * I i ^ 2)

end KAM.Planetary
