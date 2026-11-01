/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Vector

/-!
# Kepler elements, angular momentum and strong AMD in dimension three

Package LP-SP-MODEL, `LP:MAIN §1 (2) (26–45)` with `d = 3`; track LP, non-frozen; the statement
surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The total (uncarried) definitions follow the planar frozen convention (mass argument `ν`, total
Kepler energy `ν_i E_i`); they carry meaning only on the negative-energy carrier
`SpatialNegativeEnergy ν z`.  Per OD-11 (b) the carrier is explicit: `SpatialNegativeEnergy`, the
subtype `SpatialElliptic ν`, and `spatialStrongAMDOn` on it with its characterization.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary

variable {n : ℕ}

/-- Total Kepler energy `ν_i E_i` of planet `i` (planar convention). -/
def spatialKeplerEnergy (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  spaceSq (bodyVector3 z.2 i) / (2 * ν i) - ν i / spaceLength (bodyVector3 z.1 i)

/-- Osculating semimajor axis `a_i = −ν_i/(2 ν_i E_i)`. -/
def spatialKeplerAxis (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  -ν i / (2 * spatialKeplerEnergy ν z i)

/-- Kepler action `Λ_i = ν_i √a_i`. -/
def spatialKeplerAction (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : ℝ :=
  ν i * Real.sqrt (spatialKeplerAxis ν z i)

/-- Eccentricity vector `𝐞_i = (|v|² − 1/|q|) q − (q·v) v` with `v = p/ν`. -/
def spatialKeplerEccVector (ν : Fin n → ℝ) (z : Phase (n * 3)) (i : Fin n) : Fin 3 → ℝ :=
  let q := bodyVector3 z.1 i
  let p := bodyVector3 z.2 i
  (spaceSq p / ν i ^ 2 - 1 / spaceLength q) • q - (spaceDot q p / ν i ^ 2) • p

/-- Individual angular momentum `L_i = q_i × p_i`. -/
def planetAngularMomentum3 (z : Phase (n * 3)) (i : Fin n) : Fin 3 → ℝ :=
  spaceCross (bodyVector3 z.1 i) (bodyVector3 z.2 i)

/-- Total angular momentum `L = Σ_i q_i × p_i`. -/
def angularMomentum3 (z : Phase (n * 3)) : Fin 3 → ℝ :=
  ∑ i, spaceCross (bodyVector3 z.1 i) (bodyVector3 z.2 i)

/-- The strong AMD `C = Σ_i Λ_i − |L|` (`LP:MAIN §1 (2)`), `|L|` the Euclidean length. -/
def spatialStrongAMD (ν : Fin n → ℝ) (z : Phase (n * 3)) : ℝ :=
  (∑ i, spatialKeplerAction ν z i) - spaceLength (angularMomentum3 z)

/-- The source carrier of the Kepler elements: positive masses, no planet at the star, negative
energy of every planet. -/
def SpatialNegativeEnergy (ν : Fin n → ℝ) (z : Phase (n * 3)) : Prop :=
  ∀ i, 0 < ν i ∧ 0 < spaceLength (bodyVector3 z.1 i) ∧ spatialKeplerEnergy ν z i < 0

/-- Phase points of the carrier. -/
def SpatialElliptic (ν : Fin n → ℝ) : Type := {z : Phase (n * 3) // SpatialNegativeEnergy ν z}

/-- The strong AMD on its carrier. -/
def spatialStrongAMDOn (ν : Fin n → ℝ) (z : SpatialElliptic ν) : ℝ := spatialStrongAMD ν z.1

/-- Characterization: on the carrier, the strong AMD is the total one. -/
theorem spatialStrongAMDOn_eq (ν : Fin n → ℝ) (z : SpatialElliptic ν) :
    spatialStrongAMDOn ν z = spatialStrongAMD ν z.1 := rfl

theorem angularMomentum3_eq_sum (z : Phase (n * 3)) :
    angularMomentum3 z = ∑ i, planetAngularMomentum3 z i := rfl

end KAM.Planetary.Spatial

end
