/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Orbital
public import KAM.Planetary.Spatial.Momentum
public import KAM.Planetary.Spatial.Osculating.Basic
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceAngularMomentum
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceCanonicalPhase
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerAction
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerAxis
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerEcc
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceKeplerEccVector
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceOsculatingPhase
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourcePlanetAngularMomentum
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialSourceStrongAMD

/-!
# Spatial source carriers and source-facing physical quantities (OD-11 (b))

Package LP-SP-SRC, `LP:MAIN §1 (2) (26–45)`, `L2 (110–128)`, `L3 (130–139)`, `L16 (508–529)` with
`d = 3`; track LP, non-frozen.  The statement surface is proposed in
docs/tracks/LP/FREEZE-PROPOSAL.md.

This answers audit note LP-W4A-1 N1: the unrestricted total helpers `spatialKeplerAxis`,
`spatialKeplerAction`, … stay internal and are not frozen as physical quantities.  Every physical
quantity is exposed through a source subtype.

* `SpatialSourceCanonicalPhase n ν` is the canonical carrier: it is `SpatialElliptic ν`, i.e. the
  subtype of `SpatialNegativeEnergy ν` (positive masses, `0 < |q_i|`, negative energy of every
  planet).
* `SpatialSourceOsculatingPhase n ν μ` is SP-OSC's `SpatialOscPhase n ν μ` (positive masses,
  `0 < μ`, `0 < |q_i|`, `E_i^osc < 0`, `e_i^osc < 1`).  Its source quantities are SP-OSC's
  `spatialSourceOsc*` (reused, not duplicated), as are `spatialSourceKeplerPeri/Apo` on the
  canonical carrier.
* The canonical source definitions `spatialSourceKeplerAxis`, `…Action`, `…EccVector`, `…Ecc`,
  `…PlanetAngularMomentum`, `…AngularMomentum`, `spatialSourceStrongAMD` each carry a `_def`
  equation proved by `rfl`.
* The characterizations (the semantic unit) are the facts of `spatial_orbital_identities` and
  Lemma 3, restated on the carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary

variable {n : ℕ}

/-! ### Carriers -/

/-- Membership in the canonical carrier is `SpatialNegativeEnergy`. -/
theorem spatialSourceCanonicalPhase_property {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) : SpatialNegativeEnergy ν z.1 := z.2

/-- Membership in the osculating carrier: positive masses, `0 < μ`, and the three planetary
conditions. -/
theorem spatialSourceOsculatingPhase_property {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) :
    (∀ i, 0 < ν i) ∧ 0 < μ ∧
      ∀ i, 0 < spaceLength (bodyVector3 z.1.1 i) ∧ spatialOscEnergy ν μ z.1 i < 0 ∧
        spatialOscEcc ν μ z.1 i < 1 := z.2

/-! ### Canonical source definitions -/

/-! ### Defining equations (`rfl`) -/

theorem spatialSourceKeplerAxis_def {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spatialSourceKeplerAxis z i = spatialKeplerAxis ν z.1 i := rfl

theorem spatialSourceKeplerAction_def {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) :
    spatialSourceKeplerAction z i = ν i * Real.sqrt (spatialSourceKeplerAxis z i) := rfl

theorem spatialSourceKeplerEccVector_def {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) :
    spatialSourceKeplerEccVector z i =
      (spaceSq (bodyVector3 z.1.2 i) / ν i ^ 2 - 1 / spaceLength (bodyVector3 z.1.1 i)) •
          bodyVector3 z.1.1 i -
        (spaceDot (bodyVector3 z.1.1 i) (bodyVector3 z.1.2 i) / ν i ^ 2) •
          bodyVector3 z.1.2 i := rfl

theorem spatialSourceKeplerEcc_def {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) :
    spatialSourceKeplerEcc z i = spaceLength (spatialSourceKeplerEccVector z i) := rfl

theorem spatialSourcePlanetAngularMomentum_def {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) (i : Fin n) :
    spatialSourcePlanetAngularMomentum z i =
      spaceCross (bodyVector3 z.1.1 i) (bodyVector3 z.1.2 i) := rfl

theorem spatialSourceAngularMomentum_def {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν) :
    spatialSourceAngularMomentum z = ∑ i, spatialSourcePlanetAngularMomentum z i := rfl

theorem spatialSourceStrongAMD_def {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν) :
    spatialSourceStrongAMD z =
      (∑ i, spatialSourceKeplerAction z i) - spaceLength (spatialSourceAngularMomentum z) := rfl

/-- The source strong AMD is SP-MODEL's `spatialStrongAMDOn` on the carrier. -/
theorem spatialSourceStrongAMD_eq_on {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν) :
    spatialSourceStrongAMD z = spatialStrongAMDOn ν z := rfl

/-- `a (1 − e)` on the canonical carrier (SP-OSC's `spatialSourceKeplerPeri`) in source
quantities. -/
theorem spatialSourceKeplerPeri_eq_source {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) :
    spatialSourceKeplerPeri z i = spatialSourceKeplerAxis z i * (1 - spatialSourceKeplerEcc z i) :=
  rfl

/-- `a (1 + e)` on the canonical carrier (SP-OSC's `spatialSourceKeplerApo`) in source
quantities. -/
theorem spatialSourceKeplerApo_eq_source {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) :
    spatialSourceKeplerApo z i = spatialSourceKeplerAxis z i * (1 + spatialSourceKeplerEcc z i) :=
  rfl

/-! ### Characterizations of the canonical source quantities (`LP:MAIN L2`, `L3`) -/

/-- `0 < a_i` (`LP:MAIN L2 (110–128)`, `d = 3`). -/
theorem spatialSourceKeplerAxis_pos {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : 0 < spatialSourceKeplerAxis z i :=
  (spatial_orbital_identities i (z.2 i)).1

/-- `0 < Λ_i`. -/
theorem spatialSourceKeplerAction_pos {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : 0 < spatialSourceKeplerAction z i :=
  (spatial_orbital_identities i (z.2 i)).2.1

/-- `Λ_i² = ν_i² a_i` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerAction_sq {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spatialSourceKeplerAction z i ^ 2 = ν i ^ 2 * spatialSourceKeplerAxis z i :=
  (spatial_orbital_identities i (z.2 i)).2.2.1

/-- `e_i² = 1 − |L_i|²/Λ_i²` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerEcc_sq {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) :
    spatialSourceKeplerEcc z i ^ 2 =
      1 - spaceLength (spatialSourcePlanetAngularMomentum z i) ^ 2 /
        spatialSourceKeplerAction z i ^ 2 :=
  (spatial_orbital_identities i (z.2 i)).2.2.2.1

/-- `0 ≤ e_i`. -/
theorem spatialSourceKeplerEcc_nonneg {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : 0 ≤ spatialSourceKeplerEcc z i :=
  spaceLength_nonneg _

/-- `e_i ≤ 1` (`LP:MAIN L2 (110–128)`; the radial case `e_i = 1` is included). -/
theorem spatialSourceKeplerEcc_le_one {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spatialSourceKeplerEcc z i ≤ 1 :=
  (spatial_orbital_identities i (z.2 i)).2.2.2.2.1

/-- `|L_i| = Λ_i √(1 − e_i²)` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourcePlanetAngularMomentum_length {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) (i : Fin n) :
    spaceLength (spatialSourcePlanetAngularMomentum z i) =
      spatialSourceKeplerAction z i * Real.sqrt (1 - spatialSourceKeplerEcc z i ^ 2) :=
  (spatial_orbital_identities i (z.2 i)).2.2.2.2.2.1

/-- `|L_i| ≤ Λ_i`. -/
theorem spatialSourcePlanetAngularMomentum_length_le {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) (i : Fin n) :
    spaceLength (spatialSourcePlanetAngularMomentum z i) ≤ spatialSourceKeplerAction z i :=
  (spatial_orbital_identities i (z.2 i)).2.2.2.2.2.2.1

/-- Tangency on the canonical carrier: `a_i (1 − e_i) ≤ |q_i|` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerPeri_le_length {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spatialSourceKeplerPeri z i ≤ spaceLength (bodyVector3 z.1.1 i) :=
  (spatial_orbital_identities i (z.2 i)).2.2.2.2.2.2.2.1

/-- Tangency on the canonical carrier: `|q_i| ≤ a_i (1 + e_i)` (`LP:MAIN L2 (110–128)`). -/
theorem spatialSourceKeplerApo_ge_length {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν)
    (i : Fin n) : spaceLength (bodyVector3 z.1.1 i) ≤ spatialSourceKeplerApo z i :=
  (spatial_orbital_identities i (z.2 i)).2.2.2.2.2.2.2.2.1

/-- `0 ≤ C` on the canonical carrier (`LP:MAIN L3 (130–139)`). -/
theorem spatialSourceStrongAMD_nonneg {ν : Fin n → ℝ} (z : SpatialSourceCanonicalPhase n ν) :
    0 ≤ spatialSourceStrongAMD z :=
  spatialStrongAMD_nonneg z.2

/-- `Σ_i Λ_i (1 − √(1 − e_i²)) ≤ C` on the canonical carrier (`LP:MAIN L3 (130–139)`). -/
theorem spatialSourceAction_mul_eccDeficit_le {ν : Fin n → ℝ}
    (z : SpatialSourceCanonicalPhase n ν) :
    ∑ i, spatialSourceKeplerAction z i * (1 - Real.sqrt (1 - spatialSourceKeplerEcc z i ^ 2)) ≤
      spatialSourceStrongAMD z :=
  sum_action_mul_eccDeficit_le_spatialStrongAMD z.2

/-! ### Characterizations of the osculating source quantities (`LP:MAIN L16`) -/

/-- On the osculating carrier: `0 < k_i`. -/
theorem spatialSourceOscParam_pos {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 < spatialSourceOscParam z i := by
  obtain ⟨hν, hμ, -⟩ := z.2
  unfold spatialSourceOscParam spatialOscParam
  nlinarith [mul_pos hμ (hν i)]

/-- On the osculating carrier: `E_i^osc < 0`. -/
theorem spatialSourceOscEnergy_neg {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : spatialSourceOscEnergy z i < 0 :=
  (z.2.2.2 i).2.1

/-- On the osculating carrier: `e_i^osc < 1`. -/
theorem spatialSourceOscEcc_lt_one {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : spatialSourceOscEcc z i < 1 :=
  (z.2.2.2 i).2.2

/-- On the osculating carrier: `0 ≤ e_i^osc`. -/
theorem spatialSourceOscEcc_nonneg {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 ≤ spatialSourceOscEcc z i :=
  spaceLength_nonneg _

/-- On the osculating carrier: `0 < a_i^osc` (SP-OSC's `spatialOscPhase_ellipse`). -/
theorem spatialSourceOscAxis_pos {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 < spatialSourceOscAxis z i :=
  (spatialOscPhase_ellipse z i).1

/-- On the osculating carrier: `0 < a^osc (1 − e^osc)`. -/
theorem spatialSourceOscPeri_pos {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) : 0 < spatialSourceOscPeri z i :=
  (spatialOscPhase_ellipse z i).2.1

/-- Tangency on the osculating carrier: `a^osc (1 − e^osc) ≤ |q_i|`. -/
theorem spatialSourceOscPeri_le_length {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) :
    spatialSourceOscPeri z i ≤ spaceLength (bodyVector3 z.1.1 i) :=
  (spatialOscPhase_ellipse z i).2.2.1

/-- Tangency on the osculating carrier: `|q_i| ≤ a^osc (1 + e^osc)`. -/
theorem spatialSourceOscApo_ge_length {ν : Fin n → ℝ} {μ : ℝ}
    (z : SpatialSourceOsculatingPhase n ν μ) (i : Fin n) :
    spaceLength (bodyVector3 z.1.1 i) ≤ spatialSourceOscApo z i :=
  (spatialOscPhase_ellipse z i).2.2.2

end KAM.Planetary.Spatial

end
