/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.Momentum
public import KAM.Planetary.StrongAMD.Orbital
public import KAM.Planetary.StrongAMD.Osculating.Basic
public import KAM.Planetary.StrongAMD.Threshold.Defs

/-!
# Source carriers for the strong AMD and the osculating ellipses (OD-11 option (b))

Package LP-SRC (statement review F4: `LP:MAIN §1 (31–37)`, `L16 (510–525)`), track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

The total formulas `strongAMD`, `keplerPeri/Apo`, `oscVelocity/oscParam/oscEnergy/oscAxis/
oscEccVector/oscEcc/oscPeri/oscApo` are defined on every phase.  The source objects live on the
source subtypes `SourceCanonicalPhase` (positive masses, `0 < |q_i|`, `E_i < 0`) and
`SourceOsculatingPhase` (positive `ν`, `μ`, `0 < |q_i|`, `E_i^osc < 0`, `e_i^osc < 1`).  Each
`source*` definition is the total helper on the subtype (`rfl` lemmas).

Characterizations (the semantic unit):
* `sourceStrongAMD_eq`, `sourceStrongAMD_nonneg`, `sum_action_mul_eccDeficit_le_sourceStrongAMD`
  (`LP:MAIN L3 (130–139)`);
* `sourceKepler_axis_pos`, `sourceKepler_ecc_le_one`, `sourceKeplerPeri_le_planeLength`,
  `planeLength_le_sourceKeplerApo` (`LP:MAIN L2 (110–128)`);
* `sourceOscAxis_pos`, `sourceOscPeri_pos`, `sourceOscPeri_le_planeLength`,
  `planeLength_le_sourceOscApo` (`LP:MAIN L16 (527–528)`): the osculating ellipse is a genuine
  ellipse through the current position.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary

variable {n : ℕ}

/-- Source canonical phases (`LP:MAIN §1 (31–37)`): positive masses, and every planet at a
nonzero position with negative Kepler energy. -/
abbrev SourceCanonicalPhase (n : ℕ) (ν : Fin n → ℝ) :=
  {z : Phase (n * 2) // (∀ i, 0 < ν i) ∧
    ∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0}

/-- Source osculating phases (`LP:MAIN L16 (510–525)`): positive masses and `μ`, nonzero
positions, and nondegenerate actual-velocity ellipses (`E^osc < 0`, `e^osc < 1`). -/
abbrev SourceOsculatingPhase (n : ℕ) (ν : Fin n → ℝ) (μ : ℝ) :=
  {z : Phase (n * 2) // (∀ i, 0 < ν i) ∧ 0 < μ ∧
    ∀ i, 0 < planeLength (bodyVector z.1 i) ∧
      oscEnergy ν μ z i < 0 ∧ oscEcc ν μ z i < 1}

/-- The strong AMD on source canonical phases. -/
def sourceStrongAMD {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) : ℝ := strongAMD ν z.1

/-- Canonical perihelion on source canonical phases. -/
def sourceKeplerPeri {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) : ℝ :=
  keplerPeri ν z.1 i

/-- Canonical aphelion on source canonical phases. -/
def sourceKeplerApo {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) : ℝ :=
  keplerApo ν z.1 i

/-- Actual heliocentric velocity on source osculating phases. -/
def sourceOscVelocity {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    Fin 2 → ℝ := oscVelocity ν μ z.1 i

/-- Gravitational parameter `1 + μ ν_i` on source osculating phases. -/
def sourceOscParam {ν : Fin n → ℝ} {μ : ℝ} (_z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscParam ν μ i

/-- Osculating energy on source osculating phases. -/
def sourceOscEnergy {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscEnergy ν μ z.1 i

/-- Osculating semi-major axis on source osculating phases. -/
def sourceOscAxis {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscAxis ν μ z.1 i

/-- Osculating eccentricity vector on source osculating phases. -/
def sourceOscEccVector {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    Fin 2 → ℝ := oscEccVector ν μ z.1 i

/-- Osculating eccentricity on source osculating phases. -/
def sourceOscEcc {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscEcc ν μ z.1 i

/-- Osculating perihelion on source osculating phases. -/
def sourceOscPeri {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscPeri ν μ z.1 i

/-- Osculating aphelion on source osculating phases. -/
def sourceOscApo {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) : ℝ :=
  oscApo ν μ z.1 i

/-! ### Defining equations -/

theorem sourceStrongAMD_def {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) :
    sourceStrongAMD z = strongAMD ν z.1 := rfl

theorem sourceKeplerPeri_def {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) :
    sourceKeplerPeri z i = keplerPeri ν z.1 i := rfl

theorem sourceKeplerApo_def {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) :
    sourceKeplerApo z i = keplerApo ν z.1 i := rfl

theorem sourceOscVelocity_def {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : sourceOscVelocity z i = oscVelocity ν μ z.1 i := rfl

theorem sourceOscParam_def {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    sourceOscParam z i = oscParam ν μ i := rfl

theorem sourceOscEnergy_def {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : sourceOscEnergy z i = oscEnergy ν μ z.1 i := rfl

theorem sourceOscAxis_def {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    sourceOscAxis z i = oscAxis ν μ z.1 i := rfl

theorem sourceOscEccVector_def {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : sourceOscEccVector z i = oscEccVector ν μ z.1 i := rfl

theorem sourceOscEcc_def {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    sourceOscEcc z i = oscEcc ν μ z.1 i := rfl

theorem sourceOscPeri_def {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    sourceOscPeri z i = oscPeri ν μ z.1 i := rfl

theorem sourceOscApo_def {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ) (i : Fin n) :
    sourceOscApo z i = oscApo ν μ z.1 i := rfl

/-! ### Characterizations -/

theorem SourceCanonicalPhase.hz {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) :
    ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1.1 i) ∧ keplerEnergy ν z.1 i < 0 :=
  fun i => ⟨z.2.1 i, z.2.2 i⟩

/-- `C = Σ_i Λ_i - |L|` on source canonical phases (`LP:MAIN §1 (2)`). -/
theorem sourceStrongAMD_eq {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) :
    sourceStrongAMD z = (∑ i, keplerAction ν z.1 i) - |totalMomentum z.1| := rfl

/-- `0 ≤ C` on source canonical phases (`LP:MAIN L3 (130–139)`). -/
theorem sourceStrongAMD_nonneg {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) :
    0 ≤ sourceStrongAMD z := strongAMD_nonneg z.hz

/-- The deficit bound `Σ_i Λ_i D(e_i) ≤ C` on source canonical phases
(`LP:MAIN L3 (130–139)`). -/
theorem sum_action_mul_eccDeficit_le_sourceStrongAMD {ν : Fin n → ℝ}
    (z : SourceCanonicalPhase n ν) :
    ∑ i, keplerAction ν z.1 i * eccDeficit (planeLength (keplerEccVector ν z.1 i)) ≤
      sourceStrongAMD z :=
  sum_action_mul_eccDeficit_le_strongAMD z.hz

/-- `0 < a_i` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem sourceKepler_axis_pos {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) :
    0 < keplerAxis ν z.1 i := (orbital_identities i (z.hz i)).1

/-- `e_i ≤ 1` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem sourceKepler_ecc_le_one {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) :
    planeLength (keplerEccVector ν z.1 i) ≤ 1 := (orbital_identities i (z.hz i)).2.2.2.2.1

/-- `a_i (1 - e_i) ≤ |q_i|` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem sourceKeplerPeri_le_planeLength {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν)
    (i : Fin n) : sourceKeplerPeri z i ≤ planeLength (bodyVector z.1.1 i) :=
  (orbital_identities i (z.hz i)).2.2.2.2.2.2.2.1

/-- `|q_i| ≤ a_i (1 + e_i)` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem planeLength_le_sourceKeplerApo {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν)
    (i : Fin n) : planeLength (bodyVector z.1.1 i) ≤ sourceKeplerApo z i :=
  (orbital_identities i (z.hz i)).2.2.2.2.2.2.2.2.1

/-- `0 < a_i^osc` on source osculating phases (`LP:MAIN L16 (527–528)`). -/
theorem sourceOscAxis_pos {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : 0 < sourceOscAxis z i :=
  (osc_tangency ν z.2.2.1.le (z.2.1 i) (z.2.2.2 i).1 (z.2.2.2 i).2.1).1

/-- `0 < a_i^osc (1 - e_i^osc)` on source osculating phases. -/
theorem sourceOscPeri_pos {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : 0 < sourceOscPeri z i :=
  mul_pos (sourceOscAxis_pos z i) (by linarith [(z.2.2.2 i).2.2])

/-- `a^osc (1 - e^osc) ≤ |q_i|` on source osculating phases (`LP:MAIN L16 (527–528)`). -/
theorem sourceOscPeri_le_planeLength {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : sourceOscPeri z i ≤ planeLength (bodyVector z.1.1 i) :=
  (osc_tangency ν z.2.2.1.le (z.2.1 i) (z.2.2.2 i).1 (z.2.2.2 i).2.1).2.1

/-- `|q_i| ≤ a^osc (1 + e^osc)` on source osculating phases (`LP:MAIN L16 (527–528)`). -/
theorem planeLength_le_sourceOscApo {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : planeLength (bodyVector z.1.1 i) ≤ sourceOscApo z i :=
  (osc_tangency ν z.2.2.1.le (z.2.1 i) (z.2.2.2 i).1 (z.2.2.2 i).2.1).2.2

end KAM.Planetary.StrongAMD
