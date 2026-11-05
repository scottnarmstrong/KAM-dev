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
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceCanonicalPhase
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceKeplerApo
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceKeplerPeri
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscApo
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscAxis
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEcc
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEccVector
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscEnergy
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscParam
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscPeri
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscVelocity
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOsculatingPhase
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceStrongAMD

/-!
# Source carriers for the strong AMD and the osculating ellipses (OD-11 option (b))

Source: (`LP:MAIN §1 (31–37)`, `L16 (510–525)`), track LP, non-frozen.

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

/-! ### Defining equations -/

/-! ### Characterizations -/

theorem SourceCanonicalPhase.hz {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) :
    ∀ i, 0 < ν i ∧ 0 < planeLength (bodyVector z.1.1 i) ∧ keplerEnergy ν z.1 i < 0 :=
  fun i => ⟨z.2.1 i, z.2.2 i⟩

/-- `C = Σ_i Λ_i - |L|` on source canonical phases (`LP:MAIN §1 (2)`). -/
theorem sourceStrongAMD_eq {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) :
    sourceStrongAMD z = (∑ i, keplerAction ν z.1 i) - |totalMomentum z.1| := rfl

end KAM.Planetary.StrongAMD
