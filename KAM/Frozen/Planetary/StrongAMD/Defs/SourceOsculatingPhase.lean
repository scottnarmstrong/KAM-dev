/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Defs.BodyVector
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Defs.PlaneLength
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscEcc
public import KAM.Frozen.Planetary.StrongAMD.Defs.OscEnergy

/-!
# Frozen definition `KAM.Planetary.StrongAMD.SourceOsculatingPhase`

Track LP, `LP:MAIN L16 (508–525)` (MAIN as amended by AMENDMENTS). Owner-approved on 2026-11-01
(decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This
file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved
versioned successor.

Freeze role (D59, OD-11 (b)): a source carrier (subtype or carrier predicate).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

/-- Source osculating phases (`LP:MAIN L16 (510–525)`): positive masses and `μ`, nonzero
positions, and nondegenerate actual-velocity ellipses (`E^osc < 0`, `e^osc < 1`). -/
abbrev SourceOsculatingPhase (n : ℕ) (ν : Fin n → ℝ) (μ : ℝ) :=
  {z : Phase (n * 2) // (∀ i, 0 < ν i) ∧ 0 < μ ∧
    ∀ i, 0 < planeLength (bodyVector z.1 i) ∧
      oscEnergy ν μ z i < 0 ∧ oscEcc ν μ z i < 1}

end KAM.Planetary.StrongAMD

end
