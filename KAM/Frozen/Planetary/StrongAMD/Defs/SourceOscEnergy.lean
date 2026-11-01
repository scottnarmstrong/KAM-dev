/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.StrongAMD.Defs.OscEnergy
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOsculatingPhase

/-!
# Frozen definition `KAM.Planetary.StrongAMD.sourceOscEnergy`

Track LP, `LP:MAIN L16 (42) (510–520)` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a source-facing definition on its carrier, frozen as one semantic unit
with its characterization theorems (draft 7, §4).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

/-- Osculating energy on source osculating phases. -/
def sourceOscEnergy {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ} (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : ℝ :=
  oscEnergy ν μ z.1 i

end KAM.Planetary.StrongAMD

end
