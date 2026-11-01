/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.StrongAMD.Defs.OrderedActions
public import KAM.Frozen.Planetary.StrongAMD.Defs.PairThreshold

/-!
# Frozen definition `KAM.Planetary.StrongAMD.orderedPairThreshold`

Track LP, `LP:MAIN §1 (3) (47–55), L4 (141–160)` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a source-facing definition on its carrier, frozen as one semantic unit
with its characterization theorems (draft 7, §4).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

/-- `B_ij` on the carrier `𝒬` (OD-2): the total helper `pairThreshold`, with the ordering
proof as typing data. -/
def orderedPairThreshold {n : ℕ} {ν : Fin n → ℝ} (I : OrderedActions ν) (i j : Fin n)
    (_hij : i < j) : ℝ :=
  pairThreshold ν I.1 i j

end KAM.Planetary.StrongAMD

end
