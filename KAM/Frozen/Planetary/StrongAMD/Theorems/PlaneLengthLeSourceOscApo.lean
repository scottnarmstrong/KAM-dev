/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.Planetary.Defs.BodyVector
public import KAM.Frozen.Planetary.Defs.PlaneLength
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOscApo
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceOsculatingPhase
import KAM.Provider.Planetary.StrongAMD.PlaneLengthLeSourceOscApo

/-!
# Frozen theorem `KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo`

Track LP characterization theorem of `sourceOscApo` (`LP:MAIN L16 (527–528)`), frozen with its
definition as one semantic unit (D59, OD-11 (b)). Owner-approved on 2026-11-01 (decision
D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This file is
frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved versioned
successor. Only the proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo z i` when the provider
`KAM.Provider.Planetary.StrongAMD.PlaneLengthLeSourceOscApo` is complete (sealing).
-/

@[expose] public section

namespace KAM.Planetary.StrongAMD

/-- `|q_i| ≤ a^osc (1 + e^osc)` on source osculating phases (`LP:MAIN L16 (527–528)`). -/
theorem planeLength_le_sourceOscApo {n : ℕ} {ν : Fin n → ℝ} {μ : ℝ}
    (z : SourceOsculatingPhase n ν μ)
    (i : Fin n) : planeLength (bodyVector z.1.1 i) ≤ sourceOscApo z i :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo z i
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary.StrongAMD

end
-- FROZEN_ANCHOR_SUFFIX_END
