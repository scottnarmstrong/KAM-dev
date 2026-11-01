/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.Planetary.Defs.KeplerAxis
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceCanonicalPhase
import KAM.Provider.Planetary.StrongAMD.SourceKeplerAxisPos

/-!
# Frozen theorem `KAM.Planetary.StrongAMD.sourceKepler_axis_pos`

Track LP characterization theorem of `SourceCanonicalPhase` (`LP:MAIN L2 (110–128)`), frozen with
its definition as one semantic unit (D59, OD-11 (b)). Owner-approved on 2026-11-01 (decision
D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This file is
frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved versioned
successor. Only the proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.StrongAMD.sourceKepler_axis_pos z i` when the provider
`KAM.Provider.Planetary.StrongAMD.SourceKeplerAxisPos` is complete (sealing).
-/

@[expose] public section

namespace KAM.Planetary.StrongAMD

/-- `0 < a_i` on source canonical phases (`LP:MAIN L2 (110–128)`). -/
theorem sourceKepler_axis_pos {n : ℕ} {ν : Fin n → ℝ} (z : SourceCanonicalPhase n ν) (i : Fin n) :
    0 < keplerAxis ν z.1 i :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.StrongAMD.sourceKepler_axis_pos z i
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary.StrongAMD

end
-- FROZEN_ANCHOR_SUFFIX_END
