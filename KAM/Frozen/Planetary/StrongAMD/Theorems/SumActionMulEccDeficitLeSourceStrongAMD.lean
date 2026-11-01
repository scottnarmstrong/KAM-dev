/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.Planetary.Defs.KeplerAction
public import KAM.Frozen.Planetary.Defs.KeplerEccVector
public import KAM.Frozen.Planetary.Defs.PlaneLength
public import KAM.Frozen.Planetary.StrongAMD.Defs.EccDeficit
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceCanonicalPhase
public import KAM.Frozen.Planetary.StrongAMD.Defs.SourceStrongAMD
import KAM.Provider.Planetary.StrongAMD.SumActionMulEccDeficitLeSourceStrongAMD

/-!
# Frozen theorem `KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD`

Track LP characterization theorem of `sourceStrongAMD` (`LP:MAIN L3 (130–139)`), frozen with its
definition as one semantic unit (D59, OD-11 (b)). Owner-approved on 2026-11-01 (decision
D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This file is
frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved versioned
successor. Only the proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD z` when the provider
`KAM.Provider.Planetary.StrongAMD.SumActionMulEccDeficitLeSourceStrongAMD` is complete (sealing).
-/

@[expose] public section

namespace KAM.Planetary.StrongAMD

/-- The deficit bound `Σ_i Λ_i D(e_i) ≤ C` on source canonical phases
(`LP:MAIN L3 (130–139)`). -/
theorem sum_action_mul_eccDeficit_le_sourceStrongAMD {n : ℕ} {ν : Fin n → ℝ}
    (z : SourceCanonicalPhase n ν) :
    ∑ i, keplerAction ν z.1 i * eccDeficit (planeLength (keplerEccVector ν z.1 i)) ≤
      sourceStrongAMD z :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD z
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary.StrongAMD

end
-- FROZEN_ANCHOR_SUFFIX_END
