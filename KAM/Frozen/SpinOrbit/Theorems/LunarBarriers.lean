/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.SpinOrbit.Defs.SoBarrier
public import KAM.Frozen.SpinOrbit.Defs.LunarPLo
public import KAM.Frozen.SpinOrbit.Defs.LunarPHi
import KAM.Provider.SpinOrbit.LunarBarriers

/-!
# Frozen theorem `KAM.SpinOrbit.lunar_barriers`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D47 and
D49). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor. Only the proof body between the markers may change, and only to
`by exact KAM.Provider.SpinOrbit.lunar_barriers …` when the provider
`KAM.Provider.SpinOrbit.LunarBarriers` is complete (sealing).
-/

@[expose] public section

namespace KAM.SpinOrbit

/-- **Theorem A (continuous form).** In the seven-mode lunar spin–orbit model there are two
invariant
continuous barrier graphs with values in the band `[0.97245, 1.02755]`, the lower one strictly below
the
window end `lunarPLo` and the upper one strictly above `lunarPHi`. -/
theorem lunar_barriers :
    ∃ (Bm : SoBarrier (97245 / 100000) (102755 / 100000))
      (Bp : SoBarrier (97245 / 100000) (102755 / 100000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < lunarPLo) ∧ (∀ q φ, (lunarPHi : ℝ) < Bp.P q φ) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.SpinOrbit

end
-- FROZEN_ANCHOR_SUFFIX_END
