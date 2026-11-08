/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.SpinOrbit.Defs.IsSyncOrbit
public import KAM.Frozen.SpinOrbit.Defs.LunarSyncOrbit
import KAM.Provider.SpinOrbit.LunarSyncOrbitUnique

/-!
# Frozen theorem `KAM.SpinOrbit.lunarSyncOrbit_unique`

Owner-approved on 2026-10-31 (decision D49, route D45; docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md
§1, with the recommended answers of §2). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.SpinOrbit.lunarSyncOrbit_unique ψ h` when the provider
`KAM.Provider.SpinOrbit.LunarSyncOrbitUnique` is complete (sealing).
-/

@[expose] public section

namespace KAM.SpinOrbit

theorem lunarSyncOrbit_unique (ψ : ℝ → ℝ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.SpinOrbit.lunarSyncOrbit_unique ψ h
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.SpinOrbit

end
-- FROZEN_ANCHOR_SUFFIX_END
