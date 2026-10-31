/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.SpinOrbit.Defs.IsSyncOrbit

/-!
# Frozen definition `KAM.SpinOrbit.lunarSyncOrbit`

Owner-approved on 2026-10-31 (decision D49, route D45; docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md
§1, with the recommended answers of §2). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open Classical in
/-- The synchronous periodic orbit ψ* (unique by `lunarSyncOrbit_unique`). -/
def lunarSyncOrbit : ℝ → ℝ :=
  if h : ∃ ψ, IsSyncOrbit ψ then Classical.choose h else 0

end KAM.SpinOrbit

end
