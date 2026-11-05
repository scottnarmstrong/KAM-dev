/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.FrozenBridge

/-!
# Provider for the frozen theorem `KAM.SpinOrbit.lunarSyncOrbit_spec`

The proof of `KAM.SpinOrbit.lunarSyncOrbit_spec` is assembled here as
`KAM.Provider.SpinOrbit.lunarSyncOrbit_spec`, from the landed `KAM.SpinOrbit.Lock.syncOrbit_spec`
through the bridges of `KAM.SpinOrbit.Lock.FrozenBridge`. While the frozen anchor is `DRAFT_SORRY`,
this module is quarantined: no module other than the anchor may import it.
-/

@[expose] public section

namespace KAM.Provider.SpinOrbit
open KAM.SpinOrbit

/-- Quarantined provider signature; exact frozen telescope. -/
theorem lunarSyncOrbit_spec : IsSyncOrbit lunarSyncOrbit := by
  rw [Lock.frozen_lunarSyncOrbit_eq, Lock.frozen_isSyncOrbit_iff]
  exact Lock.syncOrbit_spec

end KAM.Provider.SpinOrbit
