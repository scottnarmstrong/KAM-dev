/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.FrozenBridge

/-!
# Provider for the frozen theorem `KAM.SpinOrbit.lunarSyncOrbit_unique`

The proof of `KAM.SpinOrbit.lunarSyncOrbit_unique` is assembled here as
`KAM.Provider.SpinOrbit.lunarSyncOrbit_unique`, from the landed
`KAM.SpinOrbit.Lock.syncOrbit_unique` through the bridges of `KAM.SpinOrbit.Lock.FrozenBridge`.
While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.
-/

@[expose] public section

namespace KAM.Provider.SpinOrbit
open KAM.SpinOrbit

/-- Quarantined provider signature; exact frozen telescope. -/
theorem lunarSyncOrbit_unique (ψ : ℝ → ℝ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit := by
  rw [Lock.frozen_lunarSyncOrbit_eq]
  exact Lock.syncOrbit_unique ψ ((Lock.frozen_isSyncOrbit_iff ψ).1 h)

end KAM.Provider.SpinOrbit
