/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.SpinOrbit.Defs.SoField
public import KAM.Frozen.SpinOrbit.Defs.LunarSyncOrbit
public import KAM.Frozen.SpinOrbit.Defs.LibAction
public import KAM.Frozen.SpinOrbit.Defs.LunarOmega
import KAM.Provider.SpinOrbit.LunarSyncLock

/-!
# Frozen theorem `KAM.SpinOrbit.lunar_sync_lock`

Owner-approved on 2026-10-31 (decision D48; docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md §1, with
the recommended answers of §2). This file is frozen: it is hashed in `manifest/frozen-anchors.json`;
any change needs an owner-approved versioned successor. Only the proof body between the markers may
change, and only to `by exact KAM.Provider.SpinOrbit.lunar_sync_lock q₀ p₀ φ₀ h₀` when the provider
`KAM.Provider.SpinOrbit.LunarSyncLock` is complete (sealing).
-/

@[expose] public section

namespace KAM.SpinOrbit

/-- The Moon stays locked in synchronous rotation forever. -/
theorem lunar_sync_lock (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 129 / 10000) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 21 / 100 ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 26 / 1000 ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.SpinOrbit

end
-- FROZEN_ANCHOR_SUFFIX_END
