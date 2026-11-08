/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.AssemblyN65
public import KAM.SpinOrbit.Lock.FrozenBridge
public import KAM.Frozen.SpinOrbit.Defs.LunarOmega

/-!
# Provider for the frozen theorem `KAM.SpinOrbit.lunar_sync_lock`

The proof of `KAM.SpinOrbit.lunar_sync_lock` is assembled here as
`KAM.Provider.SpinOrbit.lunar_sync_lock`, from the landed N = 65 certificate theorem
`KAM.SpinOrbit.Data.LockN65.lunar_sync_lock_N65` through the bridges of
`KAM.SpinOrbit.Lock.FrozenBridge` (the two `lunarOmega` literals agree definitionally). Application
module of `KAMLunarLock` (D51).
-/

@[expose] public section

namespace KAM.Provider.SpinOrbit
open KAM.SpinOrbit

/-- Quarantined provider signature; exact frozen telescope. -/
theorem lunar_sync_lock (q₀ p₀ φ₀ : ℝ)
    (h₀ : libAction lunarOmega lunarSyncOrbit (q₀, p₀, φ₀) < 129 / 10000) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).1 - (z t).2.2 - lunarSyncOrbit (z t).2.2| ≤ 21 / 100 ∧
        |(z t).2.1 - 1 - deriv lunarSyncOrbit (z t).2.2| ≤ 26 / 1000 ∧
        |(z t).1 - (z t).2.2| < 1 / 4) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := by
  rw [Lock.frozen_libAction_eq, Lock.frozen_lunarSyncOrbit_eq] at h₀
  rw [Lock.frozen_lunarSyncOrbit_eq]
  exact KAM.SpinOrbit.Data.LockN65.lunar_sync_lock_N65 q₀ p₀ φ₀ h₀

end KAM.Provider.SpinOrbit
