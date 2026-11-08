/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.PO.Orbit
public import KAM.SpinOrbit.Lock.Confine
public import KAM.Frozen.SpinOrbit.Defs.LunarSyncOrbit
public import KAM.Frozen.SpinOrbit.Defs.LibAction

/-!
# Bridges from the frozen lock definitions to the landed ones (LOCK-FREEZE Phase B)

The frozen `KAM.SpinOrbit.IsSyncOrbit` writes the orbit equation through `soField`, the landed
`KAM.SpinOrbit.Lock.IsSyncOrbit` through `soVq`; they agree by `soField_eq`. Hence the two chosen
orbits `lunarSyncOrbit` coincide. `libAction` agrees by `rfl` (`lunarOmega`, landed in
`Lock.Assembly`, is bridged in the `lunar_sync_lock` provider).
-/

@[expose] public section

namespace KAM.SpinOrbit.Lock

theorem frozen_isSyncOrbit_iff (ψ : ℝ → ℝ) :
    KAM.SpinOrbit.IsSyncOrbit ψ ↔ KAM.SpinOrbit.Lock.IsSyncOrbit ψ := by
  simp only [KAM.SpinOrbit.IsSyncOrbit, KAM.SpinOrbit.Lock.IsSyncOrbit, soField_eq]

theorem frozen_isSyncOrbit_eq :
    KAM.SpinOrbit.IsSyncOrbit = KAM.SpinOrbit.Lock.IsSyncOrbit :=
  funext fun ψ => propext (frozen_isSyncOrbit_iff ψ)

theorem frozen_lunarSyncOrbit_eq :
    KAM.SpinOrbit.lunarSyncOrbit = KAM.SpinOrbit.Lock.lunarSyncOrbit := by
  unfold KAM.SpinOrbit.lunarSyncOrbit KAM.SpinOrbit.Lock.lunarSyncOrbit
  rw [frozen_isSyncOrbit_eq]

theorem frozen_libAction_eq : KAM.SpinOrbit.libAction = KAM.SpinOrbit.Lock.libAction := rfl

end KAM.SpinOrbit.Lock
