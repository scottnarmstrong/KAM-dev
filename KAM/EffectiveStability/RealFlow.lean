/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.RealFlow.Basic
public import KAM.EffectiveStability.RealFlow.Symplectic
public import KAM.EffectiveStability.RealFlow.Lie

/-!
# Real time-`t` maps of holomorphic real Hamiltonian flows (facade)

See `RealFlow/Basic.lean` (definitions, reality, smoothness, displacement),
`RealFlow/Symplectic.lean` (symplectic, inverse) and `RealFlow/Lie.lean` (observables, real
Lie–Taylor bound, smoke test).
-/
