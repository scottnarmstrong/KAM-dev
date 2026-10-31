/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import KAM.Frozen.SpinOrbit.Defs.SoEps
public import KAM.Frozen.SpinOrbit.Defs.SoA
public import KAM.Frozen.SpinOrbit.Defs.SoModes

/-!
# Frozen definition `KAM.SpinOrbit.soV`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D47 and
D49). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit

/-- The period-one potential `V(q, φ) = -ε_* Σ_{m=1}^7 A_m(e_*) cos (2π (2q - mφ))`
(`q` spin angle, `φ` orbital phase, both in turns). -/
def soV (q φ : ℝ) : ℝ :=
  -soEps * ∑ m ∈ soModes, soA m * Real.cos (2 * π * (2 * q - m * φ))

end KAM.SpinOrbit

end
