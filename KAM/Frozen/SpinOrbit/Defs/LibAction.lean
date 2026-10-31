/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Frozen definition `KAM.SpinOrbit.libAction`

Owner-approved on 2026-10-31 (decision D49, route D45; docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md
§1, with the recommended answers of §2). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

open Real

namespace KAM.SpinOrbit

/-- The elliptic libration action around a curve `ψ`. -/
def libAction (Ω : ℝ) (ψ : ℝ → ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  π * (Ω * (x.1 - x.2.2 - ψ x.2.2) ^ 2 + (x.2.1 - 1 - deriv ψ x.2.2) ^ 2 / Ω)

end KAM.SpinOrbit

end
