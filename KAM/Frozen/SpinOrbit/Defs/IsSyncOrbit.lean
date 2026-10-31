/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import KAM.Frozen.SpinOrbit.Defs.SoField

/-!
# Frozen definition `KAM.SpinOrbit.IsSyncOrbit`

Owner-approved on 2026-10-31 (decision D49, route D45; docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md
§1, with the recommended answers of §2). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- `ψ` is a synchronous periodic orbit: `q = φ + ψ(φ)`, `p = 1 + ψ'(φ)` solves `soField`;
`ψ` is `C²`, one-periodic and odd. -/
def IsSyncOrbit (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ψ ∧ Function.Periodic ψ 1 ∧ (∀ φ, ψ (-φ) = -ψ φ) ∧
    ∀ φ, deriv (deriv ψ) φ = (soField (φ + ψ φ, 1 + deriv ψ φ, φ)).2.1

end KAM.SpinOrbit

end
