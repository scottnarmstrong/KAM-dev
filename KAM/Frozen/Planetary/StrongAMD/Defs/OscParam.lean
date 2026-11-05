/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Frozen definition `KAM.Planetary.StrongAMD.oscParam`

Track LP, `LP:MAIN L16 (508–525)` (MAIN as amended by AMENDMENTS). Owner-approved on 2026-11-01
(decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This
file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved
versioned successor.

Freeze role (D59, OD-11 (b)): an internal total helper in the definition closure. It is certified as
the source object only on its carrier, through the source-facing definitions and predicates that use
it; its values off that carrier carry no source meaning.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

/-- The gravitational parameter `k_i = 1 + μ ν_i`. -/
def oscParam {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (i : Fin n) : ℝ := 1 + μ * ν i

end KAM.Planetary.StrongAMD

end
