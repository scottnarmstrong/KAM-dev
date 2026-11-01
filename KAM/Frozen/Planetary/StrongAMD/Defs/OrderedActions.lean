/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.StrongAMD.Defs.Chamber

/-!
# Frozen definition `KAM.Planetary.StrongAMD.OrderedActions`

Track LP, `LP:MAIN §1 (41–55)` (MAIN as amended by AMENDMENTS). Owner-approved on 2026-11-01
(decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This
file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved
versioned successor.

Freeze role (D59, OD-11 (b)): a source carrier (subtype or carrier predicate).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

/-- The source carrier: action vectors in the chamber `𝒬`. -/
abbrev OrderedActions {n : ℕ} (ν : Fin n → ℝ) : Type := {I : Fin n → ℝ // I ∈ chamber ν}

end KAM.Planetary.StrongAMD

end
