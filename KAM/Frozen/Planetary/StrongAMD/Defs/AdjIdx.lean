/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Fin.Basic

/-!
# Frozen definition `KAM.Planetary.StrongAMD.AdjIdx`

Track LP, `LP:MAIN §1 (3) (52)` (MAIN as amended by AMENDMENTS). Owner-approved on 2026-11-01
(decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This
file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved
versioned successor.

Freeze role (D59, OD-11 (b)): a literal formula or predicate of the source, faithful on its whole
carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

/-- The index type of adjacent pairs `(i, i+1)` with `i + 1 < n`. -/
abbrev AdjIdx (n : ℕ) : Type := {i : Fin n // i.val + 1 < n}

end KAM.Planetary.StrongAMD

end
