/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.StrongAMD.Defs.ActionAxis

/-!
# Frozen definition `KAM.Planetary.StrongAMD.chamber`

Track LP, `LP:MAIN §1 (41–43)` (MAIN as amended by AMENDMENTS). Owner-approved on 2026-11-01
(decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings of D59). This
file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved
versioned successor.

Freeze role (D59, OD-11 (b)): a literal formula or predicate of the source, faithful on its whole
carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

/-- The action chamber `𝒬 = {I : I_i > 0, a_1 < ⋯ < a_n}` (`LP:MAIN` §1 (43)). -/
def chamber {n : ℕ} (ν : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {I | (∀ i, 0 < I i) ∧ ∀ i j, i < j → actionAxis ν I i < actionAxis ν I j}

end KAM.Planetary.StrongAMD

end
