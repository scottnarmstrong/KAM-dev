/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Rat.Defs

/-!
# Frozen definition `KAM.EffectiveStability.sjsuTerm`

Owner-approved on 2026-11-06 (decision D76; exact text: draft v2 of
`docs/explorations/sjsu-g2-t2conf-proposal.md`, program T2-CONF). Part of the opt-in application
library `KAMSJSU` (D51). This file is frozen: it is hashed in `manifest/frozen-anchors.json`;
any change needs an owner-approved versioned successor.
-/

@[expose] public section

namespace KAM.EffectiveStability

/-- A row of `SJSU18-O2` (complex form, D75): the exponents of
`z_J, conj z_J, z_S, conj z_S, z_U, conj z_U` and the coefficient, in the dataset's column order. -/
def sjsuTerm (aJ bJ aS bS aU bU : ℕ) (c : ℚ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ :=
  (aJ, bJ, aS, bS, aU, bU, c)

end KAM.EffectiveStability

end
