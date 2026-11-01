/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Frozen definition `KAM.Magnetic.magH0`

Owner-approved on 2026-11-01 (decision D68, docs/explorations/mag/FREEZE-PROPOSAL.md at
mag-pilot@a48eb432). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change
needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic

/-- The integrable part `h(p) = p - (3/4) p² + (1/3) p³ - (1/16) p⁴` (safety-factor profile of
Chandre et al. and Valvo–Locatelli; `p` is the flux variable, defined on all of `ℝ` as a
polynomial). -/
def magH0 (p : ℝ) : ℝ :=
  p - 3 / 4 * p ^ 2 + 1 / 3 * p ^ 3 - 1 / 16 * p ^ 4

end KAM.Magnetic

end
