/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Frozen definition `KAM.Magnetic.magAlpha`

Owner-approved on 2026-11-01 (decision D68, docs/explorations/mag/FREEZE-PROPOSAL.md at
mag-pilot@a48eb432). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change
needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic

/-- The rotation number `α = (43 + 18φ_g)/(74 + 31φ_g) = (7913 - √5)/13618`, `φ_g = (1 + √5)/2`
(continued fraction `[0; 1, 1, 2, 1, 1, 2, 3, 1̄]`, Valvo–Locatelli (12)); the barrier carries the
frequency `(α, 1)`. -/
def magAlpha : ℝ := (7913 - Real.sqrt 5) / 13618

end KAM.Magnetic

end
