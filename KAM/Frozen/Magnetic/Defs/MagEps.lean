/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Frozen definition `KAM.Magnetic.magEps`

Owner-approved on 2026-11-01 (decision D68, docs/explorations/mag/FREEZE-PROPOSAL.md at
mag-pilot@a48eb432). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change
needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic

/-- The perturbation amplitude `ε = 3/2500` of the magnetic field-line model (owner-approved
fallback pilot value, D66; the plan's `3/1000` is not attempted). -/
def magEps : ℝ := 3 / 2500

end KAM.Magnetic

end
