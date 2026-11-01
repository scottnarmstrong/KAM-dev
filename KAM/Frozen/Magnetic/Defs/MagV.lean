/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import KAM.Frozen.Magnetic.Defs.MagEps

/-!
# Frozen definition `KAM.Magnetic.magV`

Owner-approved on 2026-11-01 (decision D68, docs/explorations/mag/FREEZE-PROPOSAL.md at
mag-pilot@a48eb432). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change
needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.Magnetic

open Real

/-- The controlled perturbation (angles in turns, `a = 2π(2q - φ)`, `b = 2π(3q - 2φ)`):
`V(q, φ) = ε (cos a + cos b) + (1427/3200) ε² A²`, `A = (32000/2777) cos a - (96000/7669) cos b`.
The factor `1427/3200` is `-h''(7/20)/2` and `32000/2777`, `96000/7669` are the general-(8)
quadratic control coefficients of Chandre–Vittot–Ciraolo–Ghendrih–Lima (v2) at `p_c = 7/20`,
`ω_c = h'(7/20) = 18777/32000` (plan-magnetic-barrier §1.1). -/
def magV (q φ : ℝ) : ℝ :=
  magEps * (cos (2 * π * (2 * q - φ)) + cos (2 * π * (3 * q - 2 * φ))) +
    1427 / 3200 * magEps ^ 2 *
      (32000 / 2777 * cos (2 * π * (2 * q - φ)) - 96000 / 7669 * cos (2 * π * (3 * q - 2 * φ))) ^ 2

end KAM.Magnetic

end
