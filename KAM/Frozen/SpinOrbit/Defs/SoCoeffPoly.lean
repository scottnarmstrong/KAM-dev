/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Algebra.Field.Basic

/-!
# Frozen definition `KAM.SpinOrbit.soCoeffPoly`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D46 and
D48). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

/-- The coefficient polynomials `A_m(e)` of the model (zero outside `1 ≤ m ≤ 7`);
`A_m = W(m/2, e)/2`
in Celletti's notation (eq. (7.55)). -/
def soCoeffPoly {R : Type*} [Field R] (e : R) : ℕ → R
  | 1 => -e / 4 + e ^ 3 / 32
  | 2 => 1 / 2 - 5 * e ^ 2 / 4 + 13 * e ^ 4 / 32
  | 3 => 7 * e / 4 - 123 * e ^ 3 / 32
  | 4 => 17 * e ^ 2 / 4 - 115 * e ^ 4 / 12
  | 5 => 845 * e ^ 3 / 96 - 32525 * e ^ 5 / 1536
  | 6 => 533 * e ^ 4 / 32
  | 7 => 228347 * e ^ 5 / 7680
  | _ => 0

end KAM.SpinOrbit

end
