/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.EffectiveStability.SJSU.SJSU18O2Terms
public import Mathlib.Analysis.Complex.Basic

/-!
# Frozen definition `KAM.EffectiveStability.sjsu18O2`

Owner-approved on 2026-11-06 (decision D76; exact text: draft v2 of
`docs/explorations/sjsu-g2-t2conf-proposal.md`, program T2-CONF). Part of the opt-in application
library `KAMSJSU` (D51). This file is frozen: it is hashed in `manifest/frozen-anchors.json`;
any change needs an owner-approved versioned successor.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- **`SJSU18-O2`** (D75): the planar secular Sun–Jupiter–Saturn–Uranus Hamiltonian of degree 18,
`H = Re Σ c zᵃ z̄ᵇ` over `sjsu18O2Terms`, with `z_j = (ξ_j - i η_j)/√2`, `η = x.1` (coordinates) and
`ξ = x.2` (momenta); units AU, year, `G = 1`. The sum is real; `Re` only fixes the type. -/
noncomputable def sjsu18O2 (x : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : ℝ :=
  let z : Fin 3 → ℂ := fun j => ((x.2 j : ℂ) - Complex.I * (x.1 j : ℂ)) / (Real.sqrt 2 : ℂ)
  ((sjsu18O2Terms.map fun t =>
      ((t.2.2.2.2.2.2 : ℚ) : ℂ) * z 0 ^ t.1 * star (z 0) ^ t.2.1 * z 1 ^ t.2.2.1 *
        star (z 1) ^ t.2.2.2.1 * z 2 ^ t.2.2.2.2.1 * star (z 2) ^ t.2.2.2.2.2.1).sum).re

end KAM.EffectiveStability

end
