/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.SpinOrbit.Defs.SoField
public import KAM.Frozen.SpinOrbit.Defs.LunarPLo
public import KAM.Frozen.SpinOrbit.Defs.LunarPHi
import KAM.SpinOrbit.LunarFinalR2V2

/-!
# Provider for the frozen theorem `KAM.SpinOrbit.lunar_spin_confinement`

The proof of `KAM.SpinOrbit.lunar_spin_confinement` is assembled here as
`KAM.Provider.SpinOrbit.lunar_spin_confinement`, from landed results only. While the frozen anchor
is `DRAFT_SORRY`, this module is quarantined: no module other than the anchor may import it.

* `KAM.Provider.SpinOrbit.lunar_spin_confinement` has exactly the type of the frozen theorem. It is
  the landed `KAM.SpinOrbit.lunar_spin_confinement_65_v2` (`KAM/SpinOrbit/LunarFinalR2V2.lean`,
  SO-DATA3): its window ends `lunarR2PLo`, `lunarR2PHi` equal `lunarPLo`, `lunarPHi` by `rfl`, and
  its bound `((lunarR2Delta : ℚ) : ℝ)` is rewritten to `2755 / 100000` by a `norm_num` equality.
  Since Q11 of FREEZE-PROPOSAL-2 the landed `soField` is the frozen one. This module does not import
  the frozen theorem.
-/

public section

namespace KAM.Provider.SpinOrbit

open KAM.SpinOrbit

/-- **Theorem B**: the provider of the frozen `KAM.SpinOrbit.lunar_spin_confinement`, with exactly
its type. -/
theorem lunar_spin_confinement (q₀ p₀ φ₀ : ℝ) (hp : (lunarPLo : ℝ) < p₀ ∧ p₀ < lunarPHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 2755 / 100000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := by
  have hpl : lunarR2PLo = lunarPLo := rfl
  have hph : lunarR2PHi = lunarPHi := rfl
  have hδ : ((lunarR2Delta : ℚ) : ℝ) = 2755 / 100000 := by norm_num [lunarR2Delta]
  have h := lunar_spin_confinement_65_v2 q₀ p₀ φ₀ (by rw [hpl, hph]; exact hp)
  rw [hδ] at h
  exact h

end KAM.Provider.SpinOrbit

end
