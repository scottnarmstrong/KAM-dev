/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.SpinOrbit.Defs.SoField
public import KAM.Frozen.SpinOrbit.Defs.LunarPLo
public import KAM.Frozen.SpinOrbit.Defs.LunarPHi
import KAM.Provider.SpinOrbit.LunarSpinConfinement

/-!
# Frozen theorem `KAM.SpinOrbit.lunar_spin_confinement`

Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D47 and
D49). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor. Only the proof body between the markers may change, and only to
`by exact KAM.Provider.SpinOrbit.lunar_spin_confinement …` when the provider
`KAM.Provider.SpinOrbit.LunarSpinConfinement` is complete (sealing).
-/

@[expose] public section

namespace KAM.SpinOrbit

/-- **Theorem B.** In the seven-mode lunar spin–orbit model, every initial state `(q₀, p₀, φ₀)` with
`lunarPLo < p₀ < lunarPHi` (any angles) has a global solution, unique among global solutions, and
its
spin rate satisfies `|p(t) − 1| ≤ 2755/100000` (2.755 %) for all real `t`. -/
theorem lunar_spin_confinement (q₀ p₀ φ₀ : ℝ) (hp : (lunarPLo : ℝ) < p₀ ∧ p₀ < lunarPHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 2755 / 100000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.SpinOrbit.lunar_spin_confinement q₀ p₀ φ₀ hp
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.SpinOrbit

end
-- FROZEN_ANCHOR_SUFFIX_END
