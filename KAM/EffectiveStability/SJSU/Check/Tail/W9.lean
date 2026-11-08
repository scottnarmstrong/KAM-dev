/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.Tail.Rows

/-!
# Kernel checks of the integer row weights of `H_w`, degrees 9–9 (T2-CONF, N9 (C))

`treeSumQ 64 (rows of degree d ↦ sjsuRowWZ) ≤ sjsuW d · sjsuDen d` and the same for `sjsuRowWpZ`.
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsu_WZ_ok9 : treeSumQ 64 ((sjsuHw 9).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)) ≤
    sjsuW 9 * sjsuDen 9 := by
  decide +kernel
theorem sjsu_WpZ_ok9 : treeSumQ 64 ((sjsuHw 9).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)) ≤
    sjsuWp 9 * sjsuDen 9 := by
  decide +kernel

end KAM.EffectiveStability.SJSU

end
