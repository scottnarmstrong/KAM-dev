/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.Tail.Rows

/-!
# Kernel checks of the integer row weights of `H_w`, degrees 1–6 (T2-CONF, N9 (C))

`treeSumQ 64 (rows of degree d ↦ sjsuRowWZ) ≤ sjsuW d · sjsuDen d` and the same for `sjsuRowWpZ`.
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsu_WZ_ok1 : treeSumQ 64 ((sjsuHw 1).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)) ≤
    sjsuW 1 * sjsuDen 1 := by
  decide +kernel
theorem sjsu_WpZ_ok1 : treeSumQ 64 ((sjsuHw 1).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)) ≤
    sjsuWp 1 * sjsuDen 1 := by
  decide +kernel

theorem sjsu_WZ_ok2 : treeSumQ 64 ((sjsuHw 2).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)) ≤
    sjsuW 2 * sjsuDen 2 := by
  decide +kernel
theorem sjsu_WpZ_ok2 : treeSumQ 64 ((sjsuHw 2).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)) ≤
    sjsuWp 2 * sjsuDen 2 := by
  decide +kernel

theorem sjsu_WZ_ok3 : treeSumQ 64 ((sjsuHw 3).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)) ≤
    sjsuW 3 * sjsuDen 3 := by
  decide +kernel
theorem sjsu_WpZ_ok3 : treeSumQ 64 ((sjsuHw 3).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)) ≤
    sjsuWp 3 * sjsuDen 3 := by
  decide +kernel

theorem sjsu_WZ_ok4 : treeSumQ 64 ((sjsuHw 4).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)) ≤
    sjsuW 4 * sjsuDen 4 := by
  decide +kernel
theorem sjsu_WpZ_ok4 : treeSumQ 64 ((sjsuHw 4).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)) ≤
    sjsuWp 4 * sjsuDen 4 := by
  decide +kernel

theorem sjsu_WZ_ok5 : treeSumQ 64 ((sjsuHw 5).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)) ≤
    sjsuW 5 * sjsuDen 5 := by
  decide +kernel
theorem sjsu_WpZ_ok5 : treeSumQ 64 ((sjsuHw 5).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)) ≤
    sjsuWp 5 * sjsuDen 5 := by
  decide +kernel

theorem sjsu_WZ_ok6 : treeSumQ 64 ((sjsuHw 6).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)) ≤
    sjsuW 6 * sjsuDen 6 := by
  decide +kernel
theorem sjsu_WpZ_ok6 : treeSumQ 64 ((sjsuHw 6).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)) ≤
    sjsuWp 6 * sjsuDen 6 := by
  decide +kernel

end KAM.EffectiveStability.SJSU

end
