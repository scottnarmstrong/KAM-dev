/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.HwRow

/-!
# Integer model rows, `z`-degree 1, part 0 (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- Integer model rows of `z`-degree 1, block 0. -/
def sjsuCD1B0 : List ((Mon × Mon) × ℤ) := [
  cRow 0 0 1 0 0 1 (-11368321108345095583844920000),
  cRow 0 0 1 0 1 0 1947944397102931194407162000,
  cRow 0 1 0 0 0 1 1947944397102931194407162000,
  cRow 0 1 0 0 1 0 (-90714211920509063258496700000),
  cRow 0 0 1 1 0 0 450159361783799456870431800,
  cRow 0 1 0 1 0 0 39030233055732293918017980000,
  cRow 1 0 0 0 0 1 450159361783799456870431800,
  cRow 1 0 0 0 1 0 39030233055732293918017980000,
  cRow 1 0 0 1 0 0 (-40845174259718687311369190000)]

end KAM.EffectiveStability.SJSU

end
