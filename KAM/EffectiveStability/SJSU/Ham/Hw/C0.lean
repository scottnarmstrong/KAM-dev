/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.HwRow

/-!
# The model has no rows of `z`-degree 0 (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsuC0_check : (sjsuIntChunks 0).flatten = [] := by
  apply eq_of_listBEq
  decide +kernel

end KAM.EffectiveStability.SJSU

end
