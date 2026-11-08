/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Groups
public import Mathlib.Tactic.FinCases

/-!
# The `B_j` data checks (T2-CONF, N5a-2)

`sjsuBdat j = scatter 61² 0 (bPairs 30 sjsuEccModes sjsuEccIbar j)`: N7's dense `B_j` lists are the
index-sorted pairs of N6's tube centre. One declaration per component (about 1.7 GB each).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsuBdat_check0 :
    listBEq (sjsuBdat (0 : Fin 3))
      (scatter ((2 * 30 + 1) * (2 * 30 + 1)) 0 (bPairs 30 sjsuEccModes sjsuEccIbar 0)) = true := by
  decide +kernel

theorem sjsuBdat_check1 :
    listBEq (sjsuBdat (1 : Fin 3))
      (scatter ((2 * 30 + 1) * (2 * 30 + 1)) 0 (bPairs 30 sjsuEccModes sjsuEccIbar 1)) = true := by
  decide +kernel

theorem sjsuBdat_check2 :
    listBEq (sjsuBdat (2 : Fin 3))
      (scatter ((2 * 30 + 1) * (2 * 30 + 1)) 0 (bPairs 30 sjsuEccModes sjsuEccIbar 2)) = true := by
  decide +kernel

theorem sjsuBdat_check : ∀ j : Fin 3,
    listBEq (sjsuBdat j)
      (scatter ((2 * 30 + 1) * (2 * 30 + 1)) 0 (bPairs 30 sjsuEccModes sjsuEccIbar j)) = true := by
  intro j
  fin_cases j
  · exact sjsuBdat_check0
  · exact sjsuBdat_check1
  · exact sjsuBdat_check2

end KAM.EffectiveStability.SJSU

end
