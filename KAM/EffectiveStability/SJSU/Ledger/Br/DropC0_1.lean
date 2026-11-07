/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.Br.DropD

/-!
# A chunk of the dropped bracket terms (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem brdropc_0_1 : dropCheckC brPb sjsuHD.H brNH (2 / 1000000) 8 (Ftab 0) sjsuMons 4 1 (brDc 0 1)
  = true := by
  decide +kernel

end KAM.EffectiveStability.SJSU

end
