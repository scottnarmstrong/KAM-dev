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

theorem brdropc_1_7 : dropCheckC brPb sjsuHD.H brNH (2 / 1000000) 8 (Ftab 1) sjsuMons 4 7 (brDc 1 7)
  = true := by
  decide +kernel

end KAM.EffectiveStability.SJSU

end
