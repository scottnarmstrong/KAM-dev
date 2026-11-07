/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.Br.Prm
public import KAM.EffectiveStability.Tube.Engine.BrChunk

/-!
# A chunk of a kept bracket coefficient (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem brp_2_3_3_0_0 : brCheckC (brD 2) 25 30 true (Ftab 2) brInH (3, 3, 0) 100 0 (brGc 2 (3, 3, 0)
  0) = true := by
  decide +kernel

end KAM.EffectiveStability.SJSU

end
