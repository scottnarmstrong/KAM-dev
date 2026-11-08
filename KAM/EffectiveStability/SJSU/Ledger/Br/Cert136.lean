/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.Br.Prm
public import KAM.EffectiveStability.SJSU.Ledger.H.Main

/-!
# Bracket certificates (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem brc_n_10 : (((sjsuMons.drop (8 * 10)).take 8).all fun t => (sjsuHD.H t).ok brPb && (sjsuHD.H
  t).l1Check brPb (brNH t)) = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
