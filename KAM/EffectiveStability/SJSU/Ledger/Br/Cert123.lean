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

theorem brc_dh_26 : (((sjsuMons.drop (8 * 26)).take 8).all fun t => ([0, 1] : List (Fin 2)).all fun
  a => ((brD 0).dHL t a).ok brPd && dCheck brPc brPcd (sjsuHD.H t) ((brD 0).dHL t a) a) = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
