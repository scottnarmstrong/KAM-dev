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

theorem brc_df_0_4 : ((((Ftab 0).drop (8 * 4)).take 8).all fun i => ([0, 1] : List (Fin 2)).all fun
  a => ((brD 0).dFL i a).ok brPd && dCheck brPc brPcd ((brD 0).FL i) ((brD 0).dFL i a) a) = true :=
  by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
