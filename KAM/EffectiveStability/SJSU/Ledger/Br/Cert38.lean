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

theorem brc_f_1_8 : ((((Ftab 1).drop (8 * 8)).take 8).all fun i => ((brD 1).FL i).ok brPb && fCheck
  brPc ((brD 1).FL i) i.2) = true := by
  decide +kernel


end KAM.EffectiveStability.SJSU

end
