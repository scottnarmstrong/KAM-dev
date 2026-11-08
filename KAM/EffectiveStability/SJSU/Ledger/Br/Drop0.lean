/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_0
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_1
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_2
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_3
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_4
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_5
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_6
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_7
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_8
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_9
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_10
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_11
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_12
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_13
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_14
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_15
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_16
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_17
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_18
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_19
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_20
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC0_21

/-!
# The dropped bracket terms (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem brdrop_0 : dropCheck brPb sjsuHD.H brNH (2 / 1000000) 8 (Ftab 0) sjsuMons
    (sjsuDrop 0) = true := by
  refine dropCheck_of_chunks (m := 4) (n := 22) (Dc := brDc 0) (by norm_num)
    (by decide +kernel) (fun k hk => ?_) (by decide +kernel)
  interval_cases k
  exacts [brdropc_0_0, brdropc_0_1, brdropc_0_2, brdropc_0_3, brdropc_0_4, brdropc_0_5, brdropc_0_6,
    brdropc_0_7, brdropc_0_8, brdropc_0_9, brdropc_0_10, brdropc_0_11, brdropc_0_12, brdropc_0_13,
    brdropc_0_14, brdropc_0_15, brdropc_0_16, brdropc_0_17, brdropc_0_18, brdropc_0_19, brdropc_0_20
    , brdropc_0_21]

end KAM.EffectiveStability.SJSU

end
