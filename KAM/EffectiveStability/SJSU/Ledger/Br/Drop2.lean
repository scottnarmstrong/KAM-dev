/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_0
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_1
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_2
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_3
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_4
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_5
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_6
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_7
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_8
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_9
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_10
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_11
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_12
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_13
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_14
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_15
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_16
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_17
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_18
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_19
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_20
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_21
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_22
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC2_23

/-!
# The dropped bracket terms (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem brdrop_2 : dropCheck brPb sjsuHD.H brNH (2 / 1000000) 8 (Ftab 2) sjsuMons
    (sjsuDrop 2) = true := by
  refine dropCheck_of_chunks (m := 4) (n := 24) (Dc := brDc 2) (by norm_num)
    (by decide +kernel) (fun k hk => ?_) (by decide +kernel)
  interval_cases k
  exacts [brdropc_2_0, brdropc_2_1, brdropc_2_2, brdropc_2_3, brdropc_2_4, brdropc_2_5, brdropc_2_6,
    brdropc_2_7, brdropc_2_8, brdropc_2_9, brdropc_2_10, brdropc_2_11, brdropc_2_12, brdropc_2_13,
    brdropc_2_14, brdropc_2_15, brdropc_2_16, brdropc_2_17, brdropc_2_18, brdropc_2_19, brdropc_2_20
    , brdropc_2_21, brdropc_2_22, brdropc_2_23]

end KAM.EffectiveStability.SJSU

end
