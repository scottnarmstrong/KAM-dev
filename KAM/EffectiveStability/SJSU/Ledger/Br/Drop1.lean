/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_0
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_1
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_2
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_3
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_4
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_5
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_6
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_7
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_8
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_9
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_10
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_11
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_12
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_13
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_14
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_15
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_16
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_17
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_18
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_19
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_20
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_21
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_22
public import KAM.EffectiveStability.SJSU.Ledger.Br.DropC1_23

/-!
# The dropped bracket terms (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem brdrop_1 : dropCheck brPb sjsuHD.H brNH (2 / 1000000) 8 (Ftab 1) sjsuMons
    (sjsuDrop 1) = true := by
  refine dropCheck_of_chunks (m := 4) (n := 24) (Dc := brDc 1) (by norm_num)
    (by decide +kernel) (fun k hk => ?_) (by decide +kernel)
  interval_cases k
  exacts [brdropc_1_0, brdropc_1_1, brdropc_1_2, brdropc_1_3, brdropc_1_4, brdropc_1_5, brdropc_1_6,
    brdropc_1_7, brdropc_1_8, brdropc_1_9, brdropc_1_10, brdropc_1_11, brdropc_1_12, brdropc_1_13,
    brdropc_1_14, brdropc_1_15, brdropc_1_16, brdropc_1_17, brdropc_1_18, brdropc_1_19, brdropc_1_20
    , brdropc_1_21, brdropc_1_22, brdropc_1_23]

end KAM.EffectiveStability.SJSU

end
