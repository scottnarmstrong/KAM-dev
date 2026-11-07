/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Groups
public import Mathlib.Tactic.IntervalCases

/-!
# The `T_n` data checks, blocks 60–89 (T2-CONF, N5a-2)

Block `k` checks `tdatOk` on the groups `8k, …, 8k + 7` of `sjsuNs` (blocks of 8 keep each kernel
check near 1.7 GB).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsuTdat_block60 : ((sjsuNs.drop (8 * 60)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block61 : ((sjsuNs.drop (8 * 61)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block62 : ((sjsuNs.drop (8 * 62)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block63 : ((sjsuNs.drop (8 * 63)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block64 : ((sjsuNs.drop (8 * 64)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block65 : ((sjsuNs.drop (8 * 65)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block66 : ((sjsuNs.drop (8 * 66)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block67 : ((sjsuNs.drop (8 * 67)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block68 : ((sjsuNs.drop (8 * 68)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block69 : ((sjsuNs.drop (8 * 69)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block70 : ((sjsuNs.drop (8 * 70)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block71 : ((sjsuNs.drop (8 * 71)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block72 : ((sjsuNs.drop (8 * 72)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block73 : ((sjsuNs.drop (8 * 73)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block74 : ((sjsuNs.drop (8 * 74)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block75 : ((sjsuNs.drop (8 * 75)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block76 : ((sjsuNs.drop (8 * 76)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block77 : ((sjsuNs.drop (8 * 77)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block78 : ((sjsuNs.drop (8 * 78)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block79 : ((sjsuNs.drop (8 * 79)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block80 : ((sjsuNs.drop (8 * 80)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block81 : ((sjsuNs.drop (8 * 81)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block82 : ((sjsuNs.drop (8 * 82)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block83 : ((sjsuNs.drop (8 * 83)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block84 : ((sjsuNs.drop (8 * 84)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block85 : ((sjsuNs.drop (8 * 85)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block86 : ((sjsuNs.drop (8 * 86)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block87 : ((sjsuNs.drop (8 * 87)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block88 : ((sjsuNs.drop (8 * 88)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block89 : ((sjsuNs.drop (8 * 89)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_blocks2 :
    ∀ k, 60 ≤ k → k < 90 → ((sjsuNs.drop (8 * k)).take 8).all tdatOk = true := by
  intro k hk₀ hk₁
  interval_cases k
  · exact sjsuTdat_block60
  · exact sjsuTdat_block61
  · exact sjsuTdat_block62
  · exact sjsuTdat_block63
  · exact sjsuTdat_block64
  · exact sjsuTdat_block65
  · exact sjsuTdat_block66
  · exact sjsuTdat_block67
  · exact sjsuTdat_block68
  · exact sjsuTdat_block69
  · exact sjsuTdat_block70
  · exact sjsuTdat_block71
  · exact sjsuTdat_block72
  · exact sjsuTdat_block73
  · exact sjsuTdat_block74
  · exact sjsuTdat_block75
  · exact sjsuTdat_block76
  · exact sjsuTdat_block77
  · exact sjsuTdat_block78
  · exact sjsuTdat_block79
  · exact sjsuTdat_block80
  · exact sjsuTdat_block81
  · exact sjsuTdat_block82
  · exact sjsuTdat_block83
  · exact sjsuTdat_block84
  · exact sjsuTdat_block85
  · exact sjsuTdat_block86
  · exact sjsuTdat_block87
  · exact sjsuTdat_block88
  · exact sjsuTdat_block89

end KAM.EffectiveStability.SJSU

end
