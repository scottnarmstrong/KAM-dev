/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Groups
public import Mathlib.Tactic.IntervalCases

/-!
# The `T_n` data checks, blocks 30–59 (T2-CONF, N5a-2)

Block `k` checks `tdatOk` on the groups `8k, …, 8k + 7` of `sjsuNs` (blocks of 8 keep each kernel
check near 1.7 GB).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsuTdat_block30 : ((sjsuNs.drop (8 * 30)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block31 : ((sjsuNs.drop (8 * 31)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block32 : ((sjsuNs.drop (8 * 32)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block33 : ((sjsuNs.drop (8 * 33)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block34 : ((sjsuNs.drop (8 * 34)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block35 : ((sjsuNs.drop (8 * 35)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block36 : ((sjsuNs.drop (8 * 36)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block37 : ((sjsuNs.drop (8 * 37)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block38 : ((sjsuNs.drop (8 * 38)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block39 : ((sjsuNs.drop (8 * 39)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block40 : ((sjsuNs.drop (8 * 40)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block41 : ((sjsuNs.drop (8 * 41)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block42 : ((sjsuNs.drop (8 * 42)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block43 : ((sjsuNs.drop (8 * 43)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block44 : ((sjsuNs.drop (8 * 44)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block45 : ((sjsuNs.drop (8 * 45)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block46 : ((sjsuNs.drop (8 * 46)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block47 : ((sjsuNs.drop (8 * 47)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block48 : ((sjsuNs.drop (8 * 48)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block49 : ((sjsuNs.drop (8 * 49)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block50 : ((sjsuNs.drop (8 * 50)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block51 : ((sjsuNs.drop (8 * 51)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block52 : ((sjsuNs.drop (8 * 52)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block53 : ((sjsuNs.drop (8 * 53)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block54 : ((sjsuNs.drop (8 * 54)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block55 : ((sjsuNs.drop (8 * 55)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block56 : ((sjsuNs.drop (8 * 56)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block57 : ((sjsuNs.drop (8 * 57)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block58 : ((sjsuNs.drop (8 * 58)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block59 : ((sjsuNs.drop (8 * 59)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_blocks1 :
    ∀ k, 30 ≤ k → k < 60 → ((sjsuNs.drop (8 * k)).take 8).all tdatOk = true := by
  intro k hk₀ hk₁
  interval_cases k
  · exact sjsuTdat_block30
  · exact sjsuTdat_block31
  · exact sjsuTdat_block32
  · exact sjsuTdat_block33
  · exact sjsuTdat_block34
  · exact sjsuTdat_block35
  · exact sjsuTdat_block36
  · exact sjsuTdat_block37
  · exact sjsuTdat_block38
  · exact sjsuTdat_block39
  · exact sjsuTdat_block40
  · exact sjsuTdat_block41
  · exact sjsuTdat_block42
  · exact sjsuTdat_block43
  · exact sjsuTdat_block44
  · exact sjsuTdat_block45
  · exact sjsuTdat_block46
  · exact sjsuTdat_block47
  · exact sjsuTdat_block48
  · exact sjsuTdat_block49
  · exact sjsuTdat_block50
  · exact sjsuTdat_block51
  · exact sjsuTdat_block52
  · exact sjsuTdat_block53
  · exact sjsuTdat_block54
  · exact sjsuTdat_block55
  · exact sjsuTdat_block56
  · exact sjsuTdat_block57
  · exact sjsuTdat_block58
  · exact sjsuTdat_block59

end KAM.EffectiveStability.SJSU

end
