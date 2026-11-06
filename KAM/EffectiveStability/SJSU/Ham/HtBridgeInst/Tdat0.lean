/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Groups
public import Mathlib.Tactic.IntervalCases

/-!
# The `T_n` data checks, blocks 0–29 (T2-CONF, N5a-2)

Block `k` checks `tdatOk` on the groups `8k, …, 8k + 7` of `sjsuNs` (blocks of 8 keep each kernel
check near 1.7 GB).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsuTdat_block0 : ((sjsuNs.drop (8 * 0)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block1 : ((sjsuNs.drop (8 * 1)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block2 : ((sjsuNs.drop (8 * 2)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block3 : ((sjsuNs.drop (8 * 3)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block4 : ((sjsuNs.drop (8 * 4)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block5 : ((sjsuNs.drop (8 * 5)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block6 : ((sjsuNs.drop (8 * 6)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block7 : ((sjsuNs.drop (8 * 7)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block8 : ((sjsuNs.drop (8 * 8)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block9 : ((sjsuNs.drop (8 * 9)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block10 : ((sjsuNs.drop (8 * 10)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block11 : ((sjsuNs.drop (8 * 11)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block12 : ((sjsuNs.drop (8 * 12)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block13 : ((sjsuNs.drop (8 * 13)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block14 : ((sjsuNs.drop (8 * 14)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block15 : ((sjsuNs.drop (8 * 15)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block16 : ((sjsuNs.drop (8 * 16)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block17 : ((sjsuNs.drop (8 * 17)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block18 : ((sjsuNs.drop (8 * 18)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block19 : ((sjsuNs.drop (8 * 19)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block20 : ((sjsuNs.drop (8 * 20)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block21 : ((sjsuNs.drop (8 * 21)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block22 : ((sjsuNs.drop (8 * 22)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block23 : ((sjsuNs.drop (8 * 23)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block24 : ((sjsuNs.drop (8 * 24)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block25 : ((sjsuNs.drop (8 * 25)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block26 : ((sjsuNs.drop (8 * 26)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block27 : ((sjsuNs.drop (8 * 27)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block28 : ((sjsuNs.drop (8 * 28)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_block29 : ((sjsuNs.drop (8 * 29)).take 8).all tdatOk = true := by
  decide +kernel

theorem sjsuTdat_blocks0 :
    ∀ k, 0 ≤ k → k < 30 → ((sjsuNs.drop (8 * k)).take 8).all tdatOk = true := by
  intro k hk₀ hk₁
  interval_cases k
  · exact sjsuTdat_block0
  · exact sjsuTdat_block1
  · exact sjsuTdat_block2
  · exact sjsuTdat_block3
  · exact sjsuTdat_block4
  · exact sjsuTdat_block5
  · exact sjsuTdat_block6
  · exact sjsuTdat_block7
  · exact sjsuTdat_block8
  · exact sjsuTdat_block9
  · exact sjsuTdat_block10
  · exact sjsuTdat_block11
  · exact sjsuTdat_block12
  · exact sjsuTdat_block13
  · exact sjsuTdat_block14
  · exact sjsuTdat_block15
  · exact sjsuTdat_block16
  · exact sjsuTdat_block17
  · exact sjsuTdat_block18
  · exact sjsuTdat_block19
  · exact sjsuTdat_block20
  · exact sjsuTdat_block21
  · exact sjsuTdat_block22
  · exact sjsuTdat_block23
  · exact sjsuTdat_block24
  · exact sjsuTdat_block25
  · exact sjsuTdat_block26
  · exact sjsuTdat_block27
  · exact sjsuTdat_block28
  · exact sjsuTdat_block29

end KAM.EffectiveStability.SJSU

end
