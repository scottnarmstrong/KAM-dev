/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.Tail.Tab
public import KAM.EffectiveStability.SJSU.Check.Tail.Tails
public import KAM.EffectiveStability.SJSU.Check.Tail.W1to6
public import KAM.EffectiveStability.SJSU.Check.Tail.W7
public import KAM.EffectiveStability.SJSU.Check.Tail.W8
public import KAM.EffectiveStability.SJSU.Check.Tail.W9

/-!
# Kernel checks of the remainder data (T2-CONF, N9 (C)): facade

The checks are split into modules (one process each) to keep every kernel run within the memory
cap: `Tail/Tab` (slot tables), `Tail/Tails` (tail sums), `Tail/Rows` (row weights over common
denominators) and `Tail/W1to6`, `W7`, `W8`, `W9` (integer row sums per degree).
-/
