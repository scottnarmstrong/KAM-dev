/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.TailAcc
public import KAM.EffectiveStability.SJSU.Initial.Data
public import Mathlib.Tactic.IntervalCases

/-!
# The tail sums of the slot tables (T2-CONF, N9 (C))

At `K = 2d` (`d = 1, …, 9`, one kernel check per degree), the tail sums of the tables are below
`TT`, `TU`, `TP`.
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsu_tail_ok1 : tailQ (sjsuGT 2) 9 ≤ sjsuTT 2 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 2) i (sjsuGTD 2 i)) 9 ≤ sjsuTU 2 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 2) i (sjsuGTP 2 i)) 9 ≤ sjsuTP 2 := by
  decide +kernel

theorem sjsu_tail_ok2 : tailQ (sjsuGT 4) 9 ≤ sjsuTT 4 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 4) i (sjsuGTD 4 i)) 9 ≤ sjsuTU 4 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 4) i (sjsuGTP 4 i)) 9 ≤ sjsuTP 4 := by
  decide +kernel

theorem sjsu_tail_ok3 : tailQ (sjsuGT 6) 9 ≤ sjsuTT 6 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 6) i (sjsuGTD 6 i)) 9 ≤ sjsuTU 6 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 6) i (sjsuGTP 6 i)) 9 ≤ sjsuTP 6 := by
  decide +kernel

theorem sjsu_tail_ok4 : tailQ (sjsuGT 8) 9 ≤ sjsuTT 8 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 8) i (sjsuGTD 8 i)) 9 ≤ sjsuTU 8 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 8) i (sjsuGTP 8 i)) 9 ≤ sjsuTP 8 := by
  decide +kernel

theorem sjsu_tail_ok5 : tailQ (sjsuGT 10) 9 ≤ sjsuTT 10 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 10) i (sjsuGTD 10 i)) 9 ≤ sjsuTU 10 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 10) i (sjsuGTP 10 i)) 9 ≤ sjsuTP 10 := by
  decide +kernel

theorem sjsu_tail_ok6 : tailQ (sjsuGT 12) 9 ≤ sjsuTT 12 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 12) i (sjsuGTD 12 i)) 9 ≤ sjsuTU 12 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 12) i (sjsuGTP 12 i)) 9 ≤ sjsuTP 12 := by
  decide +kernel

theorem sjsu_tail_ok7 : tailQ (sjsuGT 14) 9 ≤ sjsuTT 14 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 14) i (sjsuGTD 14 i)) 9 ≤ sjsuTU 14 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 14) i (sjsuGTP 14 i)) 9 ≤ sjsuTP 14 := by
  decide +kernel

theorem sjsu_tail_ok8 : tailQ (sjsuGT 16) 9 ≤ sjsuTT 16 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 16) i (sjsuGTD 16 i)) 9 ≤ sjsuTU 16 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 16) i (sjsuGTP 16 i)) 9 ≤ sjsuTP 16 := by
  decide +kernel

theorem sjsu_tail_ok9 : tailQ (sjsuGT 18) 9 ≤ sjsuTT 18 ∧
    (∀ i : Fin 3, tailQ (updQ (sjsuGT 18) i (sjsuGTD 18 i)) 9 ≤ sjsuTU 18 i) ∧
    ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT 18) i (sjsuGTP 18 i)) 9 ≤ sjsuTP 18 := by
  decide +kernel

theorem sjsu_tail_ok : ∀ d < 10, 1 ≤ d →
    tailQ (sjsuGT (2 * d)) 9 ≤ sjsuTT (2 * d) ∧
      (∀ i : Fin 3, tailQ (updQ (sjsuGT (2 * d)) i (sjsuGTD (2 * d) i)) 9 ≤ sjsuTU (2 * d) i) ∧
      ∑ i : Fin 3, sjsuBeta i * tailQ (updQ (sjsuGT (2 * d)) i (sjsuGTP (2 * d) i)) 9 ≤
        sjsuTP (2 * d) := by
  intro d h10 h1
  interval_cases d
  · exact sjsu_tail_ok1
  · exact sjsu_tail_ok2
  · exact sjsu_tail_ok3
  · exact sjsu_tail_ok4
  · exact sjsu_tail_ok5
  · exact sjsu_tail_ok6
  · exact sjsu_tail_ok7
  · exact sjsu_tail_ok8
  · exact sjsu_tail_ok9

end KAM.EffectiveStability.SJSU

end
