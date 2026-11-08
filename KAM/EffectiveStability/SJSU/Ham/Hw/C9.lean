/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C9P0
public import KAM.EffectiveStability.SJSU.Ham.Hw.C9P1
public import KAM.EffectiveStability.SJSU.Ham.Hw.C9P2

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 9: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 9, in file order, in chunks. -/
def sjsuCD9 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD9B0, sjsuCD9B1, sjsuCD9B2, sjsuCD9B3, sjsuCD9B4, sjsuCD9B5, sjsuCD9B6, sjsuCD9B7,
    sjsuCD9B8, sjsuCD9B9, sjsuCD9B10, sjsuCD9B11, sjsuCD9B12, sjsuCD9B13, sjsuCD9B14, sjsuCD9B15]

/-- **Kernel check**: the literal rows are the model rows of degree 9, converted. -/
theorem sjsuCD9_check : listBEq (sjsuIntChunks 9).flatten sjsuCD9.flatten = true := by
  decide +kernel

theorem sjsuCD9B0_keys : sjsuCD9B0.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B1_keys : sjsuCD9B1.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B2_keys : sjsuCD9B2.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B3_keys : sjsuCD9B3.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B4_keys : sjsuCD9B4.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B5_keys : sjsuCD9B5.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B6_keys : sjsuCD9B6.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B7_keys : sjsuCD9B7.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B8_keys : sjsuCD9B8.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B9_keys : sjsuCD9B9.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B10_keys : sjsuCD9B10.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B11_keys : sjsuCD9B11.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B12_keys : sjsuCD9B12.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B13_keys : sjsuCD9B13.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B14_keys : sjsuCD9B14.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9B15_keys : sjsuCD9B15.all (keyIn sjsuA9) = true := by
  decide +kernel

theorem sjsuCD9_keys : ∀ e ∈ sjsuCD9.flatten, e.1.1 ∈ sjsuA9 ∧ e.1.2 ∈ sjsuA9 := by
  have h : sjsuCD9.flatten.all (keyIn sjsuA9) = true := by
    simp only [sjsuCD9, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD9B0_keys, sjsuCD9B1_keys, sjsuCD9B2_keys, sjsuCD9B3_keys, sjsuCD9B4_keys,
      sjsuCD9B5_keys, sjsuCD9B6_keys, sjsuCD9B7_keys, sjsuCD9B8_keys, sjsuCD9B9_keys,
      sjsuCD9B10_keys, sjsuCD9B11_keys, sjsuCD9B12_keys, sjsuCD9B13_keys, sjsuCD9B14_keys,
      sjsuCD9B15_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
