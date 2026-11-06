/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C8P0
public import KAM.EffectiveStability.SJSU.Ham.Hw.C8P1

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 8: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 8, in file order, in chunks. -/
def sjsuCD8 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD8B0, sjsuCD8B1, sjsuCD8B2, sjsuCD8B3, sjsuCD8B4, sjsuCD8B5, sjsuCD8B6, sjsuCD8B7,
    sjsuCD8B8, sjsuCD8B9, sjsuCD8B10]

/-- **Kernel check**: the literal rows are the model rows of degree 8, converted. -/
theorem sjsuCD8_check : listBEq (sjsuIntChunks 8).flatten sjsuCD8.flatten = true := by
  decide +kernel

theorem sjsuCD8B0_keys : sjsuCD8B0.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B1_keys : sjsuCD8B1.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B2_keys : sjsuCD8B2.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B3_keys : sjsuCD8B3.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B4_keys : sjsuCD8B4.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B5_keys : sjsuCD8B5.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B6_keys : sjsuCD8B6.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B7_keys : sjsuCD8B7.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B8_keys : sjsuCD8B8.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B9_keys : sjsuCD8B9.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8B10_keys : sjsuCD8B10.all (keyIn sjsuA8) = true := by
  decide +kernel

theorem sjsuCD8_keys : ∀ e ∈ sjsuCD8.flatten, e.1.1 ∈ sjsuA8 ∧ e.1.2 ∈ sjsuA8 := by
  have h : sjsuCD8.flatten.all (keyIn sjsuA8) = true := by
    simp only [sjsuCD8, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD8B0_keys, sjsuCD8B1_keys, sjsuCD8B2_keys, sjsuCD8B3_keys, sjsuCD8B4_keys,
      sjsuCD8B5_keys, sjsuCD8B6_keys, sjsuCD8B7_keys, sjsuCD8B8_keys, sjsuCD8B9_keys,
      sjsuCD8B10_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
