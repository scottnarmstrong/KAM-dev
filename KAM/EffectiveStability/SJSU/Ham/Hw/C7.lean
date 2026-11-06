/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C7P0
public import KAM.EffectiveStability.SJSU.Ham.Hw.C7P1

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 7: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 7, in file order, in chunks. -/
def sjsuCD7 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD7B0, sjsuCD7B1, sjsuCD7B2, sjsuCD7B3, sjsuCD7B4, sjsuCD7B5, sjsuCD7B6]

/-- **Kernel check**: the literal rows are the model rows of degree 7, converted. -/
theorem sjsuCD7_check : listBEq (sjsuIntChunks 7).flatten sjsuCD7.flatten = true := by
  decide +kernel

theorem sjsuCD7B0_keys : sjsuCD7B0.all (keyIn sjsuA7) = true := by
  decide +kernel

theorem sjsuCD7B1_keys : sjsuCD7B1.all (keyIn sjsuA7) = true := by
  decide +kernel

theorem sjsuCD7B2_keys : sjsuCD7B2.all (keyIn sjsuA7) = true := by
  decide +kernel

theorem sjsuCD7B3_keys : sjsuCD7B3.all (keyIn sjsuA7) = true := by
  decide +kernel

theorem sjsuCD7B4_keys : sjsuCD7B4.all (keyIn sjsuA7) = true := by
  decide +kernel

theorem sjsuCD7B5_keys : sjsuCD7B5.all (keyIn sjsuA7) = true := by
  decide +kernel

theorem sjsuCD7B6_keys : sjsuCD7B6.all (keyIn sjsuA7) = true := by
  decide +kernel

theorem sjsuCD7_keys : ∀ e ∈ sjsuCD7.flatten, e.1.1 ∈ sjsuA7 ∧ e.1.2 ∈ sjsuA7 := by
  have h : sjsuCD7.flatten.all (keyIn sjsuA7) = true := by
    simp only [sjsuCD7, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD7B0_keys, sjsuCD7B1_keys, sjsuCD7B2_keys, sjsuCD7B3_keys, sjsuCD7B4_keys,
      sjsuCD7B5_keys, sjsuCD7B6_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
