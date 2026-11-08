/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C6P0

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 6: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 6, in file order, in chunks. -/
def sjsuCD6 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD6B0, sjsuCD6B1, sjsuCD6B2, sjsuCD6B3]

/-- **Kernel check**: the literal rows are the model rows of degree 6, converted. -/
theorem sjsuCD6_check : listBEq (sjsuIntChunks 6).flatten sjsuCD6.flatten = true := by
  decide +kernel

theorem sjsuCD6B0_keys : sjsuCD6B0.all (keyIn sjsuA6) = true := by
  decide +kernel

theorem sjsuCD6B1_keys : sjsuCD6B1.all (keyIn sjsuA6) = true := by
  decide +kernel

theorem sjsuCD6B2_keys : sjsuCD6B2.all (keyIn sjsuA6) = true := by
  decide +kernel

theorem sjsuCD6B3_keys : sjsuCD6B3.all (keyIn sjsuA6) = true := by
  decide +kernel

theorem sjsuCD6_keys : ∀ e ∈ sjsuCD6.flatten, e.1.1 ∈ sjsuA6 ∧ e.1.2 ∈ sjsuA6 := by
  have h : sjsuCD6.flatten.all (keyIn sjsuA6) = true := by
    simp only [sjsuCD6, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD6B0_keys, sjsuCD6B1_keys, sjsuCD6B2_keys, sjsuCD6B3_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
