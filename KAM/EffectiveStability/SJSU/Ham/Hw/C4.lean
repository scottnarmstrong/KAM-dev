/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C4P0

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 4: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 4, in file order, in chunks. -/
def sjsuCD4 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD4B0, sjsuCD4B1]

/-- **Kernel check**: the literal rows are the model rows of degree 4, converted. -/
theorem sjsuCD4_check : listBEq (sjsuIntChunks 4).flatten sjsuCD4.flatten = true := by
  decide +kernel

theorem sjsuCD4B0_keys : sjsuCD4B0.all (keyIn sjsuA4) = true := by
  decide +kernel

theorem sjsuCD4B1_keys : sjsuCD4B1.all (keyIn sjsuA4) = true := by
  decide +kernel

theorem sjsuCD4_keys : ∀ e ∈ sjsuCD4.flatten, e.1.1 ∈ sjsuA4 ∧ e.1.2 ∈ sjsuA4 := by
  have h : sjsuCD4.flatten.all (keyIn sjsuA4) = true := by
    simp only [sjsuCD4, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD4B0_keys, sjsuCD4B1_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
