/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C5P0

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 5: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 5, in file order, in chunks. -/
def sjsuCD5 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD5B0, sjsuCD5B1, sjsuCD5B2]

/-- **Kernel check**: the literal rows are the model rows of degree 5, converted. -/
theorem sjsuCD5_check : listBEq (sjsuIntChunks 5).flatten sjsuCD5.flatten = true := by
  decide +kernel

theorem sjsuCD5B0_keys : sjsuCD5B0.all (keyIn sjsuA5) = true := by
  decide +kernel

theorem sjsuCD5B1_keys : sjsuCD5B1.all (keyIn sjsuA5) = true := by
  decide +kernel

theorem sjsuCD5B2_keys : sjsuCD5B2.all (keyIn sjsuA5) = true := by
  decide +kernel

theorem sjsuCD5_keys : ∀ e ∈ sjsuCD5.flatten, e.1.1 ∈ sjsuA5 ∧ e.1.2 ∈ sjsuA5 := by
  have h : sjsuCD5.flatten.all (keyIn sjsuA5) = true := by
    simp only [sjsuCD5, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD5B0_keys, sjsuCD5B1_keys, sjsuCD5B2_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
