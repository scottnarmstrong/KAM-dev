/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C3P0

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 3: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 3, in file order, in chunks. -/
def sjsuCD3 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD3B0]

/-- **Kernel check**: the literal rows are the model rows of degree 3, converted. -/
theorem sjsuCD3_check : listBEq (sjsuIntChunks 3).flatten sjsuCD3.flatten = true := by
  decide +kernel

theorem sjsuCD3B0_keys : sjsuCD3B0.all (keyIn sjsuA3) = true := by
  decide +kernel

theorem sjsuCD3_keys : ∀ e ∈ sjsuCD3.flatten, e.1.1 ∈ sjsuA3 ∧ e.1.2 ∈ sjsuA3 := by
  have h : sjsuCD3.flatten.all (keyIn sjsuA3) = true := by
    simp only [sjsuCD3, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD3B0_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
