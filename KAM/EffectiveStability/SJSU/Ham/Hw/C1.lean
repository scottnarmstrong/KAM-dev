/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C1P0

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 1: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 1, in file order, in chunks. -/
def sjsuCD1 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD1B0]

/-- **Kernel check**: the literal rows are the model rows of degree 1, converted. -/
theorem sjsuCD1_check : listBEq (sjsuIntChunks 1).flatten sjsuCD1.flatten = true := by
  decide +kernel

theorem sjsuCD1B0_keys : sjsuCD1B0.all (keyIn sjsuA1) = true := by
  decide +kernel

theorem sjsuCD1_keys : ∀ e ∈ sjsuCD1.flatten, e.1.1 ∈ sjsuA1 ∧ e.1.2 ∈ sjsuA1 := by
  have h : sjsuCD1.flatten.all (keyIn sjsuA1) = true := by
    simp only [sjsuCD1, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD1B0_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
