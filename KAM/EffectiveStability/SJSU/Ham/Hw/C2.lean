/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.IntModel
public import KAM.EffectiveStability.SJSU.Ham.Hw.A
public import KAM.EffectiveStability.SJSU.Ham.Hw.C2P0

/-!
# Integer model rows of `SJSU18-O2`, `z`-degree 2: checks (T2-CONF, N5a; generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The integer model rows `c · 10^E` of `z`-degree 2, in file order, in chunks. -/
def sjsuCD2 : List (List ((Mon × Mon) × ℤ)) :=
  [sjsuCD2B0]

/-- **Kernel check**: the literal rows are the model rows of degree 2, converted. -/
theorem sjsuCD2_check : listBEq (sjsuIntChunks 2).flatten sjsuCD2.flatten = true := by
  decide +kernel

theorem sjsuCD2B0_keys : sjsuCD2B0.all (keyIn sjsuA2) = true := by
  decide +kernel

theorem sjsuCD2_keys : ∀ e ∈ sjsuCD2.flatten, e.1.1 ∈ sjsuA2 ∧ e.1.2 ∈ sjsuA2 := by
  have h : sjsuCD2.flatten.all (keyIn sjsuA2) = true := by
    simp only [sjsuCD2, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      sjsuCD2B0_keys, Bool.and_true]
  intro e he
  have := List.all_eq_true.1 h e he
  simpa [keyIn] using this

end KAM.EffectiveStability.SJSU

end
