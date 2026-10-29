/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic

/-!
# Axis cone: dilation closure

`bpP:p10:conv#data` (the `cone` clause): the set `A_n` of ordered positive axes is closed under
positive dilation.
-/

public section

namespace KAM.Planetary.SecularForm

/-- `bpP:p10:conv#data` (cone clause): `c > 0` and `a ∈ axes n` give `c • a ∈ axes n`. -/
theorem smul_mem_axes {n : ℕ} {c : ℝ} (hc : 0 < c) {a : Vec n} (ha : a ∈ axes n) :
    c • a ∈ axes n :=
  ⟨fun i => mul_pos hc (ha.1 i), fun _ _ hij => mul_lt_mul_of_pos_left (ha.2 hij) hc⟩

end KAM.Planetary.SecularForm
