/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.NhatTaylor
import Mathlib.Tactic.Linarith

/-!
# The zero Taylor element (blueprint-W `bpW:w5:step`)

`zeroTaylor`: the element `0 ∈ 𝒯_s`; used as the value of parameter families outside the parameter
set `Π`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The zero element of `𝒯_s`. -/
def zeroTaylor (a p pb s : ℝ) : HomTaylor_gen a p pb s where
  a0 := fun _ => 0
  b := fun _ => 0
  cp := fun _ => 0
  cm := fun _ => 0
  P := fun _ => 0
  P' := fun _ => 0
  Q := fun _ => 0
  Qt := fun _ => 0
  comp_a0 := isHomComp_const s _
  comp_b := isHomComp_const s _
  comp_cp := isHomComp_const s _
  comp_cm := isHomComp_const s _
  comp_P := isHomComp_const s _
  comp_P' := isHomComp_const s _
  comp_Q := isHomComp_const s _
  comp_Qt := isHomComp_const s _
  symP := fun _ _ i j => by simp [homNormalEntry_gen, kamEntry]
  symP' := fun _ _ i j => by simp [homNormalEntry_gen, kamEntry]
  transQ := fun _ _ i j => by simp [homNormalEntry_gen, kamEntry]

end KAM.Wave
