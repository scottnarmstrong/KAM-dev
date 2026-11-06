/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.TailData
public import KAM.EffectiveStability.SJSU.Confinement.Shift
public import KAM.EffectiveStability.Tube.Check.TailQ

/-!
# Accessors and box checks of the remainder data (T2-CONF, N9 (C))

The lookups `sjsuGT K j m`, `sjsuGTD`, `sjsuGTP`, `sjsuTT K`, `sjsuTU K i`, `sjsuTP K`, `sjsuW d`,
`sjsuWp d` into the generated lists of `TailData`, the radius `sjsuTailR = 2·10⁻⁶`, and the checks
of the short-decimal box (`sjsu_tail_box`): `2·10⁻⁶ < sjsuTailBmin ≤ sjsuBmin`,
`sjsuBmax ≤ sjsuTailBmax ≤ sjsuTailHi²`.
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The tube radius `κδ = 2·10⁻⁶`. -/
def sjsuTailR : ℚ := 2 / 1000000

def sjsuGT (K : ℕ) (j : Fin 3) (m : ℕ) : ℚ := ((sjsuGTlist.getD K []).getD j.val []).getD m 0
def sjsuGTD (K : ℕ) (j : Fin 3) (m : ℕ) : ℚ := ((sjsuGTDlist.getD K []).getD j.val []).getD m 0
def sjsuGTP (K : ℕ) (j : Fin 3) (m : ℕ) : ℚ := ((sjsuGTPlist.getD K []).getD j.val []).getD m 0
def sjsuTT (K : ℕ) : ℚ := sjsuTTlist.getD K 0
def sjsuTU (K : ℕ) (i : Fin 3) : ℚ := (sjsuTUlist.getD K []).getD i.val 0
def sjsuTP (K : ℕ) : ℚ := sjsuTPlist.getD K 0
def sjsuW (d : ℕ) : ℚ := sjsuWlist.getD d 0
def sjsuWp (d : ℕ) : ℚ := sjsuWplist.getD d 0

/-- The hats of the SJSU instance (`L = 9`, short-decimal box). -/
def sjsuHat (j : Fin 3) (n m : ℕ) : ℚ := slotHatQ 9 (sjsuTailBmin j) (sjsuTailBmax j) sjsuTailR n m
def sjsuHatDu (j : Fin 3) (n m : ℕ) : ℚ :=
  slotHatDuQ 9 (sjsuTailBmin j) (sjsuTailBmax j) sjsuTailR n m
def sjsuHatP (j : Fin 3) (n m : ℕ) : ℚ :=
  slotHatPQ 9 (sjsuTailBmin j) (sjsuTailBmax j) sjsuTailR n m

/-- The short-decimal box of the tube centre. -/
theorem sjsu_tail_box (j : Fin 3) :
    sjsuTailR < sjsuTailBmin j ∧ sjsuTailBmin j ≤ sjsuBmin j ∧ sjsuBmax j ≤ sjsuTailBmax j ∧
      0 ≤ sjsuTailHi j ∧ sjsuTailBmax j ≤ sjsuTailHi j ^ 2 := by
  revert j; decide +kernel

end KAM.EffectiveStability.SJSU

end
