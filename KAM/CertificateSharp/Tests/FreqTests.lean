/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Freq.SmallDivisorFiber
public import KAM.CertificateSharp.Freq.QuadraticLunar

/-!
# Kernel tests of the frequency checkers (C2)

Small test models only (never lunar data): the box test and the fibered test on a toy frequency
`(0.618, 1)` at `δ = 1/2`, `N = 6`, and the quadratic checker on the four lunar instances
(`QuadraticLunar`). Both side-condition tests pass (`decide +kernel`), and the
fibered one needs `2N = 12` entries against `≈ 4N² = 144` modes.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM.Certificate

/-- The toy box for `ω' = 0.618`. -/
def toyBox1 : FreqBox := [(618 / 1000, 1 / 1000000)]

/-- The toy box for `ω = (0.618, 1)`. -/
def toyBox2 : FreqBox := [(618 / 1000, 1 / 1000000), (1, 0)]

/-- The toy bound data. -/
def toyData (box : FreqBox) : SdsData :=
  { box := box, γ := 1 / 10, δ := 1 / 2, N := 6, J := 12, E1 := 1 / 20 }

example : (toyData toyBox2).check (n := 2) = true := by decide +kernel

example : (toyData toyBox1).fiberCheck (m := 1) = true := by decide +kernel

/-- The stage list over the toy box. -/
example : sdsStagesOk 2 toyBox2 (1 / 10)
    [{ δ := 1 / 2, N := 6, J := 12, E1 := 1 / 20, claim := 100 },
     { δ := 1, N := 4, J := 12, E1 := 1 / 400, claim := 100 }] = true := by decide +kernel

-- The axioms of the main results.
#print axioms isDiophantine_of_quadCheck
#print axioms lunarNuMinus_isDiophantine_exact
#print axioms lunarNuPlus_isDiophantine_exact
#print axioms lunarNuMinus_sub_one_isDiophantine_exact
#print axioms lunarNuPlus_sub_one_isDiophantine_exact
#print axioms sdsBound_sound
#print axioms sdsStagesOk_sound
#print axioms sdsFiberBound_sound

end KAM.CertificateSharp
