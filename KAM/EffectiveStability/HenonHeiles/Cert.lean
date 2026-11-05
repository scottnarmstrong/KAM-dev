/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorChainCheck
public import KAM.EffectiveStability.HenonHeiles.Data.Residual
public import KAM.EffectiveStability.HenonHeiles.Data.Step1
public import KAM.EffectiveStability.HenonHeiles.Data.Step2
public import KAM.EffectiveStability.HenonHeiles.Data.Step3

/-!
# The Hénon–Heiles certificate (track B, B3-CERT)

The data of `hhCert : OscChainCertK QSqrt2 2` (producer output `out/hh-cert.json`), with the three
steps `hhStep1..3`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

open CartPoly

/-- Step 1: degree-3 generator, Lie order 5. -/
def hhStep1 : OscStepK QSqrt2 := ⟨hhGen1, hhOut1, 5, 5047 / 31250000, 4611 / 31250000000, 1 / 2⟩

/-- Step 2: degree-4 generator, Lie order 2. -/
def hhStep2 : OscStepK QSqrt2 := ⟨hhGen2, hhOut2, 2, 161431 / 1000000000, 11 / 250000000000, 1 / 2⟩

/-- Step 3: degree-5 generator, Lie order 2. -/
def hhStep3 : OscStepK QSqrt2 := ⟨hhGen3, hhOut3, 2, 161431 / 1000000000, 1 / 1000000000000, 1 / 2⟩

/-- The Hénon–Heiles certificate. -/
def hhCert : OscChainCertK QSqrt2 2 where
  H := hhH
  Nact := hhNact
  P := hhP
  steps := [hhStep1, hhStep2, hhStep3]
  δc := 1 / 50000
  εb := 1 / 1000000000000
  T := 10000000000
  a := [6561 / 1000000000000, 6561 / 1000000000000]
  b := [1 / 100000000, 1 / 100000000]
  η := [1 / 10000000000000000000, 1 / 10000000000000000000]
  r := [14143 / 100000000, 14143 / 100000000]

end KAM.EffectiveStability.HenonHeiles

end
