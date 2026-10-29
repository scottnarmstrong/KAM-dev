/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Preparation.SlowData
public import KAM.Planetary.Preparation.SlowCauchy
public import KAM.Planetary.Preparation.SlowJets
public import KAM.Planetary.Preparation.SlowMean
public import KAM.Planetary.Preparation.SlowAverage
public import KAM.Planetary.Preparation.SlowDivisor
public import KAM.Planetary.Preparation.SlowRates
public import KAM.Planetary.Preparation.SlowSmall
public import KAM.Planetary.Preparation.SlowConclude
public import KAM.Planetary.Preparation.SlowCoeff
public import KAM.Planetary.Preparation.SlowMW
public import KAM.Planetary.Preparation.SlowAssembly
public import KAM.Planetary.Preparation.SlowSigned

/-!
# Slow averaging facade (P11A-P7, `bpP:p11:avg-slow`)

Facade over the P7, P7b, P7c and P7d modules; `avg_slow` (signed) is proved in `SlowSigned`.
-/
