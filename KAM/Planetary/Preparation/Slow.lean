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

/-!
# Slow averaging facade (P11A-P7, `bpP:p11:avg-slow`)

Facade over the P7 modules. PARTIAL: the core theorem `avg_slow_of_spec` is not yet proved.
-/
