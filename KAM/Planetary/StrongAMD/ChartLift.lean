/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.ChartLift.Stopped
public import KAM.Planetary.StrongAMD.ChartLift.Lift
public import KAM.Planetary.StrongAMD.ChartLift.Premises

/-!
# The chart lift on the stopped interval (package LP-LIFT, facade)

Package LP-LIFT, MAIN Lemma 14, chart part (`LP:MAIN L14 (468–500)`), track LP, non-frozen.
Facade for `ChartLift.Stopped` (prograde states and the whole-ball bound), `ChartLift.Lift` (the
chart lift) and `ChartLift.Premises` (the D1 premises of the Lemma 13 adapter).
-/
