/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.ChartLift.Stopped
public import KAM.Planetary.Spatial.ChartLift.Uniform
public import KAM.Planetary.Spatial.ChartLift.Setting
public import KAM.Planetary.Spatial.ChartLift.Lift
public import KAM.Planetary.Spatial.ChartLift.Premises

/-!
# The spatial chart lift on a stopped interval (facade)

Package LP-SP-LIFT, MAIN Lemma 14 with the Lemma 18 alignment, `d = 3`; track LP, non-frozen.
The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

Facade over `ChartLift.{Stopped, Uniform, Setting, Lift, Premises}`:
`SpatialLiftData`, `SpatialStoppedOn`, `SpatialLiftData.spLift_prograde_of_stopped`,
`SpatialLiftData.spLift_strongAMD_le_of_stopped`, `SpatialLiftData.spatialChartLift_of_stopped`,
`SpatialLiftData.spatialChartLift_premises`.
-/

@[expose] public section

end
