/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.FullRangeStepsExt
public import KAM.Iso.Linear.FullRangeStepsEnergy
public import KAM.Iso.Linear.FullRangeStepsFrame
public import KAM.Iso.Linear.FullRangeStepsPert

/-!
# Part 1 step exports under the source setting (graph gap GAP-I1b)

Facade for the 29 literal step exports of Part 1 (`step_eb_*`, `step_lr_*`, `step_ea_*`,
`step_ec_*`, `step_rd_*`, `step_geo_*`, `step_pt_*`); see the four `FullRangeSteps*` modules.
-/

public section
