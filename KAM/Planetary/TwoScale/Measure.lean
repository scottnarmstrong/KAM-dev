/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.MeasureJoint

/-!
# Two-scale KAM: measure estimates (`bpP:p3:meas-actions`, `bpP:p3:meas-torus`), facade

Facade over `MeasureActions` (`ActionsMeas`, `meas_actions_of_limit`), `MeasureScaled`
(`scaled_cover`, `lip_image_scaled`), `MeasureTorus` (`TorusMeas`, `TorusMeas.meas_torus_of_limit`)
and `MeasureJoint` (constructors `actionsMeas_of_limit`, `torusMeas_of_limit`, `ko_eq`,
`meas_torus_final` and the joint check `meas_of_iterative`). These are private conditional
interfaces (design finding N2): the only hypotheses are bundles of proved outputs of
`limit_actions_of_steps` and `limit_phi_real_of_steps` on the shared witnesses of `iterative`.
Design package P23-21.
-/
