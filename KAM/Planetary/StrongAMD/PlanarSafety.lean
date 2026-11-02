/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.PlanarSafety.Orientation
public import KAM.Planetary.StrongAMD.PlanarSafety.Constants
public import KAM.Planetary.StrongAMD.PlanarSafety.Prograde
public import KAM.Planetary.StrongAMD.PlanarSafety.Main

/-!
# The planar theorem LP1 (facade)

Source: (MAIN Theorem 15 with Lemma 16), track LP, non-frozen.  Re-exports the parts:
`Orientation` (reflection transport of the conclusion), `Constants` (budget radius, axis estimate),
`Prograde` (the theorem for `L > 0`), `Main` (`lp1_planar_strongAMD_safety`, its corollaries and
`lp0_planar_barrier`).

-/

public section
