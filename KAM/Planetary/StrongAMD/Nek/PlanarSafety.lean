/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.Nek.PlanarSafety.Orientation
public import KAM.Planetary.StrongAMD.Nek.PlanarSafety.Prograde
public import KAM.Planetary.StrongAMD.Nek.PlanarSafety.Main

/-!
# The planar theorem the Nekhoroshev part (facade)

Source: (MAIN Theorem 15 with Lemma 16, Nekhoroshev drift), track LP, non-frozen.
Re-exports the parts: `Orientation` (reflection transport of the conclusion, drift scale as a
parameter), `Prograde` (the theorem for `L > 0`), `Main` (`lp3_planar_strongAMD_safety` and its
normalized form).

-/

public section
