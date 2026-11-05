/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.SpatialSafety.Orientation
public import KAM.Planetary.Spatial.SpatialSafety.Constants
public import KAM.Planetary.Spatial.SpatialSafety.Bridge
public import KAM.Planetary.Spatial.SpatialSafety.Aligned
public import KAM.Planetary.Spatial.SpatialSafety.Main

/-!
# The spatial theorem LP2 (facade)

Source: MAIN Theorem 19 with Lemma 16 for `d = 3`; track LP, non-frozen.

Facade over `SpatialSafety.{Orientation, Constants, Bridge, Aligned, Main}`:
`lp2_spatial_strongAMD_safety`, `lp2_spatial_strongAMD_safety_normalized`,
`lp2_spatial_strongAMD_safety_halfInteger`, and the internal `spatial_safety_of_aligned`.
-/

@[expose] public section

end
