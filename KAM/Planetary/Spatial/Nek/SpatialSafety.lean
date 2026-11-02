/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Nek.SpatialSafety.Orientation
public import KAM.Planetary.Spatial.Nek.SpatialSafety.Aligned
public import KAM.Planetary.Spatial.Nek.SpatialSafety.Main

/-!
# The spatial theorem the Nekhoroshev part (facade)

Source: `LP:MAIN T19 (599–603)` with `L14`, `L16`, `L18` for `d = 3`; track LP,
non-frozen.

Facade over `Nek.SpatialSafety.{Orientation, Aligned, Main}`: `lp3_spatial_strongAMD_safety`,
`lp3_spatial_strongAMD_safety_normalized`, and the internal `spatial_nek_safety_of_aligned`.
-/

@[expose] public section

end
