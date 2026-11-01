/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.AnalyticDomain.Core
public import KAM.Planetary.Spatial.AnalyticDomain.Safety
public import KAM.Planetary.Spatial.AnalyticDomain.Extension
public import KAM.Planetary.Spatial.AnalyticDomain.Containment
public import KAM.Planetary.Spatial.AnalyticDomain.Alignment

/-!
# The spatial whole-sublevel complex domain (facade)

Package LP-SP-DOM, `LP:MAIN L18 (580–597)`, track LP, non-frozen. Facade importing the modules of
`KAM/Planetary/Spatial/AnalyticDomain/`:

* `Core`: D2 `spatialStrongCore` (MAIN (47)), compactness, margin, inclusion in the chart domain;
* `Safety`: D3 core points are `SpatialBarrierState`s for the whole ball, and collision free;
* `Extension`: D4 `exists_spatialStrongTube` (via `tubeNM`), D6 the exact split `h + μ f`;
* `Containment`: D5 MAIN (22) with (47) lies in the half tube;
* `Alignment`: the alignment remark (MAIN 595–597).

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/
