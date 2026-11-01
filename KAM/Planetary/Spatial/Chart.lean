/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.Chart.Defs
public import KAM.Planetary.Spatial.Chart.Elements
public import KAM.Planetary.Spatial.Chart.Analytic
public import KAM.Planetary.Spatial.Chart.RotAlgebra
public import KAM.Planetary.Spatial.Chart.LineDeriv
public import KAM.Planetary.Spatial.Chart.Symplectic
public import KAM.Planetary.Spatial.Chart.Inverse
public import KAM.Planetary.Spatial.Chart.Image
public import KAM.Planetary.Spatial.Chart.Diffeo

/-!
# The regular spatial Poincare chart for one body (facade)

Package LP-SP-CHART, `LP:MAIN L17 (533–578)`, track LP, non-frozen. Facade importing
the modules of `KAM/Planetary/Spatial/Chart/`:

* `Defs`: (44) `spatialPoincareDom`, (46) `spatialPoincare`, item 1;
* `Elements`: (45), item 2;
* `Analytic`: analyticity and `2π`-periodicity, item 4;
* `RotAlgebra`, `LineDeriv`, `Symplectic`: the symplectic computation, item 5;
* `Inverse`, `Image`, `Diffeo`: the inverse, the image and local analytic diffeomorphism, item 3.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/
