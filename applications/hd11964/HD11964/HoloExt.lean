/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.HoloExt.Point
public import HD11964.HoloExt.Real

/-!
# HD 11964: the fully complexified perturbation (HD11964-HOLO, (1c); facade)

Imports the parts:

* `HD11964.HoloExt.Point`: the fully complexified chart and perturbation (`CVar`, `qpCC`,
  `distSqCC`, `pertCC`, `realVar`), the chart conditions (`PlanetOk`, `ChartOkAt`),
  `keplerSol_analyticAt`, analyticity at a point `pertCC_analyticAt` (1c-i), periodicity
  `pertCC_add_single` (1c-ii);
* `HD11964.HoloExt.Real`: agreement at real points `planetChartC_ofReal`, `pertCC_realVar_ofReal`
  (1c-iii); (1c) in the drafted form on the strips, `chartPertExt_HD` / `_A` / `_B`, with (1b) as
  the named premise `NoCollisionOn`; the decided cell-to-slab check `fitPlan_slabs_xi`.
-/

public section
