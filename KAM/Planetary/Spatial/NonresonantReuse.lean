/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.NonresonantReuse.Pert
public import KAM.Planetary.Spatial.NonresonantReuse.PertClass
public import KAM.Planetary.Spatial.NonresonantReuse.Hyp
public import KAM.Planetary.Spatial.NonresonantReuse.Drift

/-!
# The spatial engine data and stopped drift (facade)

Source: MAIN Lemma 13 with `2n` slow pairs and Theorem 19
(`LP:MAIN L13 (429–464)`, `LP:MAIN T19 (599–603)`), track LP, non-frozen. Facade importing the
modules of `KAM/Planetary/Spatial/NonresonantReuse/`:

* `Pert`: `lpUnrescaleCNM`, `lpPertNM`, `LPChartTubeNM`, containment in `complexTubeNM`;
* `PertClass`: `ext_class`, sup bound and `WBound` of `lpPertNM`;
* `Hyp`: the trace identity `lpTraceNM` and `lpExtNFHypNM` for `PartialBlock n (n + n)`;
* `Drift`: `spatial_stopped_drift`, via `nonresonant_drift_of_chartDataNM`.

-/
