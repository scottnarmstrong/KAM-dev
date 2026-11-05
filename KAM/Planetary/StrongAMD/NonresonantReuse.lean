/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.StrongAMD.NonresonantReuse.Kepler
public import KAM.Planetary.StrongAMD.NonresonantReuse.Pert
public import KAM.Planetary.StrongAMD.NonresonantReuse.PertClass
public import KAM.Planetary.StrongAMD.NonresonantReuse.Hyp
public import KAM.Planetary.StrongAMD.NonresonantReuse.Drift

/-!
# The engine's analytic data and the stopped drift

Facade for track LP, non-frozen: `Kepler` (period-one Kepler data, nonresonance), `Pert`/`PertClass`
(complex unrescaling and the perturbation), `Hyp` (`ExtNFHyp` and the trace identity), `Drift`
(`lp_stopped_drift`).
-/

@[expose] public section
end
