/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Core
public import KAM.Planetary.StrongAMD.AnalyticDomain.Safety
public import KAM.Planetary.StrongAMD.AnalyticDomain.Extension
public import KAM.Planetary.StrongAMD.AnalyticDomain.Containment
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds

/-!
# The whole-sublevel planar analytic domain (facade)

Package LP-DOM, `LP:MAIN L8 (244–271)` with amendments N2, N3; track LP, non-frozen; the statement
surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

* `AnalyticDomain.Core`: D0 (`isCompact_strongLSet`, `strongLSet_subset_chamber`), D1
  (`exists_isSharedTube`), D2 (`strongCore`, `isCompact_strongCore`, `strongCore_subset_dom`).
* `AnalyticDomain.Safety`: D3 (`strongCore_barrierState`, `strongCore_subset_chartSafe`).
* `AnalyticDomain.Extension`: D4 (`exists_strongTube`), D6 (`movingHamiltonian_poincareProd_split`).
* `AnalyticDomain.Containment`: D5 (`strongCore_containment`).
-/

@[expose] public section

end
