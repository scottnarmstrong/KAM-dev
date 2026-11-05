/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Planetary.Spatial.Defs.SpatialBarycentricPositions

/-!
# Frozen definition `KAM.Planetary.Spatial.spatialSourceBarycentricPositions`

Track LP, `LP:MAIN L1 (100–108), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a source-facing literal formula on its carrier
(CHARACTERIZATION: N/A_LITERAL; draft 7, §4). Its source domain is given by the proof arguments
`_hν : ∀ i, 0 < ν i` and `_hμ : 0 < μ` (the source premises of MAIN L1: positive masses and positive
μ), which exclude the zero-denominator inputs of the internal total helper
`spatialBarycentricPositions`, to which it is definitionally equal (statement audit of draft 7, F1).
CHARACTERIZATION: N/A_LITERAL; MAIN L1 (100–106) gives the reconstruction by this explicit formula,
and no barycentric identity is frozen for it, as for the already-frozen planar
`KAM.Planetary.barycentricPositions`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

def spatialSourceBarycentricPositions {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ)
    (_hν : ∀ i, 0 < ν i) (_hμ : 0 < μ) (q : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) := spatialBarycentricPositions ν μ q

end KAM.Planetary.Spatial

end
