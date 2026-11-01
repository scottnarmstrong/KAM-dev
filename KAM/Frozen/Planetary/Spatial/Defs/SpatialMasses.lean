/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Frozen definition `KAM.Planetary.Spatial.spatialMasses`

Track LP, `LP:MAIN L1 (100–108), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a literal formula or predicate of the source, faithful on its whole
carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- The masses `(1, μ ν_1, …, μ ν_n)`. -/
def spatialMasses {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons 1 (fun i => μ * ν i)

end KAM.Planetary.Spatial

end
