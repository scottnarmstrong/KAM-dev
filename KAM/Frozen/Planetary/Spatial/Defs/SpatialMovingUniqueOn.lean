/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Convex.Basic
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Spatial.Defs.IsSpatialMovingSolutionOn

/-!
# Frozen definition `KAM.Planetary.Spatial.SpatialMovingUniqueOn`

Track LP, `LP:MAIN §1 (69–72), L1, d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a literal formula or predicate of the source, faithful on its whole
carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- Agreement with every other local spatial solution on its overlap with the certified interval
(the pattern of the frozen planar `MovingUniqueOn`). -/
def SpatialMovingUniqueOn {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (J : Set ℝ)
    (z : ℝ → Phase (n * 3)) : Prop :=
  ∀ (U : Set ℝ) (w : ℝ → Phase (n * 3)), IsOpen U → Convex ℝ U → 0 ∈ U →
    w 0 = z 0 → IsSpatialMovingSolutionOn ν μ U w → ∀ t ∈ U ∩ J, w t = z t

end KAM.Planetary.Spatial

end
