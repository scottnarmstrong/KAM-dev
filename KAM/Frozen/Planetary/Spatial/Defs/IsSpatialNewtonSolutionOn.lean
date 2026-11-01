/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceLength

/-!
# Frozen definition `KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn`

Track LP, `LP:MAIN L1 (100–108), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a literal formula or predicate of the source, faithful on its whole
carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- Finite-interval Newton equations in dimension three, with Euclidean lengths (`G = 1`). -/
def IsSpatialNewtonSolutionOn {N : ℕ} (mass : Fin N → ℝ) (J : Set ℝ)
    (Q V : ℝ → Fin N → (Fin 3 → ℝ)) : Prop :=
  (∀ t ∈ J, ∀ i j, i ≠ j → 0 < spaceLength (Q t j - Q t i)) ∧
  (∀ t ∈ J, ∀ i, HasDerivAt (fun s => Q s i) (V t i) t) ∧
  (∀ t ∈ J, ∀ i, HasDerivAt (fun s => V s i)
    (∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
      (mass j / spaceLength (Q t j - Q t i) ^ 3) • (Q t j - Q t i)) t)

end KAM.Planetary.Spatial

end
