/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Iso.Defs.IsHamiltonianSolutionOn
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialHamiltonian
public import KAM.Frozen.Planetary.Spatial.Defs.SpatialNoCollision

/-!
# Frozen definition `KAM.Planetary.Spatial.IsSpatialMovingSolutionOn`

Track LP, `LP:MAIN §1 (1) (17–24), L1, d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): a literal formula or predicate of the source, faithful on its whole
carrier.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- A genuine spatial moving-Sun solution on `J`: the frozen differentiability-guarded Hamiltonian
ODE for `H_μ` together with collision exclusion (`LP:MAIN §1 (1)`). -/
def IsSpatialMovingSolutionOn {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (J : Set ℝ)
    (z : ℝ → Phase (n * 3)) : Prop :=
  KAM.Iso.IsHamiltonianSolutionOn (spatialHamiltonian ν μ) Set.univ J z ∧
    ∀ t ∈ J, SpatialNoCollision (z t).1

end KAM.Planetary.Spatial

end
