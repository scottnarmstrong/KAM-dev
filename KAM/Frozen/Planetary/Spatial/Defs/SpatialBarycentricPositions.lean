/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Fin.Tuple.Basic
public import KAM.Frozen.Planetary.Spatial.Defs.BodyVector3

/-!
# Frozen definition `KAM.Planetary.Spatial.spatialBarycentricPositions`

Track LP, `LP:MAIN L1 (100–108), d = 3` (MAIN as amended by AMENDMENTS). Owner-approved on
2026-11-01 (decision D62; docs/tracks/LP/FREEZE-PROPOSAL.md draft 7, under the rulings
of D59). This file is frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an
owner-approved versioned successor.

Freeze role (D59, OD-11 (b)): an internal total algebraic helper in the definition closure.
No source-object meaning is asserted off the source domain. Source-facing uses must supply
positive masses; barycentric reconstruction also supplies positive μ. The eccentricity-deficit
expression is interpreted only on [0,1]. Source-facing restrictions and guarded predicates,
rather than this total helper alone, carry the physical meaning.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

/-- Barycentric positions (star first, then the planets) from heliocentric `q`, with `m₀ = 1`. -/
def spatialBarycentricPositions {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) (q : Fin (n * 3) → ℝ) :
    Fin (n + 1) → (Fin 3 → ℝ) :=
  let x0 := (-μ / (1 + μ * ∑ i, ν i)) • ∑ i, ν i • bodyVector3 q i
  Fin.cons x0 (fun i => x0 + bodyVector3 q i)

end KAM.Planetary.Spatial

end
