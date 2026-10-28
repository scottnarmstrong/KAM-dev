/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Covering parameters (`bpN:p8:covering`, early interface)

The raw parameter record `CoverParams` of the covering lemma and its source-premise predicate
`CoverParams.Valid`. Only real numerical fields: no lattice, projection or Hamiltonian appears, so
that the constants of Part 9 (`theoremCover`) can use the record before the geometry of Part 8 is
available. The geometry-dependent definitions (`lam`, `radius`, `alpha`, `delta`, `actionBlock`) and
the covering and cutoff theorems live in `ResonanceGeometry/Covering.lean`.
-/

@[expose] public noncomputable section

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- Raw parameters `(p, b, r₀, M, m, K, A)` of the covering lemma. -/
structure CoverParams (n : ℕ) where
  p : ℝ
  b : ℝ
  r0 : ℝ
  M : ℝ
  m : ℝ
  K : ℝ
  A : ℝ

/-- The source premises of the covering lemma on the raw parameters. -/
structure CoverParams.Valid (c : CoverParams n) : Prop where
  hn : 1 ≤ n
  hp : 0 < c.p
  hb : 0 < c.b
  hr0 : 0 < c.r0
  hM : 0 < c.M
  hm : 0 < c.m
  hK : 1 ≤ c.K
  hA : c.p * c.M / (c.b * c.m) + Real.sqrt 2 ≤ c.A

end KAM.Nekhoroshev
