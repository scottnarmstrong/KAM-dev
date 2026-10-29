/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import KAM.Frozen.Defs.IsDiophantine
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Defs.MovingKolmogorovSet
import KAM.Provider.Planetary.PlanarTwoPlanetKAM

/-!
# Frozen theorem `KAM.Planetary.planarTwoPlanetKAM`

Owner-approved on 2026-10-27 (decision D20). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.planarTwoPlanetKAM` when the provider
`KAM.Provider.Planetary.PlanarTwoPlanetKAM` is complete (sealing).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

/-- P-PLANAR: analytic planar two-planet theorem, with moving Sun.
CP09 Theorem 4 with Fejoz Proposition 77, using the recorded source-proof repairs.
Fejoz erratum p.3 supplies the smooth counterpart. Only distinct ordered axes are assumed;
no numerical separation threshold is taken from CP11 Section 8.1 (audit P4). -/
theorem planarTwoPlanetKAM (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ mu0 d D : ℝ, 0 < mu0 ∧ 0 < d ∧ d < D ∧
      ∀ mu : ℝ, 0 < mu → mu < mu0 →
        ∃ S : Set (Phase (2 * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          MovingKolmogorovSet G m0 m a mu eta d D S :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.planarTwoPlanetKAM G m0 m a hG hm0 hm ha hsep eta heta
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary

end
-- FROZEN_ANCHOR_SUFFIX_END
