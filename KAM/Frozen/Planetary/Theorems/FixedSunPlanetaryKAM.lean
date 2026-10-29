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
public import KAM.Frozen.Planetary.Defs.FixedKolmogorovSet
import KAM.Provider.Planetary.FixedSunPlanetaryKAM

/-!
# Frozen theorem `KAM.Planetary.fixedSunPlanetaryKAM`

Owner-approved on 2026-10-27 (decision D20). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.fixedSunPlanetaryKAM` when the provider
`KAM.Provider.Planetary.FixedSunPlanetaryKAM` is complete (sealing).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

/-- P-FIXED: our proposed Newtonian fixed-center deduction, not a published fixed-Sun
statement. Fejoz Lemma 64, Proposition 77; analytic KAM input CP09 Theorem 4.
No arbitrary perturbing function or assumed secular nondegeneracy is a premise. -/
theorem fixedSunPlanetaryKAM {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.fixedSunPlanetaryKAM
      hn G m0 m a hG hm0 hm ha hsep eta heta
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary

end
-- FROZEN_ANCHOR_SUFFIX_END
