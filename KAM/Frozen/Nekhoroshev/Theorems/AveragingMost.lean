/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.Nekhoroshev.Defs.IsAnalyticIntegrable
public import KAM.Frozen.Nekhoroshev.Defs.IsAnalyticPerturbation
public import KAM.Frozen.Nekhoroshev.Defs.IsSolutionOn
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import KAM.Frozen.Nekhoroshev.Defs.HasAveragingFrequencyRank
import KAM.Provider.Nekhoroshev.AveragingMost

/-!
# Frozen theorem `KAM.Nekhoroshev.averaging_most`

Owner-approved on 2026-10-27 (decision D28). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Nekhoroshev.averaging_most` when the provider `KAM.Provider.Nekhoroshev.AveragingMost`
is complete (sealing).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace KAM.Nekhoroshev

/-- N-AVERAGING-MOST, derived from AKN06 p.243 and Neishtadt 1976 pp.1295--1298.
Local-domain, actual-solution consequence of AKN (6.28).
Existence and confinement are conclusions on the good data, not premises.
The source smoothness convention is AKN06 p.3 footnote 1; the averaged-orbit
collar is Remark 6.4, pp.217--218. Neishtadt Theorem 2 includes existence
in its good-data definition; notes.md gives the stopped proof plan and corrects
the maximum-error step. No flow or future confinement is assumed here. -/
theorem averaging_most
    {n : ℕ} (hn : 2 ≤ n) (R s : ℝ) (hR : 0 < R) (hs : 0 < s)
    (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (hh : IsAnalyticIntegrable R s h) (hf : IsAnalyticPerturbation R s 1 f)
    (hrank : HasAveragingFrequencyRank (actionBall n R) h)
    (K : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hK : IsCompact K)
    (hKI : ∀ x ∈ K, x.2 ∈ actionBall n (R / 2)) :
    ∃ A ε₀ η₀ : ℝ, 0 < A ∧ 0 < ε₀ ∧ 0 < η₀ ∧ η₀ ≤ R / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∃ E : Set ((Fin n → ℝ) × (Fin n → ℝ)), MeasurableSet E ∧ E ⊆ K ∧
        volume E ≤ ENNReal.ofReal (A * Real.sqrt ε / η) ∧
        ∀ x ∈ K \ E, ∃ z : ℝ → ((Fin n → ℝ) × (Fin n → ℝ)),
          z 0 = x ∧
          IsSolutionOn (KAM.realHamiltonian h (fun w => (ε : ℂ) * f w))
            (actionBall n R) (Set.Icc 0 (1 / ε)) z ∧
          ∀ t ∈ Set.Icc 0 (1 / ε), ‖(z t).2 - x.2‖ ≤ η :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Nekhoroshev.averaging_most hn R s hR hs h f hh hf hrank K hK hKI
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Nekhoroshev

end
-- FROZEN_ANCHOR_SUFFIX_END
