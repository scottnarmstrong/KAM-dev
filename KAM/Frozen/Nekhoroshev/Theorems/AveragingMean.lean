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
public import KAM.Frozen.Nekhoroshev.Defs.AveragingError
import KAM.Provider.Nekhoroshev.AveragingMean

/-!
# Frozen theorem `KAM.Nekhoroshev.averaging_mean`

Owner-approved on 2026-10-27 (decision D28). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Nekhoroshev.averaging_mean` when the provider `KAM.Provider.Nekhoroshev.AveragingMean`
is complete (sealing).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace KAM.Nekhoroshev

/-- N-AVERAGING-MEAN, analytic Hamiltonian specialization of AKN06 p.243 (6.27)--(6.28).
AKN Theorem 6.11 and Corollary 6.1 for genuine solution families.
The flow premise is only typing/existence on the stated interval;
there is no hypothesis about its error or about an exceptional set.
Constants are chosen after the fixed analytic system and compact initial set,
before ε, the solution family, and κ. Measure is unnormalized phase volume. -/
theorem averaging_mean
    {n : ℕ} (hn : 2 ≤ n) (R s : ℝ) (hR : 0 < R) (hs : 0 < s)
    (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (hh : IsAnalyticIntegrable R s h) (hf : IsAnalyticPerturbation R s 1 f)
    (hrank : HasAveragingFrequencyRank (actionBall n R) h)
    (K : Set ((Fin n → ℝ) × (Fin n → ℝ))) (hK : IsCompact K)
    (hKI : ∀ x ∈ K, x.2 ∈ actionBall n (R / 2)) :
    ∃ A ε₀ : ℝ, 0 < A ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ Φ : ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ → ((Fin n → ℝ) × (Fin n → ℝ)),
      (∀ x ∈ K, Φ x 0 = x ∧
        IsSolutionOn (KAM.realHamiltonian h (fun w => (ε : ℂ) * f w))
          (actionBall n R) (Set.Icc 0 (1 / ε)) (Φ x)) →
      IntegrableOn (averagingError ε Φ) K ∧
      (∫⁻ x in K, ENNReal.ofReal (averagingError ε Φ x) ∂volume)
        ≤ ENNReal.ofReal (A * Real.sqrt ε) ∧
      ∀ κ : ℝ, 0 < κ → ∃ E : Set ((Fin n → ℝ) × (Fin n → ℝ)),
        MeasurableSet E ∧ E ⊆ K ∧ volume E ≤ ENNReal.ofReal κ ∧
        ∀ x ∈ K \ E, ∀ t ∈ Set.Icc 0 (1 / ε),
          ‖(Φ x t).2 - x.2‖ ≤ A * Real.sqrt ε / κ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Nekhoroshev.averaging_mean hn R s hR hs h f hh hf hrank K hK hKI
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Nekhoroshev

end
-- FROZEN_ANCHOR_SUFFIX_END
