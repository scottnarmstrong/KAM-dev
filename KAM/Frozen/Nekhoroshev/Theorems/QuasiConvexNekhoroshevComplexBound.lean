/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.RealHamiltonian
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import KAM.Frozen.Nekhoroshev.Defs.ActionBall
public import KAM.Frozen.Nekhoroshev.Defs.RealActionDomain
public import KAM.Frozen.Nekhoroshev.Defs.IsAnalyticIntegrable
public import KAM.Frozen.Nekhoroshev.Defs.IsStrictlyQuasiConvex
public import KAM.Frozen.Nekhoroshev.Defs.HasDerivativeBounds
public import KAM.Frozen.Nekhoroshev.Defs.IsAnalyticPerturbation
public import KAM.Frozen.Nekhoroshev.Defs.IsSolutionOn
public import KAM.Frozen.Nekhoroshev.Defs.HasComplexHessianBound
import KAM.Provider.Nekhoroshev.QuasiConvexNekhoroshevComplexBound

/-!
# Frozen theorem `KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound`

Owner-approved on 2026-10-27 (decision D20). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` when the provider
`KAM.Provider.Nekhoroshev.QuasiConvexNekhoroshevComplexBound` is complete (sealing).
-/

@[expose] public section

namespace KAM.Nekhoroshev

/-- N-HEAD-C: a separate source-input variant using Pöschel 1993, Theorem 1, pp. 190--191.
Both new bounds precede the constants. `Mcomplex` supplies the complex Hessian bound;
`ωmin` supplies quantitative quasi-convexity and excludes Theorem 1's low-frequency exception.
The frequency upper bound required by its time prefactor follows from the retained real `B(M)`.
All conversions and source-line anchors are given in docs/tracks/N/sources.md.
This is a new proposal; the approved N-HEAD declaration above is unchanged. -/
theorem quasiConvex_nekhoroshev_complexBound {n : ℕ} (hn : 3 ≤ n) {R s M m Mcomplex ωmin : ℝ}
    (hR : 0 < R) (hs : 0 < s) (hM : 0 < M) (hm : 0 < m)
    (hMcomplex : 0 < Mcomplex) (hωmin : 0 < ωmin) :
    ∃ C T c ε₀ : ℝ, 0 < C ∧ 0 < T ∧ 0 < c ∧ 0 < ε₀ ∧
      C * ε₀ ^ ((1 : ℝ) / (2 * (n : ℝ))) ≤ R / 4 ∧
      ∀ (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        IsAnalyticIntegrable R s h →
        HasComplexHessianBound R s h Mcomplex →
        (∀ I ∈ actionBall n R, ωmin ≤ ‖KAM.frequencyMap h I‖) →
        IsStrictlyQuasiConvex (realActionDomain n R s) h m →
        HasDerivativeBounds (realActionDomain n R s) h M →
        IsAnalyticPerturbation R s ε f → 0 < ε → ε ≤ ε₀ →
        ∀ θ₀ I₀ : Fin n → ℝ, I₀ ∈ actionBall n (R / 2) →
          ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = (θ₀, I₀) ∧
            IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R)
              (Set.Icc (- (T * Real.exp (c * ε ^ (- ((1 : ℝ) / (2 * (n : ℝ)))))))
                (T * Real.exp (c * ε ^ (- ((1 : ℝ) / (2 * (n : ℝ))))))) z ∧
            (∀ t : ℝ, |t| ≤ T * Real.exp (c * ε ^ (- ((1 : ℝ) / (2 * (n : ℝ))))) →
              ‖(z t).2 - I₀‖ ≤ C * ε ^ ((1 : ℝ) / (2 * (n : ℝ)))) ∧
            (∀ (L : ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), 0 ≤ L →
              L ≤ T * Real.exp (c * ε ^ (- ((1 : ℝ) / (2 * (n : ℝ))))) →
              y 0 = (θ₀, I₀) →
              IsSolutionOn (KAM.realHamiltonian h f) (actionBall n R)
                (Set.Icc (-L) L) y → ∀ t ∈ Set.Icc (-L) L, y t = z t) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound hn hR hs hM hm hMcomplex
      hωmin
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Nekhoroshev

end
-- FROZEN_ANCHOR_SUFFIX_END
