/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.FundamentalDomain
public import KAM.Frozen.Russmann.Defs.RussmannCover
import KAM.Provider.Russmann.RussmannKam

/-!
# Frozen theorem `KAM.Russmann.russmann_kam`

Owner-approved on 2026-10-30 (R-HEAD with Q1(d), docs/tracks/R/RULINGS.md R1). This file is
frozen: it is hashed in `manifest/frozen-anchors.json`; any change needs an owner-approved
versioned successor. Rüssmann's KAM theorem under weak non-degeneracy (Rus01 Thm 1.7, p. 126,
maximal case `p = q = 0`), in the hypothesis style of `KAM.kam_positive_measure_qualitative`.
Only the proof body between the markers may change, and only to
`by exact KAM.Provider.Russmann.russmann_kam …` when the provider
`KAM.Provider.Russmann.RussmannKam` is complete (sealing).
-/

@[expose] public section

open MeasureTheory

namespace KAM.Russmann

open KAM

/-- **R-HEAD.** Rüssmann's KAM theorem (Rus01 Thm 1.7, maximal case). Let `h` be real-analytic on
a complex neighbourhood of a bounded connected open set `B ⊆ ℝⁿ` whose frequency map `ω = ∇h` is
not contained in any hyperplane through the origin: `c · ω ≢ 0` on `B` for every `c ≠ 0`. Then
there is a Diophantine exponent `τ > n - 1` such that, for every closeness `δ > 0`, every `κ > 0`
and every sufficiently small real-analytic perturbation `f`, the invariant Lagrangian tori of
`H = h + f` with `(γ, τ)`-Diophantine frequencies lying within `δ` of the unperturbed tori fill
`Tⁿ × B` up to a set of volume at most `κ · vol(Tⁿ × B)`. -/
theorem russmann_kam {n : ℕ} (hn : 1 ≤ n) {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} (hB_open : IsOpen B) (hB_conn : IsConnected B)
    (hB_bdd : Bornology.IsBounded B)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    (h_russmann : ∀ c : Fin n → ℝ, c ≠ 0 → ∃ I ∈ B, ∑ i, c i * frequencyMap h I i ≠ 0) :
    ∃ τ : ℝ, (n : ℝ) - 1 < τ ∧ ∀ δ : ℝ, 0 < δ → ∀ κ : ℝ, 0 < κ →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
          f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
        (∀ θ I : Fin n → ℝ,
          ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
          (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
        volume (fundamentalDomain B \ russmannCover h f B r₀ τ δ) ≤
          ENNReal.ofReal κ * volume (fundamentalDomain B) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Russmann

end
-- FROZEN_ANCHOR_SUFFIX_END
