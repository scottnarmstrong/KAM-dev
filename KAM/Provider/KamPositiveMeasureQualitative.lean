/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.HeadQ
import KAM.Frozen.Theorems.KamPositiveMeasure

/-!
# Provider for the frozen theorem `KAM.kam_positive_measure_qualitative`

The proof of `KAM.kam_positive_measure_qualitative` is assembled here as
`KAM.Provider.kam_positive_measure_qualitative`, from graph predecessors and approved external
inputs only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other
than the anchor may import it.

This file imports the sealed frozen theorem `KAM.kam_positive_measure` (HEAD).

* `KAM.Provider.kam_positive_measure_qualitative` is the HEAD-Q theorem with exactly the type of
  the frozen `KAM.kam_positive_measure_qualitative`. It applies `KAM.Head.headq_of_head`, supplying
  its hypothesis `hHEAD` from the sealed `KAM.kam_positive_measure` at every action domain `B'`.
-/

public section

open MeasureTheory KAM.Head

namespace KAM.Provider

/-- **HEAD-Q.** Positive-measure KAM theorem, qualitative form (no boundary condition): the
provider of the frozen `KAM.kam_positive_measure_qualitative`, with exactly its type. -/
theorem kam_positive_measure_qualitative {n : ℕ} (hn : 2 ≤ n) {τ : ℝ} (hτ : (n : ℝ) - 1 < τ)
    {s₀ r₀ : ℝ} (hs₀ : 0 < s₀) (hr₀ : 0 < r₀)
    {B : Set (Fin n → ℝ)} (hB_open : IsOpen B) (hB_bdd : Bornology.IsBounded B)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (actionNbhd B r₀))
    (hh_real : ∀ I : Fin n → ℝ, (fun i => (I i : ℂ)) ∈ actionNbhd B r₀ →
      (h fun i => (I i : ℂ)).im = 0)
    (h_nondeg : ∃ L : ℝ, ∀ I ∈ closure B, ∀ J ∈ closure B,
      ‖I - J‖ ≤ L * ‖frequencyMap h I - frequencyMap h J‖) :
    ∀ κ : ℝ, 0 < κ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
        DifferentiableOn ℂ f (complexStrip n s₀ ×ˢ actionNbhd B r₀) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin n → ℤ,
          f (z.1 + (fun i => (k i : ℂ)), z.2) = f z) →
        (∀ θ I : Fin n → ℝ,
          ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀ →
          (f ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
        (∀ z ∈ complexStrip n s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε) → ε ≤ ε₀ →
        volume (fundamentalDomain B \ kamCover h f B r₀ τ κ) ≤
          ENNReal.ofReal κ * volume (fundamentalDomain B) :=
  headq_of_head hn hτ hs₀ hr₀ hB_open hB_bdd hh hh_real h_nondeg
    fun _ h1 h2 h3 h4 h5 h6 => KAM.kam_positive_measure hn hτ hs₀ hr₀ h1 h2 h3 h4 h5 h6

end KAM.Provider
