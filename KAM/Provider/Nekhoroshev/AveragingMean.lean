/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Mean

/-!
# Provider for the frozen theorem `KAM.Nekhoroshev.averaging_mean`

The proof of `KAM.Nekhoroshev.averaging_mean` is assembled here as
`KAM.Provider.Nekhoroshev.averaging_mean`, from graph predecessors and approved external inputs
only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace KAM.Provider.Nekhoroshev

open KAM.Nekhoroshev

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
  by
  have d : AveragingData n R s h f := ⟨by omega, hR, hs, hh, hf, hrank⟩
  obtain ⟨A, hA, hcore⟩ := averaging_mean_core d K hK hKI
  exact ⟨A, 1, hA, one_pos, fun ε hε hε1 Φ hΦ => hcore ε hε hε1 Φ hΦ⟩

end KAM.Provider.Nekhoroshev

end
