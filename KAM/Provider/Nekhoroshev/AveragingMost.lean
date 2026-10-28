/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Averaging.Most

/-!
# Provider for the frozen theorem `KAM.Nekhoroshev.averaging_most`

The proof of `KAM.Nekhoroshev.averaging_most` is assembled here as
`KAM.Provider.Nekhoroshev.averaging_most`, from graph predecessors and approved external inputs
only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace KAM.Provider.Nekhoroshev

open KAM.Nekhoroshev

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
  by
  have d : AveragingData n R s h f := ⟨by omega, hR, hs, hh, hf, hrank⟩
  obtain ⟨A, hA, hcore⟩ := averaging_most_core d K hK hKI
  refine ⟨A, 1, R / 8, hA, one_pos, by linarith, by linarith, fun ε hε hε1 η hη hηR => ?_⟩
  exact hcore ε hε hε1 η hη hηR

end KAM.Provider.Nekhoroshev

end
