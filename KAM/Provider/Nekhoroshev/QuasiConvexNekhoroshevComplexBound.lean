/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Assembly.Headline

/-!
# Provider for the frozen theorem `KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound`

The proof of `KAM.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` is assembled here as
`KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound`, from graph predecessors and
approved external inputs only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined:
no module other than the anchor may import it.
-/

public section

namespace KAM.Provider.Nekhoroshev

open KAM.Nekhoroshev

/-- The frozen telescope, assembled from `choice_props` and `head`. -/
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
                (Set.Icc (-L) L) y → ∀ t ∈ Set.Icc (-L) L, y t = z t) := by
  let p : HeadParams n := ⟨R, s, M, m, Mcomplex, ωmin⟩
  have hp : p.Pos := ⟨hR, hs, hM, hm, hMcomplex, hωmin⟩
  obtain ⟨hC, hT, hc, he, hmar, -⟩ := choice_props hn p hp
  exact ⟨p.C, p.T, p.c, p.eps0, hC, hT, hc, he, hmar,
    fun h f ε => head hn p hp h f ε⟩

end KAM.Provider.Nekhoroshev

end
