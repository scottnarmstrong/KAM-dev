/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Assembly.Existence

/-!
# Part 10 assembly: the headline with the specified constants (`bpN:p10:head`)

`head` combines `existence` (with `hypotheses_check` supplying the analytic ODE data) and
`uniqueness`, for the constants `p.C, p.T, p.c, p.eps0` fixed before `h`, `f`, `ε`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- head with the specified constants, before existentially packaging them. -/
theorem head (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) :
    ∀ (h : (Fin n → ℂ) → ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ε : ℝ),
      IsAnalyticIntegrable p.R p.s h → HasComplexHessianBound p.R p.s h p.Mc →
      (∀ I ∈ actionBall n p.R, p.wmin ≤ ‖KAM.frequencyMap h I‖) →
      IsStrictlyQuasiConvex (realActionDomain n p.R p.s) h p.m →
      HasDerivativeBounds (realActionDomain n p.R p.s) h p.M →
      IsAnalyticPerturbation p.R p.s ε f → 0 < ε → ε ≤ p.eps0 →
      ∀ θ₀ I₀ : Fin n → ℝ, I₀ ∈ actionBall n (p.R / 2) →
        ∃ z : ℝ → (Fin n → ℝ) × (Fin n → ℝ), z 0 = (θ₀, I₀) ∧
          IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R)
            (Icc (-p.tau ε) (p.tau ε)) z ∧
          (∀ t : ℝ, |t| ≤ p.tau ε → ‖(z t).2 - I₀‖ ≤ p.rho ε) ∧
          (∀ (L : ℝ) (y : ℝ → (Fin n → ℝ) × (Fin n → ℝ)), 0 ≤ L → L ≤ p.tau ε →
            y 0 = (θ₀, I₀) → IsSolutionOn (KAM.realHamiltonian h f) (actionBall n p.R)
              (Icc (-L) L) y → ∀ t ∈ Icc (-L) L, y t = z t) := by
  intro h f ε h1 h2 h3 h4 h5 hf hε hε0 θ₀ I₀ hI
  have hh : HeadHyp p h := ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨z, hz0, hz, hzc⟩ := existence hn p hp hh hf hε hε0 θ₀ I₀ hI
  have hd := (hypotheses_check hn p hp hh hf hε hε0).1
  refine ⟨z, hz0, hz, hzc, fun L y hL hLτ hy0 hy t ht => ?_⟩
  exact uniqueness hd hz hL hLτ (hy0.trans hz0.symm) hy ht

end KAM.Nekhoroshev

end
