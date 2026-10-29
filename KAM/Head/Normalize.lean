/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Apply
import KAM.Head.Adapters
import KAM.Head.Shift
import KAM.Strip.Averages

/-!
# Properties of the normalized torus `K_ω`

Blueprint Part 4, `bp:p4:normalize`. Under `(SA)`, for `ω ∈ Ω_γ`, the
torus `K_ω = (K^∞_ω)^{[-ph(K^∞_ω)]}` (Definition `bp:p4:normalized-torus`, `KAM.Head.normTorus`) is
holomorphic, primary, real on reals, invariant, normalized, with `B_{μ/2}(K_ω(θ)) ⊆ 𝔇`,
`‖DK_ω‖ ≤ σ_K - μ/2` and `‖W_ω‖ ≤ η₀` on `T_{s/8}`.

The proof is step `step:p4:normalize-proof`. It does not use `applyTorus` beyond the choice
`KAM.Head.apply`: the helper `KAM.Head.isApplyTorus_phaseShift` proves everything for the phase
shift of an arbitrary torus satisfying `KAM.Head.IsApplyTorus`, through the adapter
`KAM.Head.shift_design` of `bp:p4:shift` (a)-(e), and `normalize` is its instance at
`Classical.epsilon_spec` of `KAM.Head.apply`. No further G call occurs.

The last bound is `‖W_ω‖ ≤ ‖K^∞ - K⁰‖ + ‖ph(K^∞)‖ ≤ η₀/2 + η₀/2`, by `shift_design` (e) at the
real points (for `ph`) and at `θ + ι a ∈ T_{s/8}` (for the displacement).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε γ : ℝ} {gc : GConsts}

/-- Everything but the bound on the phase average, for the phase shift of an APPLY torus. -/
theorem isApplyTorus_phaseShift_structure (hs₀ : 0 < s₀) {ω : Fin n → ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsApplyTorus τ s₀ r₀ B h f gc ε γ ω K) :
    DifferentiableOn ℂ (phaseShift K (-phaseAverage K)) (complexStrip n (stripWidth s₀ / 8)) ∧
    IsPrimaryOnStrip (phaseShift K (-phaseAverage K)) (stripWidth s₀ / 8) ∧
    IsRealOnReals (phaseShift K (-phaseAverage K)) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      invarianceError (hbold h f) (phaseShift K (-phaseAverage K)) ω θ = 0) ∧
    IsNormalized (phaseShift K (-phaseAverage K)) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      Metric.ball (phaseShift K (-phaseAverage K) θ) (muParam s₀ r₀ / 2) ⊆
        domainD n s₀ r₀ B) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      ‖fderiv ℂ (phaseShift K (-phaseAverage K)) θ‖ ≤ sigmaK s₀ r₀ - muParam s₀ r₀ / 2) := by
  obtain ⟨hKd, hKp, hKr, hKE, hKball, hKL, -⟩ := hK
  have hρ : 0 < stripWidth s₀ / 8 := by have := stripWidth_pos hs₀; positivity
  obtain ⟨⟨s1, s2, s3, -⟩, s4, s5, s6, -⟩ :=
    shift_design hρ hKd hKp hKr (-phaseAverage K) ω
  exact ⟨s1, s2, s3, (s4 (hbold h f)).2 hKE, s6.2.1, s5.2 _ _ hKball,
    s5.1 _ hKL⟩

/-- The bound `‖W‖ ≤ η₀` for the phase shift of an APPLY torus: `‖ph(K)‖ ≤ η₀/2` and
`‖K - K⁰‖ ≤ η₀/2`. -/
theorem isApplyTorus_phaseShift_disp (hs₀ : 0 < s₀) {ω : Fin n → ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsApplyTorus τ s₀ r₀ B h f gc ε γ ω K) :
    ∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      ‖phaseShift K (-phaseAverage K) θ - unperturbedTorus (invFreq h B ω) θ‖ ≤
        eta0 n τ s₀ r₀ gc ε γ := by
  obtain ⟨hKd, hKp, hKr, hKE, hKball, hKL, hKclose⟩ := hK
  have hρ : 0 < stripWidth s₀ / 8 := by have := stripWidth_pos hs₀; positivity
  obtain ⟨-, -, -, -, s5⟩ := shift_design hρ hKd hKp hKr (-phaseAverage K) ω
  obtain ⟨hph, hdisp⟩ := s5 (invFreq h B ω)
  have hA : ‖phaseAverage K‖ ≤ eta0 n τ s₀ r₀ gc ε γ / 2 :=
    hph _ fun x => hKclose _ (ofReal_mem_complexStrip hρ x)
  intro θ hθ
  refine (hdisp θ).trans ?_
  have := hKclose _ (add_ofReal_mem_complexStrip hθ (-phaseAverage K))
  rw [norm_neg]
  linarith

/-- The properties of `K_ω` for the phase shift of an arbitrary APPLY torus. -/
theorem isApplyTorus_phaseShift (hs₀ : 0 < s₀) {ω : Fin n → ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsApplyTorus τ s₀ r₀ B h f gc ε γ ω K) :
    DifferentiableOn ℂ (phaseShift K (-phaseAverage K)) (complexStrip n (stripWidth s₀ / 8)) ∧
    IsPrimaryOnStrip (phaseShift K (-phaseAverage K)) (stripWidth s₀ / 8) ∧
    IsRealOnReals (phaseShift K (-phaseAverage K)) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      invarianceError (hbold h f) (phaseShift K (-phaseAverage K)) ω θ = 0) ∧
    IsNormalized (phaseShift K (-phaseAverage K)) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      Metric.ball (phaseShift K (-phaseAverage K) θ) (muParam s₀ r₀ / 2) ⊆
        domainD n s₀ r₀ B) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      ‖fderiv ℂ (phaseShift K (-phaseAverage K)) θ‖ ≤ sigmaK s₀ r₀ - muParam s₀ r₀ / 2) ∧
    ∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      ‖phaseShift K (-phaseAverage K) θ - unperturbedTorus (invFreq h B ω) θ‖ ≤
        eta0 n τ s₀ r₀ gc ε γ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := isApplyTorus_phaseShift_structure hs₀ hK
  exact ⟨a1, a2, a3, a4, a5, a6, a7, isApplyTorus_phaseShift_disp hs₀ hK⟩

/-- Blueprint `bp:p4:normalize`. -/
theorem normalize (hD : Data τ s₀ r₀ B h Lh) (hP : Pert s₀ r₀ B f ε)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hSA : SA τ s₀ r₀ B h Lh gc ε γ) {ω : Fin n → ℝ}
    (hω : ω ∈ OmegaGamma h B τ γ) :
    DifferentiableOn ℂ (normTorus τ s₀ r₀ B h f gc ε γ ω) (complexStrip n (stripWidth s₀ / 8)) ∧
    IsPrimaryOnStrip (normTorus τ s₀ r₀ B h f gc ε γ ω) (stripWidth s₀ / 8) ∧
    IsRealOnReals (normTorus τ s₀ r₀ B h f gc ε γ ω) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      invarianceError (hbold h f) (normTorus τ s₀ r₀ B h f gc ε γ ω) ω θ = 0) ∧
    IsNormalized (normTorus τ s₀ r₀ B h f gc ε γ ω) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      Metric.ball (normTorus τ s₀ r₀ B h f gc ε γ ω θ) (muParam s₀ r₀ / 2) ⊆
        domainD n s₀ r₀ B) ∧
    (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      ‖fderiv ℂ (normTorus τ s₀ r₀ B h f gc ε γ ω) θ‖ ≤ sigmaK s₀ r₀ - muParam s₀ r₀ / 2) ∧
    ∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
      ‖normDisp τ s₀ r₀ B h f gc ε γ ω θ‖ ≤ eta0 n τ s₀ r₀ gc ε γ :=
  isApplyTorus_phaseShift hD.s₀_pos
    (Classical.epsilon_spec (apply hD hP hgc hSA hω) :
      IsApplyTorus τ s₀ r₀ B h f gc ε γ ω (applyTorus τ s₀ r₀ B h f gc ε γ ω))

end KAM.Head

end
