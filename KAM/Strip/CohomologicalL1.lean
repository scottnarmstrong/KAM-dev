/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalL1Bound

/-!
# The cohomological estimate in weighted ℓ¹ norms (Wiener algebra), node form

`KAM.cohomological_l1` and `KAM.cohomological_operator_l1` are `KAM.cohomological` and
`KAM.cohomological_operator` (`KAM.Strip.CohomologicalNodes`) with the same standing premises
(`ω` `(γ, τ)`-Diophantine, `γ > 0`, `τ ≥ 0`, `0 < δ < ρ`). The difference is the norm of the data:
instead of `sup_{T_ρ} |g| ≤ A`, the torus coefficients `ĝ` are summable with
`‖ĝ‖_{ℓ¹, 2πρ} = ∑_k |ĝ_k| e^{2πρ|k|₁} ≤ A`.
* **Qualitative clauses.** Holomorphy, periodicity, zero average, the equation, realness and
  uniqueness are those of `KAM.cohomological`, reused through `KAM.norm_le_of_l1`.
* **Bound clauses.** Each bound clause becomes two:
  - the ℓ¹ norm of the solution's coefficients at radius `2π(ρ - δ)` is `≤ Γ_∞(ω, δ) A`;
  - the sup norm on `T_{ρ-δ}` is `≤ Γ_∞(ω, δ) A`;
  with `Γ_∞ = KAM.smallDivisorSup ω δ = sup_{k≠0} e^{-2πδ|k|₁}/(2π|k·ω|)`.
* **Vector data.** The ℓ¹ bound is componentwise, with `0 ≤ A`.
* **Matrix data.** It is the ℓ¹ bound of the components of `g v` for `‖v‖ ≤ 1` (the ℓ¹ analogue of
  the operator norm), with `0 ≤ A`. The a-priori clause is stated the same way for `∂_ω u`.

By `KAM.smallDivisorSup_le_solveBound`, `Γ_∞ ≤ (2πγ)⁻¹ (τ/(2πeδ))^τ`, which has no `δ^{-n}` loss.
By `KAM.smallDivisorSup_le_sqrt_sum`, `Γ_∞ ≤ (2π)⁻¹ S(ω, 2δ)^{1/2}`; this is the SHARP-L2 constant
without its factor `2^{n/2}`, at twice the loss. The two estimates are in different norms: ℓ¹
data are more restrictive than sup data on the same strip.
-/

public noncomputable section

namespace KAM

open scoped Matrix.Norms.Operator

variable {n : ℕ} {ω : Fin n → ℝ} {γ τ ρ δ : ℝ}

/-- `KAM.cohomological` in weighted ℓ¹ norms with the constant `Γ_∞ = KAM.smallDivisorSup ω δ`
(scalar and `ℂ^p`-valued data). -/
theorem cohomological_l1 (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδρ : δ < ρ) :
    (∀ (g : (Fin n → ℂ) → ℂ) (A : ℝ), DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => g fun j => (x j : ℂ)) →
      Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => g fun j => (x j : ℂ)) ≤ A →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolution ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolution ω g (z + Pi.single i 1) = cohSolution ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolution ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolution ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
        (torusCoeff fun x => cohSolution ω g fun j => (x j : ℂ)) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
        (torusCoeff fun x => cohSolution ω g fun j => (x j : ℂ)) ≤ smallDivisorSup ω δ * A ∧
      (∀ θ ∈ complexStrip n (ρ - δ), ‖cohSolution ω g θ‖ ≤ smallDivisorSup ω δ * A) ∧
      ((∀ x : Fin n → ℝ, (g fun j => (x j : ℂ)).im = 0) →
        ∀ x : Fin n → ℝ, (cohSolution ω g fun j => (x j : ℂ)).im = 0) ∧
      ∀ u : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ u (complexStrip n (ρ - δ)) →
        (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) → u (z + Pi.single i 1) = u z) →
        torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
        (∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolution ω g θ) ∧
    (∀ {p : ℕ} (g : (Fin n → ℂ) → Fin p → ℂ) (A : ℝ), DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      0 ≤ A →
      (∀ l : Fin p,
        Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => g (fun j => (x j : ℂ)) l) ∧
          Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => g (fun j => (x j : ℂ)) l)
            ≤ A) →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolutionPi ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolutionPi ω g (z + Pi.single i 1) = cohSolutionPi ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolutionPi ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolutionPi ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ l : Fin p,
        Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
            (torusCoeff fun x => cohSolutionPi ω g (fun j => (x j : ℂ)) l) ∧
          Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
            (torusCoeff fun x => cohSolutionPi ω g (fun j => (x j : ℂ)) l) ≤
              smallDivisorSup ω δ * A) ∧
      (∀ θ ∈ complexStrip n (ρ - δ), ‖cohSolutionPi ω g θ‖ ≤ smallDivisorSup ω δ * A) ∧
      ((∀ (x : Fin n → ℝ) (i : Fin p), (g (fun j => (x j : ℂ)) i).im = 0) →
        ∀ (x : Fin n → ℝ) (i : Fin p), (cohSolutionPi ω g (fun j => (x j : ℂ)) i).im = 0) ∧
      ∀ u : (Fin n → ℂ) → Fin p → ℂ, DifferentiableOn ℂ u (complexStrip n (ρ - δ)) →
        (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) → u (z + Pi.single i 1) = u z) →
        torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
        (∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolutionPi ω g θ) := by
  have hρ : 0 < ρ := hδ.trans hδρ
  refine ⟨fun g A hg hp hs hA h0 => ?_, fun {p} g A hg hp hA0 hs h0 => ?_⟩
  · have hA' := norm_le_of_l1 hρ hg hp hs hA
    obtain ⟨h1, h2⟩ := summableWeighted_cohSolution_l1 hω hγ hτ hδ hδρ hs
    exact ⟨differentiableOn_cohSolution hω hγ hτ hδ hδρ hg hp hA' h0,
      fun i z _ => cohSolution_add_single ω _ z i,
      torusAverage_cohSolution hω hγ hτ hδ hδρ hg hp hA' h0,
      fun _ hθ => fderiv_cohSolution hω hγ hτ hδ hδρ hg hp hA' h0 hθ,
      h1, h2.trans (mul_le_mul_of_nonneg_left hA (smallDivisorSup_nonneg ω δ)),
      fun _ hθ => norm_cohSolution_l1_le hω hγ hτ hδ hδρ hs hA hθ,
      fun hreal x => cohSolution_im_eq_zero ω hreal x,
      fun _ hu hup hu0 hud _ hθ =>
        eq_cohSolution hω hγ hτ hδ hδρ hg hp hA' h0 hu hup hu0 hud hθ⟩
  · have hA' := norm_le_of_l1_pi hρ hg hp hA0 hs
    exact ⟨differentiableOn_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA' h0,
      fun i z _ => cohSolutionPi_add_single ω _ z i,
      torusAverage_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA' h0,
      fun _ hθ => fderiv_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA' h0 hθ,
      summableWeighted_cohSolutionPi_l1 hω hγ hτ hδ hδρ hs,
      fun _ hθ => norm_cohSolutionPi_l1_le hω hγ hτ hδ hδρ hA0 hs hθ,
      fun hreal x l => cohSolutionPi_im_eq_zero ω hreal x l,
      fun _ hu hup hu0 hud _ hθ =>
        eq_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA' h0 hu hup hu0 hud hθ⟩

/-- `KAM.cohomological_operator` in weighted ℓ¹ norms with the constant
`Γ_∞ = KAM.smallDivisorSup ω δ`: matrix-valued data with ℓ¹ bounds on the components of `g v`
(`‖v‖ ≤ 1`), and the a-priori bound with ℓ¹ bounds on the components of `(∂_ω u) v`. -/
theorem cohomological_operator_l1 (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (hδρ : δ < ρ) :
    (∀ {p q : ℕ} (g : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (A : ℝ),
      DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      0 ≤ A →
      (∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
        Fourier.SummableWeighted (2 * Real.pi * ρ)
            (torusCoeff fun x => (g fun j => (x j : ℂ)).mulVec v i) ∧
          Fourier.weightedNorm (2 * Real.pi * ρ)
            (torusCoeff fun x => (g fun j => (x j : ℂ)).mulVec v i) ≤ A) →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolutionMat ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (k : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolutionMat ω g (z + Pi.single k 1) = cohSolutionMat ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolutionMat ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolutionMat ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
        Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
            (torusCoeff fun x => (cohSolutionMat ω g fun j => (x j : ℂ)).mulVec v i) ∧
          Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
            (torusCoeff fun x => (cohSolutionMat ω g fun j => (x j : ℂ)).mulVec v i) ≤
              smallDivisorSup ω δ * A) ∧
      (∀ θ ∈ complexStrip n (ρ - δ), ‖cohSolutionMat ω g θ‖ ≤ smallDivisorSup ω δ * A) ∧
      ((∀ (x : Fin n → ℝ) (i : Fin p) (j : Fin q), (g (fun l => (x l : ℂ)) i j).im = 0) →
        ∀ (x : Fin n → ℝ) (i : Fin p) (j : Fin q),
          (cohSolutionMat ω g (fun l => (x l : ℂ)) i j).im = 0) ∧
      ∀ u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ,
        DifferentiableOn ℂ u (complexStrip n (ρ - δ)) →
        (∀ (k : Fin n) z, z ∈ complexStrip n (ρ - δ) → u (z + Pi.single k 1) = u z) →
        torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
        (∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolutionMat ω g θ) ∧
    (∀ {p q : ℕ} (u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (H : ℝ),
      DifferentiableOn ℂ u (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z) →
      torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
      0 ≤ H →
      (∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
        Fourier.SummableWeighted (2 * Real.pi * ρ)
            (torusCoeff fun x =>
              (fderiv ℂ u (fun j => (x j : ℂ)) (fun l => (ω l : ℂ))).mulVec v i) ∧
          Fourier.weightedNorm (2 * Real.pi * ρ)
            (torusCoeff fun x =>
              (fderiv ℂ u (fun j => (x j : ℂ)) (fun l => (ω l : ℂ))).mulVec v i) ≤ H) →
      (∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
        Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
            (torusCoeff fun x => (u fun j => (x j : ℂ)).mulVec v i) ∧
          Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
            (torusCoeff fun x => (u fun j => (x j : ℂ)).mulVec v i) ≤ smallDivisorSup ω δ * H) ∧
      ∀ θ ∈ complexStrip n (ρ - δ), ‖u θ‖ ≤ smallDivisorSup ω δ * H) := by
  have hρ : 0 < ρ := hδ.trans hδρ
  refine ⟨fun {p q} g A hg hp hA0 hs h0 => ?_, fun {p q} u H hu hup hu0 hH0 hs =>
    cohomological_apriori_operator_l1 hω hγ hτ hδ hδρ hu hup hu0 hH0 hs⟩
  have hA' := norm_le_of_l1_mat hρ hg hp hA0 hs
  exact ⟨differentiableOn_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA' h0,
    fun k z _ => cohSolutionMat_add_single ω _ z k,
    torusAverage_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA' h0,
    fun _ hθ => fderiv_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA' h0 hθ,
    fun _ hv1 i => summableWeighted_cohSolutionMat_l1 hω hγ hτ hδ hδρ hg hp hA0 hs h0 hv1 i,
    fun _ hθ => norm_cohSolutionMat_l1_le hω hγ hτ hδ hδρ hg hp hA0 hs h0 hθ,
    fun hreal x i j => cohSolutionMat_im_eq_zero ω hreal x i j,
    fun _ hu hup hu0 hud _ hθ =>
      eq_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA' h0 hu hup hu0 hud hθ⟩

end KAM

end
