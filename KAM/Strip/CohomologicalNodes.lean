/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalOperator

/-!
# The node-level statements of `bp:p1:cohomological` and `bp:p1:cohomological-operator`

The scalar and vector parts are in `KAM.Strip.Cohomological`; the matrix
parts are in `KAM.Strip.CohomologicalOperator`. This file only assembles them into the two
node-level statements, with the exact constant `KAM.cohConst` and the bound written, as in
`KAM.norm_cohSolution_le`, as `cohConst n τ / (γ * δ ^ (τ + n)) * A`.

* `KAM.cohomological`: for `ω` Diophantine with `γ > 0`, `τ ≥ 0`, `0 < δ < ρ`, and `g` holomorphic,
  `1`-periodic, bounded by `A` on `T_ρ`, with zero average: `𝓡 g` is holomorphic and `1`-periodic
  on `T_{ρ-δ}`, has zero average, solves `∂_ω u = g`, satisfies the bound, is real if `g` is, and is
  the only holomorphic `1`-periodic zero-average solution on `T_{ρ-δ}`, bounded or not. Scalar data
  (`KAM.cohSolution`), and `ℂ^p`-valued data componentwise (`KAM.cohSolutionPi`, definitionally
  `KAM.Apost.cohR`).
* `KAM.cohomological_operator`: the same for `ℂ^{p×q}`-valued data in the operator norm
  (`KAM.cohSolutionMat`), and the a-priori bound for every holomorphic `1`-periodic zero-average `u`
  with `‖∂_ω u‖ ≤ H` on `T_ρ`.

## Map of the Part 1 nodes

* `bp:p1:fourier-basic` (a): `KAM.torusCoeff_fderiv` (holomorphic form, `Strip/Cohomological`)
  and `KAM.torusCoeff_fderiv_coordinate_real`, `KAM.torusCoeff_fderiv_real` (real `C¹` form,
  `Strip/FourierDerivative`). (b), (c): `KAM.hasSum_torusCoeff_mul_character`,
  `KAM.eq_zero_of_torusCoeff_eq_zero`, `KAM.eq_zero_of_torusCoeff_holomorphic`
  (`Strip/FourierBasic`).
* `bp:p1:summation`: `KAM.differentiableOn_fourierSum`, `KAM.fourierSum_add_single`,
  `KAM.torusCoeff_fourierSum`, `KAM.norm_fourierSum_le`, `KAM.summableWeighted_torusCoeff`
  (`Strip/FourierSeries`), `KAM.eq_fourierSum_torusCoeff` (`Strip/FourierBasic`).
* `bp:p1:cohomological`: `KAM.cohomological`; scalar `KAM.differentiableOn_cohSolution`,
  `KAM.torusAverage_cohSolution`, `KAM.fderiv_cohSolution`, `KAM.norm_cohSolution_le`,
  `KAM.eq_cohSolution`, `KAM.cohSolution_im_eq_zero`; vector the `cohSolutionPi` family
  (`Strip/Cohomological`).
* `bp:p1:cohomological-operator`: `KAM.cohomological_operator`; `KAM.cohSolutionMat`,
  `KAM.norm_cohSolutionMat_le`, `KAM.eq_cohSolutionMat`, `KAM.cohomological_apriori_operator`
  (`Strip/CohomologicalOperator`).
-/

public noncomputable section

namespace KAM

open scoped Matrix.Norms.Operator

variable {n : ℕ} {ω : Fin n → ℝ} {γ τ ρ δ : ℝ}

/-- Blueprint `bp:p1:cohomological` (scalar and `ℂ^p`-valued data), with the exact constant
`KAM.cohConst`. -/
theorem cohomological (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδρ : δ < ρ) :
    (∀ (g : (Fin n → ℂ) → ℂ) (A : ℝ), DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      (∀ θ ∈ complexStrip n ρ, ‖g θ‖ ≤ A) →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolution ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolution ω g (z + Pi.single i 1) = cohSolution ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolution ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolution ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        ‖cohSolution ω g θ‖ ≤ cohConst n τ / (γ * δ ^ (τ + n)) * A) ∧
      ((∀ x : Fin n → ℝ, (g fun j => (x j : ℂ)).im = 0) →
        ∀ x : Fin n → ℝ, (cohSolution ω g fun j => (x j : ℂ)).im = 0) ∧
      ∀ u : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ u (complexStrip n (ρ - δ)) →
        (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) → u (z + Pi.single i 1) = u z) →
        torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
        (∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolution ω g θ) ∧
    (∀ {p : ℕ} (g : (Fin n → ℂ) → Fin p → ℂ) (A : ℝ), DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      (∀ θ ∈ complexStrip n ρ, ‖g θ‖ ≤ A) →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolutionPi ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolutionPi ω g (z + Pi.single i 1) = cohSolutionPi ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolutionPi ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolutionPi ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        ‖cohSolutionPi ω g θ‖ ≤ cohConst n τ / (γ * δ ^ (τ + n)) * A) ∧
      ((∀ (x : Fin n → ℝ) (i : Fin p), (g (fun j => (x j : ℂ)) i).im = 0) →
        ∀ (x : Fin n → ℝ) (i : Fin p), (cohSolutionPi ω g (fun j => (x j : ℂ)) i).im = 0) ∧
      ∀ u : (Fin n → ℂ) → Fin p → ℂ, DifferentiableOn ℂ u (complexStrip n (ρ - δ)) →
        (∀ (i : Fin n) z, z ∈ complexStrip n (ρ - δ) → u (z + Pi.single i 1) = u z) →
        torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0 →
        (∀ θ ∈ complexStrip n (ρ - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolutionPi ω g θ) :=
  ⟨fun _ _ hg hp hA h0 =>
    ⟨differentiableOn_cohSolution hω hγ hτ hδ hδρ hg hp hA h0,
      fun i z _ => cohSolution_add_single ω _ z i,
      torusAverage_cohSolution hω hγ hτ hδ hδρ hg hp hA h0,
      fun _ hθ => fderiv_cohSolution hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun _ hθ => norm_cohSolution_le hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun hreal x => cohSolution_im_eq_zero ω hreal x,
      fun _ hu hup hu0 hud _ hθ =>
        eq_cohSolution hω hγ hτ hδ hδρ hg hp hA h0 hu hup hu0 hud hθ⟩,
    fun _ _ hg hp hA h0 =>
    ⟨differentiableOn_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0,
      fun i z _ => cohSolutionPi_add_single ω _ z i,
      torusAverage_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0,
      fun _ hθ => fderiv_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun _ hθ => norm_cohSolutionPi_le hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun hreal x l => cohSolutionPi_im_eq_zero ω hreal x l,
      fun _ hu hup hu0 hud _ hθ =>
        eq_cohSolutionPi hω hγ hτ hδ hδρ hg hp hA h0 hu hup hu0 hud hθ⟩⟩

/-- Blueprint `bp:p1:cohomological-operator`: `bp:p1:cohomological` for `ℂ^{p×q}`-valued data in the
operator norm (entrywise solution `KAM.cohSolutionMat`), together with the a-priori bound for every
holomorphic `1`-periodic zero-average `u`. -/
theorem cohomological_operator (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδρ : δ < ρ) :
    (∀ {p q : ℕ} (g : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (A : ℝ),
      DifferentiableOn ℂ g (complexStrip n ρ) →
      (∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) →
      (∀ θ ∈ complexStrip n ρ, ‖g θ‖ ≤ A) →
      torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 →
      DifferentiableOn ℂ (cohSolutionMat ω g) (complexStrip n (ρ - δ)) ∧
      (∀ (k : Fin n) z, z ∈ complexStrip n (ρ - δ) →
        cohSolutionMat ω g (z + Pi.single k 1) = cohSolutionMat ω g z) ∧
      torusAverage (fun x : Fin n → ℝ => cohSolutionMat ω g fun j => (x j : ℂ)) = 0 ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        fderiv ℂ (cohSolutionMat ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ θ ∈ complexStrip n (ρ - δ),
        ‖cohSolutionMat ω g θ‖ ≤ cohConst n τ / (γ * δ ^ (τ + n)) * A) ∧
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
      (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) →
      ∀ θ ∈ complexStrip n (ρ - δ), ‖u θ‖ ≤ cohConst n τ / (γ * δ ^ (τ + n)) * H) :=
  ⟨fun _ _ hg hp hA h0 =>
    ⟨differentiableOn_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0,
      fun k z _ => cohSolutionMat_add_single ω _ z k,
      torusAverage_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0,
      fun _ hθ => fderiv_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun _ hθ => norm_cohSolutionMat_le hω hγ hτ hδ hδρ hg hp hA h0 hθ,
      fun hreal x i j => cohSolutionMat_im_eq_zero ω hreal x i j,
      fun _ hu hup hu0 hud _ hθ =>
        eq_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0 hu hup hu0 hud hθ⟩,
    fun _ _ hu hup hu0 hH =>
      cohomological_apriori_operator hω hγ hτ hδ hδρ hu hup hu0 hH⟩

end KAM

end
