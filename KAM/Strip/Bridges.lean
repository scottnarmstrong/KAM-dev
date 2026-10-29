/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.HigherCauchy
public import KAM.Strip.Averages
public import KAM.Strip.Fourier
public import KAM.Matrix.Norms
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Positivity

/-!
# Adapters from the existing strip infrastructure to the Part 1 graph nodes

The strip infrastructure proves the Cauchy estimates, the regularity of holomorphic maps and the
averages of periodic functions in forms that predate the blueprint statements. This file states,
for the nodes where the existing declarations do not match the blueprint statement exactly, the
blueprint statement itself and derives it from those declarations.

* `bp:p1:holomorphic-regularity`: `KAM.holomorphic_regularity` (the lemma on `Fin m → ℂ`), built
  from `KAM.holomorphic_regularity_of_finiteDimensional` (any finite-dimensional complex domain),
  which adds to the existing `KAM.differentiableOn_fderiv_of_isOpen` the holomorphy of every `D^j F`
  (`KAM.differentiableOn_iteratedFDeriv_of_differentiableOn`, step `step:p1:hreg-orders`) and the
  symmetry of the second derivative (`KAM.fderiv_apply_comm_of_differentiableOn`, step
  `step:p1:hreg-symmetry`).
* `bp:p1:cauchy-open`: `KAM.cauchy_open`, which collects the existing coordinate, second and third
  derivative bounds into the blueprint statement, for any finite-dimensional complex normed target
  (the existing lemmas ask for `CompleteSpace` and `SecondCountableTopology` of the target).
* `bp:p1:cauchy-strip`: `KAM.cauchy_strip`, with the stated factor `n` in the bound for `D u`.
* `bp:p1:cauchy-corollaries`: `KAM.cauchy_corollaries_transpose` and
  `KAM.cauchy_corollaries_directional`.
* `bp:p1:averages`: `KAM.averages`, for finite-dimensional targets (scalars, vectors, matrices).
* `bp:p1:averages-matrix`: `KAM.averages_matrix`, for the entrywise average of a matrix-valued
  function, as in the blueprint and in the frozen `KAM.torsionAverage`.
* `bp:p1:decay`: `KAM.decay` and `KAM.decay_boundary_radius`, for `u` valued in a complete complex
  normed space `W` (every finite-dimensional one: scalars, vectors, matrices with the operator
  norm), with the `W`-valued coefficient `KAM.torusCoeffW`. The existing
  `KAM.norm_torusCoeff_le_of_lt` is the scalar case; the `W`-valued bound is dimension-free, in the
  norm of `W`, and is derived from the scalar one by duality (Hahn-Banach): the coefficient is
  tested against `φ ∈ W*` with `‖φ‖ ≤ 1`.

Sup norms are expressed pointwise (`∀ θ ∈ complexStrip n ρ, ‖u θ‖ ≤ A`), periodicity coordinatewise
(`u (z + Pi.single i 1) = u z`), as in the existing files.
-/

public noncomputable section

open Metric Set MeasureTheory
open scoped Matrix.Norms.Operator

namespace KAM

/-! ### Derivatives of holomorphic maps (`bp:p1:holomorphic-regularity`) -/

section Regularity

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

/-- Blueprint `step:p1:hreg-orders` (first half). On an open set, every iterated derivative
`D^j F` of a holomorphic map is holomorphic. -/
theorem differentiableOn_iteratedFDeriv_of_differentiableOn {U : Set E} (hU : IsOpen U)
    {F : E → W} (hF : DifferentiableOn ℂ F U) (j : ℕ) :
    DifferentiableOn ℂ (iteratedFDeriv ℂ j F) U := by
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have h := (contDiffOn_infty_of_differentiableOn hU hF).differentiableOn_iteratedFDerivWithin
    (m := j) (by exact_mod_cast ENat.natCast_lt_top j) hU.uniqueDiffOn
  exact h.congr fun x hx => (iteratedFDerivWithin_of_isOpen j hU hx).symm

/-- Blueprint `step:p1:hreg-symmetry`. The mixed second derivative of a holomorphic map is
symmetric: `∂_v ∂_w F = ∂_w ∂_v F` at every point of the open domain. -/
theorem fderiv_apply_comm_of_differentiableOn {U : Set E} (hU : IsOpen U) {F : E → W}
    (hF : DifferentiableOn ℂ F U) {z : E} (hz : z ∈ U) (v w : E) :
    fderiv ℂ (fun x => fderiv ℂ F x w) z v = fderiv ℂ (fun x => fderiv ℂ F x v) z w := by
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have hz' : U ∈ nhds z := hU.mem_nhds hz
  have hD : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (differentiableOn_fderiv_of_isOpen hU hF).differentiableAt hz'
  have hev : ∀ᶠ y in nhds z, HasFDerivAt F (fderiv ℂ F y) y := by
    filter_upwards [hz'] with y hy
    exact (hF.differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hsymm := second_derivative_symmetric_of_eventually hev hD.hasFDerivAt v w
  have happly : ∀ u t : E,
      fderiv ℂ (fun x => fderiv ℂ F x u) z t = fderiv ℂ (fderiv ℂ F) z t u := by
    intro u t
    rw [fderiv_clm_apply hD (differentiableAt_const u)]
    simp
  rw [happly w v, happly v w]
  exact hsymm

open scoped ContDiff in
/-- Blueprint `bp:p1:holomorphic-regularity`, on any finite-dimensional complex domain. For `F`
holomorphic on an open `U`: `D F` is holomorphic, every `D^j F` is holomorphic, `F` is `C^∞`,
`‖D^{j+1} F z‖ = ‖D^j (D F) z‖ = ‖D (D^j F) z‖`, and the second derivative is symmetric. -/
theorem holomorphic_regularity_of_finiteDimensional {U : Set E} (hU : IsOpen U) {F : E → W}
    (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (fderiv ℂ F) U ∧
    (∀ j : ℕ, 1 ≤ j → DifferentiableOn ℂ (iteratedFDeriv ℂ j F) U) ∧
    ContDiffOn ℂ ∞ F U ∧
    (∀ z ∈ U, ∀ j : ℕ,
      ‖iteratedFDeriv ℂ (j + 1) F z‖ = ‖iteratedFDeriv ℂ j (fderiv ℂ F) z‖ ∧
        ‖iteratedFDeriv ℂ j (fderiv ℂ F) z‖ = ‖fderiv ℂ (iteratedFDeriv ℂ j F) z‖) ∧
    (∀ z ∈ U, ∀ v w : E, iteratedFDeriv ℂ 2 F z ![v, w] = iteratedFDeriv ℂ 2 F z ![w, v]) := by
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  refine ⟨differentiableOn_fderiv_of_isOpen hU hF,
    fun j _ => differentiableOn_iteratedFDeriv_of_differentiableOn hU hF j,
    contDiffOn_infty_of_differentiableOn hU hF, fun z _ j => ?_, fun z hz v w => ?_⟩
  · exact ⟨norm_iteratedFDeriv_fderiv.symm, norm_iteratedFDeriv_fderiv.trans
      norm_fderiv_iteratedFDeriv.symm⟩
  · have hD : DifferentiableAt ℂ (fderiv ℂ F) z :=
      (differentiableOn_fderiv_of_isOpen hU hF).differentiableAt (hU.mem_nhds hz)
    have happly : ∀ u t : E,
        fderiv ℂ (fun x => fderiv ℂ F x u) z t = fderiv ℂ (fderiv ℂ F) z t u := by
      intro u t
      rw [fderiv_clm_apply hD (differentiableAt_const u)]
      simp
    have h := fderiv_apply_comm_of_differentiableOn hU hF hz v w
    rw [happly w v, happly v w] at h
    simpa [iteratedFDeriv_two_apply] using h

end Regularity

open scoped ContDiff in
/-- Blueprint `bp:p1:holomorphic-regularity`. Let `U ⊆ ℂ^m` be open and `F : U → W` holomorphic,
with `W` a finite-dimensional complex normed space. Then `D F` is holomorphic, every `D^j F`
(`j ≥ 1`) exists and is holomorphic, `F` is `C^∞`,
`‖D^{j+1} F z‖ = ‖D^j (D F) z‖ = ‖D (D^j F) z‖`, the second derivative is symmetric, and the
mixed partial derivatives commute: `∂_i ∂_j F = ∂_j ∂_i F` on `U`. -/
theorem holomorphic_regularity {m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {U : Set (Fin m → ℂ)} (hU : IsOpen U) {F : (Fin m → ℂ) → W}
    (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (fderiv ℂ F) U ∧
    (∀ j : ℕ, 1 ≤ j → DifferentiableOn ℂ (iteratedFDeriv ℂ j F) U) ∧
    ContDiffOn ℂ ∞ F U ∧
    (∀ z ∈ U, ∀ j : ℕ,
      ‖iteratedFDeriv ℂ (j + 1) F z‖ = ‖iteratedFDeriv ℂ j (fderiv ℂ F) z‖ ∧
        ‖iteratedFDeriv ℂ j (fderiv ℂ F) z‖ = ‖fderiv ℂ (iteratedFDeriv ℂ j F) z‖) ∧
    (∀ z ∈ U, ∀ v w : Fin m → ℂ,
      iteratedFDeriv ℂ 2 F z ![v, w] = iteratedFDeriv ℂ 2 F z ![w, v]) ∧
    (∀ z ∈ U, ∀ i j : Fin m,
      fderiv ℂ (fun x => fderiv ℂ F x (Pi.single j 1)) z (Pi.single i 1) =
        fderiv ℂ (fun x => fderiv ℂ F x (Pi.single i 1)) z (Pi.single j 1)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := holomorphic_regularity_of_finiteDimensional hU hF
  exact ⟨h1, h2, h3, h4, h5, fun z hz i j =>
    fderiv_apply_comm_of_differentiableOn hU hF hz (Pi.single i 1) (Pi.single j 1)⟩

/-! ### Cauchy estimates on open sets (`bp:p1:cauchy-open`) -/

/-- Blueprint `bp:p1:cauchy-open`. Let `f` be holomorphic on an open `U ⊆ ℂ^m` with `‖f‖ ≤ A` on
`U`, and let the closed polydisc (the closed ball for the max norm) of radius `δ > 0` around `z`
lie in `U`. Then `‖∂_ℓ f z‖ ≤ A / δ` and `‖D^j f z‖ ≤ c(m, j) A δ^{-j}` for `j = 1, 2, 3`, with
the constants `c(m, 1) = 1`, `c(m, 2) = 4`, `c(m, 3) = 32` of `step:p1:co-constants`. The target
`W` is any finite-dimensional complex normed space (scalars, vectors, matrices). -/
theorem cauchy_open {m : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {U : Set (Fin m → ℂ)} (hU : IsOpen U) {f : (Fin m → ℂ) → W}
    (hf : DifferentiableOn ℂ f U) {A δ : ℝ} (hδ : 0 < δ) {z : Fin m → ℂ}
    (hz : closedBall z δ ⊆ U) (hA : ∀ w ∈ U, ‖f w‖ ≤ A) :
    (∀ ℓ : Fin m, ‖fderiv ℂ f z (Pi.single ℓ 1)‖ ≤ A / δ) ∧
    ‖iteratedFDeriv ℂ 1 f z‖ ≤ 1 * A / δ ^ 1 ∧
    ‖iteratedFDeriv ℂ 2 f z‖ ≤ 4 * A / δ ^ 2 ∧
    ‖iteratedFDeriv ℂ 3 f z‖ ≤ 32 * A / δ ^ 3 := by
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  have hball : ∀ w ∈ closedBall z δ, ‖f w‖ ≤ A := fun w hw => hA w (hz hw)
  refine ⟨fun ℓ => norm_coordinate_fderiv_le_of_closedBall hU hf hδ hz hA ℓ, ?_,
    norm_iteratedFDeriv_two_le_of_closedBall hU hf hδ hz hball,
    norm_iteratedFDeriv_three_le_of_closedBall hU hf hδ hz hball⟩
  rw [norm_iteratedFDeriv_one, one_mul, pow_one]
  exact norm_fderiv_le_of_closedBall hU hf hδ hz hA

/-! ### Cauchy estimates on strips (`bp:p1:cauchy-strip`, `bp:p1:cauchy-corollaries`) -/

section Strips

variable {n : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Blueprint `bp:p1:cauchy-strip`. Let `u` be holomorphic on `T_ρ` with `‖u‖ ≤ A` there, and
`0 < δ`. Then on `T_{ρ-δ}` every partial derivative satisfies `‖∂_ℓ u‖ ≤ δ⁻¹ A` and the full
derivative satisfies `‖D u‖ ≤ n δ⁻¹ A`. The target is any complex normed space (scalars, vectors
with the max norm, matrices with the operator norm). The hypothesis `δ < ρ` of the blueprint is
not needed. -/
theorem cauchy_strip {ρ δ A : ℝ} {u : (Fin n → ℂ) → W}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hA : ∀ θ ∈ complexStrip n ρ, ‖u θ‖ ≤ A) (hδ : 0 < δ) :
    (∀ (ℓ : Fin n), ∀ θ ∈ complexStrip n (ρ - δ), ‖fderiv ℂ u θ (Pi.single ℓ 1)‖ ≤ δ⁻¹ * A) ∧
    ∀ θ ∈ complexStrip n (ρ - δ), ‖fderiv ℂ u θ‖ ≤ n * δ⁻¹ * A := by
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun θ hθ i =>
    (hθ i).trans (by linarith)
  refine ⟨fun ℓ θ hθ => ?_, fun θ hθ => ?_⟩
  · rw [inv_mul_eq_div]
    exact norm_coordinate_fderiv_le_of_mem_complexStrip hu hA hδ hθ ℓ
  · have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA θ (hsub hθ))
    have hnn : 0 ≤ (n : ℝ) * δ⁻¹ * A := by positivity
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : fderiv ℂ u θ = 0 :=
        ContinuousLinearMap.ext fun v => by
          rw [Subsingleton.elim v 0, map_zero, zero_apply]
      rw [h0, norm_zero]
      exact hnn
    · have h := norm_fderiv_le_of_mem_complexStrip hu hA hδ hθ
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc ‖fderiv ℂ u θ‖ ≤ A / δ := h
        _ = 1 * δ⁻¹ * A := by rw [div_eq_inv_mul, one_mul, mul_comm]
        _ ≤ n * δ⁻¹ * A := by gcongr

/-- Blueprint `bp:p1:cauchy-corollaries`, first estimate. For `f` holomorphic on `T_ρ` with values
in `ℂ^p` and `‖f‖ ≤ A`, the transpose of the Jacobian matrix `(∂_ℓ f_i)_{iℓ}` satisfies
`‖(D f)ᵀ‖ ≤ p δ⁻¹ A` on `T_{ρ-δ}` (row-sum operator norm). -/
theorem cauchy_corollaries_transpose {p : ℕ} {ρ δ A : ℝ} {f : (Fin n → ℂ) → Fin p → ℂ}
    (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ θ ∈ complexStrip n ρ, ‖f θ‖ ≤ A) (hδ : 0 < δ) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖(Matrix.of fun (i : Fin p) (ℓ : Fin n) => fderiv ℂ f θ (Pi.single ℓ 1) i).transpose‖ ≤
        p * δ⁻¹ * A := by
  intro θ hθ
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun θ hθ i =>
    (hθ i).trans (by linarith)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA θ (hsub hθ))
  refine (norm_le_iff_forall_rowSum (by positivity)).2 fun ℓ => ?_
  have hcoord : ‖fderiv ℂ f θ (Pi.single ℓ 1)‖ ≤ δ⁻¹ * A :=
    (cauchy_strip hf hA hδ).1 ℓ θ hθ
  calc ∑ i : Fin p, ‖(Matrix.of fun (i : Fin p) (ℓ : Fin n) =>
          fderiv ℂ f θ (Pi.single ℓ 1) i).transpose ℓ i‖
      = ∑ i : Fin p, ‖fderiv ℂ f θ (Pi.single ℓ 1) i‖ := rfl
    _ ≤ ∑ _i : Fin p, ‖fderiv ℂ f θ (Pi.single ℓ 1)‖ :=
        Finset.sum_le_sum fun i _ => norm_le_pi_norm _ i
    _ = p * ‖fderiv ℂ f θ (Pi.single ℓ 1)‖ := by simp
    _ ≤ p * (δ⁻¹ * A) := by gcongr
    _ = p * δ⁻¹ * A := by ring

/-- Blueprint `bp:p1:cauchy-corollaries`, second estimate. For `f` holomorphic on `T_ρ` with
values in a complex normed space (`ℂ^p`, `ℂ^{p×q}`, …) and `‖f‖ ≤ A`, the derivative along
`ω ∈ ℂ^n` satisfies `‖∂_ω f‖ ≤ |ω|₁ δ⁻¹ A` on `T_{ρ-δ}`, where `|ω|₁ = ∑ ‖ω_ℓ‖`. -/
theorem cauchy_corollaries_directional {ρ δ A : ℝ} {f : (Fin n → ℂ) → W}
    (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ θ ∈ complexStrip n ρ, ‖f θ‖ ≤ A) (hδ : 0 < δ) (ω : Fin n → ℂ) :
    ∀ θ ∈ complexStrip n (ρ - δ), ‖fderiv ℂ f θ ω‖ ≤ (∑ ℓ, ‖ω ℓ‖) * δ⁻¹ * A := by
  intro θ hθ
  have hcoord := (cauchy_strip hf hA hδ).1
  have hexp : fderiv ℂ f θ ω = ∑ ℓ, ω ℓ • fderiv ℂ f θ (Pi.single ℓ 1) := by
    conv_lhs => rw [pi_eq_sum_univ' ω]
    simp [map_sum]
  rw [hexp, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ _ => ?_)
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hcoord ℓ θ hθ) (norm_nonneg _)

/-- Blueprint `bp:p1:cauchy-corollaries`, second estimate for a real frequency. This is
`KAM.cauchy_corollaries_directional` for `ω ∈ ℝ^n`, with the derivative along `ω` written as in the
frozen `KAM.invarianceError`: `‖D f θ (ω : ℂ^n)‖ ≤ (∑ |ω_ℓ|) δ⁻¹ A`. -/
theorem cauchy_corollaries_directional_real {ρ δ A : ℝ} {f : (Fin n → ℂ) → W}
    (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ θ ∈ complexStrip n ρ, ‖f θ‖ ≤ A) (hδ : 0 < δ) (ω : Fin n → ℝ) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖fderiv ℂ f θ (fun i => (ω i : ℂ))‖ ≤ (∑ ℓ, |ω ℓ|) * δ⁻¹ * A := by
  intro θ hθ
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    cauchy_corollaries_directional hf hA hδ (fun i => (ω i : ℂ)) θ hθ

end Strips

/-! ### Averages (`bp:p1:averages`, `bp:p1:averages-matrix`) -/

/-- Blueprint `bp:p1:averages`. Let `v` be holomorphic, `1`-periodic and bounded by `A` on `T_ρ`
(`ρ > 0`), with values in a finite-dimensional complex normed space `W` (scalars, `ℂ^p`,
`ℂ^{p×q}`). Then `⟨∂_ℓ v⟩ = 0`, `⟨D v ω⟩ = 0` for every `ω ∈ ℂ^n`, and `‖⟨v⟩‖ ≤ A`. The averages
are over the real torus `[0,1]^n ⊆ T_ρ`. -/
theorem averages {n : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℂ W] {ρ A : ℝ} (hρ : 0 < ρ)
    {v : (Fin n → ℂ) → W} (hv : DifferentiableOn ℂ v (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → v (z + Pi.single i 1) = v z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖v z‖ ≤ A) :
    (∀ ℓ : Fin n, torusAverage (fun x : Fin n → ℝ =>
        fderiv ℂ v (fun i => (x i : ℂ)) (Pi.single ℓ 1)) = 0) ∧
    (∀ ω : Fin n → ℂ, torusAverage (fun x : Fin n → ℝ =>
        fderiv ℂ v (fun i => (x i : ℂ)) ω) = 0) ∧
    ‖torusAverage (fun x : Fin n → ℝ => v (fun i => (x i : ℂ)))‖ ≤ A := by
  have : ProperSpace W := FiniteDimensional.proper ℂ W
  exact ⟨fun ℓ => torusAverage_complex_coordinate_eq_zero hρ hv ℓ (hp ℓ),
    fun ω => torusAverage_complex_direction_eq_zero hρ hv hp ω,
    norm_torusAverage_le_of_strip_bound hρ hA⟩

/-- Blueprint `bp:p1:averages-matrix` (the entrywise average). The Bochner average of a continuous
matrix-valued function on the torus is the matrix of the entrywise averages. -/
theorem torusAverage_matrix_apply {n p q : ℕ} {M : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ}
    (hM : Continuous M) (i : Fin p) (j : Fin q) :
    torusAverage M i j = ∫ x in Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1), M x i j := by
  let L : Matrix (Fin p) (Fin q) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact (L.integral_comp_comm (μ := volume.restrict (Set.pi Set.univ
    fun _ : Fin n => Icc (0 : ℝ) 1)) (φ := M) (integrableOn_unitCube_of_continuous hM)).symm

/-- Blueprint `bp:p1:averages-matrix`. Let `M : ℝ^n → ℂ^{p×q}` be continuous and `1`-periodic, with
the entrywise average `⟨M⟩_{ij} = ∫_{[0,1]^n} M_{ij}` (the convention of the frozen
`KAM.torsionAverage`). If `‖M‖ ≤ A` on `ℝ^n` for the operator norm, then `‖⟨M⟩‖ ≤ A`; if `M` is
`C^1`, then `⟨∂_ω M⟩ = 0` entrywise for every `ω ∈ ℝ^n`. -/
theorem averages_matrix {n p q : ℕ} {M : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ}
    (hM : Continuous M) (hp : ∀ (i : Fin n) x, M (x + Pi.single i 1) = M x) :
    (∀ A : ℝ, (∀ x, ‖M x‖ ≤ A) →
      ‖(Matrix.of fun i j => ∫ x in Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1), M x i j :
        Matrix (Fin p) (Fin q) ℂ)‖ ≤ A) ∧
    (ContDiff ℝ 1 M → ∀ (ω : Fin n → ℝ) (i : Fin p) (j : Fin q),
      ∫ x in Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1), fderiv ℝ M x ω i j = 0) := by
  refine ⟨fun A hA => ?_, fun hC ω i j => ?_⟩
  · have h : (Matrix.of fun i j =>
        ∫ x in Set.pi Set.univ (fun _ : Fin n => Icc (0 : ℝ) 1), M x i j :
          Matrix (Fin p) (Fin q) ℂ) = torusAverage M :=
      Matrix.ext fun i j => (torusAverage_matrix_apply hM i j).symm
    rw [h]
    exact norm_torusAverage_le fun x _ => hA x
  · have hcont : Continuous fun x => fderiv ℝ M x ω :=
      (hC.continuous_fderiv one_ne_zero).clm_apply continuous_const
    rw [← torusAverage_matrix_apply hcont i j]
    exact congrFun (congrFun (torusAverage_fderiv_eq_zero hC hp ω) i) j

/-! ### Coefficient decay for `W`-valued functions (`bp:p1:decay`) -/

/-- Blueprint `bp:p1:decay` (helper). The restriction to the real torus of a function holomorphic
on a strip of positive width is continuous. -/
private theorem continuous_realRestriction {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {ρ : ℝ} (hρ : 0 < ρ) {u : (Fin n → ℂ) → W}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ)) :
    Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ)) :=
  hu.continuousOn.comp_continuous
    (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
    fun x => ofReal_mem_complexStrip hρ x

/-- Blueprint `bp:p1:decay` (helper). A pointwise strip bound is nonnegative when the strip is
nonempty. -/
private theorem nonneg_of_strip_bound {n : ℕ} {W : Type*} [NormedAddCommGroup W] {ρ A : ℝ}
    (hρ : 0 < ρ) {u : (Fin n → ℂ) → W} (hA : ∀ z ∈ complexStrip n ρ, ‖u z‖ ≤ A) : 0 ≤ A :=
  (norm_nonneg _).trans (hA 0 fun i => by simpa using hρ)

section Decay

variable {n : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
  [IsScalarTower ℝ ℂ W] [CompleteSpace W]

/-- Blueprint `bp:p1:decay` (the coefficient `û_k = ⟨u χ_{-k}⟩`, entrywise for vector and matrix
values). The Fourier coefficient of a `W`-valued function on the real torus, as a `W`-valued torus
average. For `W = ℂ` it is `KAM.torusCoeff`. -/
@[expose] def torusCoeffW (v : (Fin n → ℝ) → W) (k : Fin n → ℤ) : W :=
  torusAverage fun x => character (-k) (fun j => (x j : ℂ)) • v x

/-- Blueprint `bp:p1:decay` (the coefficient for `W = ℂ`): `KAM.torusCoeffW` is `KAM.torusCoeff`. -/
theorem torusCoeffW_complex (v : (Fin n → ℝ) → ℂ) (k : Fin n → ℤ) :
    torusCoeffW v k = torusCoeff v k := rfl

/-- Blueprint `bp:p1:decay` (duality step). A `W`-valued coefficient bound follows from the scalar
bounds for `φ ∘ u`, `φ ∈ W*`: if `‖φ(û_k)‖ ≤ B ‖φ‖` for every continuous linear `φ : W → ℂ`, then
`‖û_k‖ ≤ B`. The coefficient of `φ ∘ u` is `φ(û_k)` because `φ` commutes with the torus average. -/
theorem norm_torusCoeffW_le_of_dual {v : (Fin n → ℝ) → W} (hv : Continuous v)
    (k : Fin n → ℤ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ φ : W →L[ℂ] ℂ, ‖torusCoeff (fun x => φ (v x)) k‖ ≤ B * ‖φ‖) :
    ‖torusCoeffW v k‖ ≤ B := by
  refine NormedSpace.norm_le_dual_bound ℂ _ hB fun φ => ?_
  have hL : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hchar : Continuous fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character (-k)).continuous.comp hL
  have hint : Integrable (fun x : Fin n → ℝ => character (-k) (fun j => (x j : ℂ)) • v x)
      (volume.restrict (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1)) :=
    integrableOn_unitCube_of_continuous (hchar.smul hv)
  have hcomm := (φ.restrictScalars ℝ).integral_comp_comm hint
  have hφ : φ (torusCoeffW v k) = torusCoeff (fun x => φ (v x)) k := by
    unfold torusCoeffW torusCoeff torusAverage
    simpa [map_smul] using hcomm.symm
  rw [hφ]
  exact h φ

/-- Blueprint `bp:p1:decay`. Let `u` be holomorphic, `1`-periodic and bounded by `A` on `T_ρ`, with
values in a complete complex normed space `W` (every finite-dimensional one: `ℂ`, `ℂ^p`, `ℂ^{p×q}`
with the operator norm). Then for every `k ∈ ℤⁿ` and `0 ≤ ρ' < ρ` the `W`-valued coefficient
`û_k = ⟨u χ_{-k}⟩` satisfies `‖û_k‖ ≤ e^{-2π ρ' |k|₁} A`, in the norm of `W` and with no
dimension factor. -/
theorem decay {ρ ρ' A : ℝ} (hρ' : 0 ≤ ρ') (hρρ' : ρ' < ρ) {u : (Fin n → ℂ) → W}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖u z‖ ≤ A) (k : Fin n → ℤ) :
    ‖torusCoeffW (fun x => u (fun j => (x j : ℂ))) k‖ ≤
      Real.exp (-(2 * Real.pi * ρ' * Fourier.modeSize k)) * A := by
  have hρ : 0 < ρ := hρ'.trans_lt hρρ'
  refine norm_torusCoeffW_le_of_dual (continuous_realRestriction hρ hu) k
    (mul_nonneg (Real.exp_pos _).le (nonneg_of_strip_bound hρ hA)) fun φ => ?_
  have h := norm_torusCoeff_le_of_lt hρ' hρρ'
    (φ.differentiable.comp_differentiableOn hu)
    (fun i z hz => by simp only [Function.comp_apply, hp i z hz])
    (fun z hz => (φ.le_opNorm (u z)).trans
      (mul_le_mul_of_nonneg_left (hA z hz) (norm_nonneg φ))) k
  calc _ ≤ Real.exp (-(2 * Real.pi * ρ' * Fourier.modeSize k)) * (‖φ‖ * A) := h
    _ = _ := by ring

/-- Blueprint `bp:p1:decay#boundary-radius`. For `u` as in `KAM.decay` and `0 < ρ`, the `W`-valued
coefficient satisfies `‖û_k‖ ≤ e^{-2π ρ |k|₁} A` at the full radius. -/
theorem decay_boundary_radius {ρ A : ℝ} (hρ : 0 < ρ) {u : (Fin n → ℂ) → W}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖u z‖ ≤ A) (k : Fin n → ℤ) :
    ‖torusCoeffW (fun x => u (fun j => (x j : ℂ))) k‖ ≤
      Real.exp (-(2 * Real.pi * ρ * Fourier.modeSize k)) * A := by
  refine norm_torusCoeffW_le_of_dual (continuous_realRestriction hρ hu) k
    (mul_nonneg (Real.exp_pos _).le (nonneg_of_strip_bound hρ hA)) fun φ => ?_
  have h := norm_torusCoeff_le hρ (φ.differentiable.comp_differentiableOn hu)
    (fun i z hz => by simp only [Function.comp_apply, hp i z hz])
    (fun z hz => (φ.le_opNorm (u z)).trans
      (mul_le_mul_of_nonneg_left (hA z hz) (norm_nonneg φ))) k
  calc _ ≤ Real.exp (-(2 * Real.pi * ρ * Fourier.modeSize k)) * (‖φ‖ * A) := h
    _ = _ := by ring

end Decay

end KAM

end
