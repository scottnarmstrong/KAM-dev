/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Constants
public import KAM.Torus.Basic
public import KAM.Matrix.Norms
public import KAM.Strip.Bridges
public import KAM.Strip.CohomologicalNodes
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Tools for Part 2: matrix norms, averages, the cohomological operator

This file specializes the infrastructure of Part 1 to the form used in Part 2
(blueprint subsection "Tools").

* `KAM.Apost.matrix_facts` (Corollary `bp:p2:matrix`): the matrix norm facts (a)–(d), for every
  finite index type, with `Fin n ⊕ Fin n` for the `2n` of the blueprint. The steps are
  `step:p2:matrix-op` (`KAM.isGreatest_norm_mulVec`, `KAM.norm_entry_le`),
  `step:p2:matrix-transpose` (`KAM.norm_transpose_le_card_mul`, `Matrix.linfty_opNorm_mul`) and
  `step:p2:matrix-blocks` (`KAM.Apost.Tools.norm_fromCols_le_add`, `KAM.norm_fromBlocks_le`,
  `KAM.Apost.Tools.norm_fromBlocks_diagonal`, the `Ω₀` lemmas `omegaZeroMatrix_inv` etc.).
* `KAM.Apost.averages` (Corollary `bp:p2:averages`): (a) integrability, linearity, realness and
  the sup bound of the torus average, for a complex Banach space `W` and, entrywise, for vectors
  and matrices (steps `step:p2:avg-bound`: `Tools.torusAverage_basic`,
  `Tools.torusAverage_vector_apply`, `KAM.torusAverage_matrix_apply`, `Tools.im_integral_eq_zero`);
  (b) a periodic holomorphic function on `T_r` has zero average of `∂_ℓ v` and `∂_ω v` (step
  `step:p2:avg-deriv`: `Tools.torusAverage_fderiv_apply_eq_zero`). The value space `W` is an
  arbitrary complex Banach space, not nec. separable: the scalar case
  `KAM.torusAverage_complex_direction_eq_zero` is lifted by duality.
* `KAM.Apost.cohR` is the vector solution operator `𝓡`, componentwise `KAM.cohSolution`.
* `KAM.Apost.Tools.differentiableOn_fderiv_apply`, `isPeriodicOn_fderiv_apply`: the facts about
  `g := ∂_ω u` (holomorphic, periodic) that the a-priori bound `step:p2:coh-apriori` needs besides
  Part 1's cohomological equation; its zero average is `averages` (b).

## `bp:p2:cohomological`

`KAM.Apost.cohomological` (the properties of `cohR` and the a-priori bound in the operator norm) is
proved from Part 1's `KAM.cohomological` and `KAM.cohomological_operator`,
which use the exact constant `KAM.cohConst`; `c_R = max {1, cohConst n τ}` only enlarges it
(`KAM.Apost.Tools.cohConst_div_le_cR`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Apost

open KAM.Torus

namespace Tools

/-! ### Helper lemmas for `matrix_facts` -/

section MatrixHelpers

variable {m₁ m₂ k₁ k₂ : Type*} [Fintype m₁] [Fintype m₂] [Fintype k₁] [Fintype k₂]

/-- Step `step:p2:matrix-blocks`: the norm of a block row `(A B)`. -/
theorem norm_fromCols_le_add (A : Matrix m₁ k₁ ℂ) (B : Matrix m₁ k₂ ℂ) :
    ‖Matrix.fromCols A B‖ ≤ ‖A‖ + ‖B‖ := by
  refine (norm_le_iff_forall_rowSum (add_nonneg (norm_nonneg A) (norm_nonneg B))).2 fun i => ?_
  rw [Fintype.sum_sum_type]
  simp only [Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]
  exact add_le_add (rowSum_le_norm A i) (rowSum_le_norm B i)

/-- Step `step:p2:matrix-blocks`: a block diagonal matrix has the maximum of the block norms. -/
theorem norm_fromBlocks_diagonal (A : Matrix m₁ k₁ ℂ) (D : Matrix m₂ k₂ ℂ) :
    ‖Matrix.fromBlocks A 0 0 D‖ = max ‖A‖ ‖D‖ := by
  refine le_antisymm ((norm_le_iff_forall_rowSum (le_max_of_le_left (norm_nonneg _))).2 ?_)
    (max_le ?_ ?_)
  · rintro (i | i)
    · rw [Fintype.sum_sum_type]
      simpa using (rowSum_le_norm A i).trans (le_max_left _ _)
    · rw [Fintype.sum_sum_type]
      simpa using (rowSum_le_norm D i).trans (le_max_right _ _)
  · refine (norm_le_iff_forall_rowSum (norm_nonneg _)).2 fun i => ?_
    have := rowSum_le_norm (Matrix.fromBlocks A 0 0 D) (Sum.inl i)
    rw [Fintype.sum_sum_type] at this
    simpa using this
  · refine (norm_le_iff_forall_rowSum (norm_nonneg _)).2 fun i => ?_
    have := rowSum_le_norm (Matrix.fromBlocks A 0 0 D) (Sum.inr i)
    rw [Fintype.sum_sum_type] at this
    simpa using this

end MatrixHelpers

section OmegaHelpers

variable {n : ℕ}

/-- Step `step:p2:matrix-blocks`: `Ω₀ᵀ Ω₀ = I`. -/
theorem omegaZeroMatrix_transpose_mul_self :
    (omegaZeroMatrix n)ᵀ * omegaZeroMatrix n = 1 := by
  rw [omegaZeroMatrix_transpose, Matrix.neg_mul, omegaZeroMatrix_mul_self, neg_neg]

/-- Step `step:p2:matrix-blocks`: `Ω₀⁻¹ = Ω₀ᵀ`. -/
theorem omegaZeroMatrix_inv : (omegaZeroMatrix n)⁻¹ = (omegaZeroMatrix n)ᵀ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [omegaZeroMatrix_transpose, Matrix.mul_neg, omegaZeroMatrix_mul_self, neg_neg]

/-- Step `step:p2:matrix-blocks`: `Ω₀ (U₁; U₂) = (-U₂; U₁)`. -/
theorem omegaZeroMatrix_mul_fromRows {q : Type*} [Fintype q] (U₁ U₂ : Matrix (Fin n) q ℂ) :
    omegaZeroMatrix n * Matrix.fromRows U₁ U₂ = Matrix.fromRows (-U₂) U₁ := by
  ext (i | i) j
  · rw [omegaZeroMatrix_mul_apply_inl]
    simp
  · rw [omegaZeroMatrix_mul_apply_inr]
    simp

end OmegaHelpers

/-! ### Helper lemmas for `averages` -/

section AverageHelpers

/-- The imaginary part of an integral of a function with vanishing imaginary part vanishes. -/
theorem im_integral_eq_zero {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (h : ∀ x, (f x).im = 0) : (∫ x, f x ∂μ).im = 0 := by
  have h1 : ∫ x, f x ∂μ = ∫ x, (((f x).re : ℝ) : ℂ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Complex.ext rfl (by simp [h x]))
  rw [h1, integral_complex_ofReal]
  simp

/-- Step `step:p2:avg-bound`, general part: integrability, linearity and the sup bound of the
torus average, for any complex Banach space `W` (scalars, `ℂ^p`, `ℂ^{p×q}`). -/
theorem torusAverage_basic {n : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace W] (f g : (Fin n → ℝ) → W) (hf : Continuous f) (hg : Continuous g) :
    IntegrableOn f (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) ∧
      torusAverage (f + g) = torusAverage f + torusAverage g ∧
      (∀ c : ℂ, torusAverage (c • f) = c • torusAverage f) ∧
      ∀ A, (∀ x ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1), ‖f x‖ ≤ A) →
        ‖torusAverage f‖ ≤ A :=
  ⟨integrableOn_unitCube_of_continuous hf,
    integral_add (integrableOn_unitCube_of_continuous hf) (integrableOn_unitCube_of_continuous hg),
    fun c => integral_smul c f, fun _ hA => norm_torusAverage_le hA⟩

/-- Step `step:p2:avg-bound`, vector part: the average is the vector of entrywise averages. -/
theorem torusAverage_vector_apply {n p : ℕ} {f : (Fin n → ℝ) → Fin p → ℂ} (hf : Continuous f)
    (i : Fin p) :
    torusAverage f i = ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), f x i := by
  let L : (Fin p → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj i
  exact (L.integral_comp_comm (μ := volume.restrict (Set.pi Set.univ
    fun _ : Fin n => Set.Icc (0 : ℝ) 1)) (φ := f) (integrableOn_unitCube_of_continuous hf)).symm

/-- Step `step:p2:avg-deriv`: a directional derivative of a holomorphic periodic function on a
strip of positive width has zero torus average, for values in any complex Banach space `W`.

The scalar case is `KAM.torusAverage_complex_direction_eq_zero`. For general `W`, apply every
continuous functional `φ`: either the integrand is integrable and `φ` commutes with the integral,
or the integral is `0` by definition. This needs no separability of `W`. -/
theorem torusAverage_fderiv_apply_eq_zero {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [CompleteSpace W] {r : ℝ} (hr : 0 < r) {v : (Fin n → ℂ) → W}
    (hv : DifferentiableOn ℂ v (complexStrip n r)) (hp : IsPeriodicOn v r) (ω : Fin n → ℂ) :
    torusAverage (fun x : Fin n → ℝ => fderiv ℂ v (fun i => (x i : ℂ)) ω) = 0 := by
  by_cases hint : IntegrableOn (fun x : Fin n → ℝ => fderiv ℂ v (fun i => (x i : ℂ)) ω)
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1)
  swap
  · exact integral_undef hint
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun φ => ?_
  have hφv : DifferentiableOn ℂ (fun θ => φ (v θ)) (complexStrip n r) :=
    φ.differentiable.comp_differentiableOn hv
  have hφp : ∀ (i : Fin n) z, z ∈ complexStrip n r →
      (fun θ => φ (v θ)) (z + Pi.single i 1) = (fun θ => φ (v θ)) z := fun i z hz => by
    simp only [hp i z hz]
  have hzero := torusAverage_complex_direction_eq_zero hr hφv hφp ω
  have hcomm := (φ.restrictScalars ℝ).integral_comp_comm hint
  have hder : ∀ x : Fin n → ℝ, fderiv ℂ (fun θ => φ (v θ)) (fun i => (x i : ℂ)) ω =
      φ (fderiv ℂ v (fun i => (x i : ℂ)) ω) := fun x => by
    have hx := ofReal_mem_complexStrip hr x
    have hd : DifferentiableAt ℂ v (fun i => (x i : ℂ)) :=
      hv.differentiableAt ((isOpen_complexStrip n r).mem_nhds hx)
    exact congrArg (fun L => L ω) (φ.hasFDerivAt.comp _ hd.hasFDerivAt).fderiv
  simp only [hder] at hzero
  exact hcomm.symm.trans hzero

end AverageHelpers

/-! ### Prerequisites of the a-priori bound (`step:p2:coh-apriori`)

The function `g := ∂_ω u` is holomorphic and periodic on `T_r` when `u` is, and has zero average
by `KAM.Apost.averages` (b). These facts do not depend on Part 1's cohomological equation. -/

section Derivative

/-- Step `step:p2:coh-apriori` (prerequisite): a directional derivative of a holomorphic function
on a strip is holomorphic there. -/
theorem differentiableOn_fderiv_apply {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] {r : ℝ} {u : (Fin n → ℂ) → W}
    (hu : DifferentiableOn ℂ u (complexStrip n r)) (ω : Fin n → ℂ) :
    DifferentiableOn ℂ (fun θ => fderiv ℂ u θ ω) (complexStrip n r) :=
  (ContinuousLinearMap.apply ℂ W ω).differentiable.comp_differentiableOn
    (holomorphic_regularity (isOpen_complexStrip n r) hu).1

/-- Step `step:p2:coh-apriori` (prerequisite): a directional derivative of a periodic function on
a strip is periodic there. -/
theorem isPeriodicOn_fderiv_apply {n : ℕ} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {r : ℝ} {u : (Fin n → ℂ) → W} (hu : IsPeriodicOn u r) (ω : Fin n → ℂ) :
    IsPeriodicOn (fun θ => fderiv ℂ u θ ω) r := fun i z hz => by
  have hev : (fun w => u (w + Pi.single i 1)) =ᶠ[𝓝 z] u :=
    Filter.eventuallyEq_of_mem ((isOpen_complexStrip n r).mem_nhds hz) fun w hw => hu i w hw
  have h := hev.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp_add_right] at h
  simp only [h]

end Derivative

end Tools

/-! ### `bp:p2:matrix` -/

/-- Blueprint `bp:p2:matrix` (all finite index types; `Fin n ⊕ Fin n` for `2n`). -/
theorem matrix_facts :
    (∀ {m k : Type} [Fintype m] [Fintype k] (A : Matrix m k ℂ),
      (∀ i j, ‖A i j‖ ≤ ‖A‖) ∧
      IsGreatest ((fun v : k → ℂ => ‖A *ᵥ v‖) '' Metric.closedBall 0 1) ‖A‖ ∧
      ‖Aᵀ‖ ≤ Fintype.card m * ‖A‖) ∧
    (∀ {m k l : Type} [Fintype m] [Fintype k] [Fintype l] (A : Matrix m k ℂ) (B : Matrix k l ℂ)
      (v : k → ℂ), ‖A * B‖ ≤ ‖A‖ * ‖B‖ ∧ ‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖) ∧
    (∀ {m₁ m₂ k₁ k₂ : Type} [Fintype m₁] [Fintype m₂] [Fintype k₁] [Fintype k₂]
      (A₁₁ : Matrix m₁ k₁ ℂ) (A₁₂ : Matrix m₁ k₂ ℂ) (A₂₁ : Matrix m₂ k₁ ℂ) (A₂₂ : Matrix m₂ k₂ ℂ),
      ‖Matrix.fromCols A₁₁ A₁₂‖ ≤ ‖A₁₁‖ + ‖A₁₂‖ ∧
      ‖Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂‖ ≤ max (‖A₁₁‖ + ‖A₁₂‖) (‖A₂₁‖ + ‖A₂₂‖) ∧
      ‖Matrix.fromBlocks A₁₁ 0 0 A₂₂‖ = max ‖A₁₁‖ ‖A₂₂‖) ∧
    (∀ n : ℕ, (omegaZeroMatrix n)ᵀ = -omegaZeroMatrix n ∧
      omegaZeroMatrix n * omegaZeroMatrix n = -1 ∧ (omegaZeroMatrix n)ᵀ * omegaZeroMatrix n = 1 ∧
      (omegaZeroMatrix n)⁻¹ = (omegaZeroMatrix n)ᵀ ∧ (0 < n → ‖omegaZeroMatrix n‖ = 1) ∧
      ∀ {q : Type} [Fintype q] (U₁ U₂ : Matrix (Fin n) q ℂ),
        omegaZeroMatrix n * Matrix.fromRows U₁ U₂ = Matrix.fromRows (-U₂) U₁) :=
  ⟨fun A => ⟨norm_entry_le A, isGreatest_norm_mulVec A, norm_transpose_le_card_mul A⟩,
    fun A B v => ⟨Matrix.linfty_opNorm_mul A B, Matrix.linfty_opNorm_mulVec A v⟩,
    fun A₁₁ A₁₂ A₂₁ A₂₂ => ⟨Tools.norm_fromCols_le_add A₁₁ A₁₂,
      norm_fromBlocks_le A₁₁ A₁₂ A₂₁ A₂₂, Tools.norm_fromBlocks_diagonal A₁₁ A₂₂⟩,
    fun _ => ⟨omegaZeroMatrix_transpose, omegaZeroMatrix_mul_self,
      Tools.omegaZeroMatrix_transpose_mul_self, Tools.omegaZeroMatrix_inv, norm_omegaZeroMatrix,
      fun U₁ U₂ => Tools.omegaZeroMatrix_mul_fromRows U₁ U₂⟩⟩

/-! ### `bp:p2:averages` -/

/-- Blueprint `bp:p2:averages`. (a) for `f : ℝⁿ → W`, `W` any complex Banach space (`ℂ`, `ℂ^p`,
`ℂ^{p×q}`), entrywise form and realness for matrices and vectors; (b) for `v` holomorphic and
periodic on `T_r`. -/
theorem averages {n : ℕ} :
    (∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
      (f g : (Fin n → ℝ) → W), Continuous f → Continuous g →
      (∀ (i : Fin n) x, f (x + Pi.single i 1) = f x) →
      IntegrableOn f (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) ∧
      torusAverage (f + g) = torusAverage f + torusAverage g ∧
      (∀ c : ℂ, torusAverage (c • f) = c • torusAverage f) ∧
      ∀ A, (∀ x ∈ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1), ‖f x‖ ≤ A) →
        ‖torusAverage f‖ ≤ A) ∧
    (∀ {p q : ℕ} (f : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ), Continuous f →
      (∀ i j, torusAverage f i j = ∫ x in Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1), f x i j) ∧
      ((∀ x i j, (f x i j).im = 0) → ∀ i j, (torusAverage f i j).im = 0)) ∧
    (∀ {p : ℕ} (f : (Fin n → ℝ) → Fin p → ℂ), Continuous f →
      (∀ i, torusAverage f i = ∫ x in Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1), f x i) ∧
      ((∀ x i, (f x i).im = 0) → ∀ i, (torusAverage f i).im = 0)) ∧
    (∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
      {r : ℝ} (v : (Fin n → ℂ) → W) (ω : Fin n → ℝ), 0 < r →
      DifferentiableOn ℂ v (complexStrip n r) → IsPeriodicOn v r →
      (∀ ℓ : Fin n, avg (fun θ => fderiv ℂ v θ (Pi.single ℓ 1)) = 0) ∧
      avg (fun θ => fderiv ℂ v θ (fun l => (ω l : ℂ))) = 0) :=
  ⟨fun f g hf hg _ => Tools.torusAverage_basic f g hf hg,
    fun f hf => ⟨fun i j => torusAverage_matrix_apply hf i j, fun h i j => by
      rw [torusAverage_matrix_apply hf i j]
      exact Tools.im_integral_eq_zero fun x => h x i j⟩,
    fun f hf => ⟨fun i => Tools.torusAverage_vector_apply hf i, fun h i => by
      rw [Tools.torusAverage_vector_apply hf i]
      exact Tools.im_integral_eq_zero fun x => h x i⟩,
    fun v ω hr hv hp =>
      ⟨fun ℓ => Tools.torusAverage_fderiv_apply_eq_zero hr hv hp (Pi.single ℓ 1),
        Tools.torusAverage_fderiv_apply_eq_zero hr hv hp fun l => (ω l : ℂ)⟩⟩

/-! ### The solution operator `𝓡` -/

/-- The vector solution operator `𝓡 g` of `bp:p2:cohomological`, componentwise `cohSolution`. -/
def cohR {n p : ℕ} (ω : Fin n → ℝ) (g : (Fin n → ℂ) → Fin p → ℂ) : (Fin n → ℂ) → Fin p → ℂ :=
  fun θ i => cohSolution ω (fun θ' => g θ' i) θ

/-! ### The Part 2 corollary `bp:p2:cohomological`

Part 1's `KAM.cohomological` and `KAM.cohomological_operator` are stated with
the exact constant `KAM.cohConst n τ`, in the form `cohConst n τ / (γ δ^{τ+n}) A`. Part 2 uses
the larger `c_R = max {1, cohConst n τ}` and writes the bound as `c_R γ⁻¹ δ^{-κ}` with
`κ = τ + n`. -/

namespace Tools

/-- The bound of Part 1 in the form of Part 2: `cohConst / (γ δ^{τ+n}) H ≤ c_R γ⁻¹ δ^{-κ} H`. -/
theorem cohConst_div_le_cR {n : ℕ} {τ γ δ H : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (hH : 0 ≤ H) :
    cohConst n τ / (γ * δ ^ (τ + n)) * H ≤ cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * H := by
  have e1 : cohConst n τ / (γ * δ ^ (τ + n)) * H =
      cohConst n τ * (γ⁻¹ * (δ ^ (τ + n))⁻¹ * H) := by
    rw [div_eq_mul_inv, mul_inv]
    ring
  have e2 : cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * H = cR n τ * (γ⁻¹ * (δ ^ (τ + n))⁻¹ * H) := by
    rw [kappa, Real.rpow_neg hδ.le]
    ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right cohConst_le_cR (by positivity)

end Tools

/-- The exponent `τ` of a standing datum is nonnegative (`τ ≥ n - 1 ≥ 1`). -/
theorem cohomological_tau_nonneg {n : ℕ} {τ M σK σB σT : ℝ}
    {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {ω : Fin n → ℝ} {γ : ℝ} (hS : Standing n τ M σK σB σT 𝔅 h ω γ) : 0 ≤ τ := by
  have h1 := hS.tau_ge
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hS.two_le
  linarith

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- Blueprint `bp:p2:cohomological`, with `Γ_δ = c_R γ⁻¹ δ^{-κ}`. -/
theorem cohomological (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hδr : δ < r) :
    (∀ {p : ℕ} (g : (Fin n → ℂ) → Fin p → ℂ) (H : ℝ), DifferentiableOn ℂ g (complexStrip n r) →
      IsPeriodicOn g r → (∀ θ ∈ complexStrip n r, ‖g θ‖ ≤ H) → avg g = 0 →
      DifferentiableOn ℂ (cohR ω g) (complexStrip n (r - δ)) ∧ IsPeriodicOn (cohR ω g) (r - δ) ∧
      avg (cohR ω g) = 0 ∧
      (∀ θ ∈ complexStrip n (r - δ), fderiv ℂ (cohR ω g) θ (fun l => (ω l : ℂ)) = g θ) ∧
      (∀ θ ∈ complexStrip n (r - δ), ‖cohR ω g θ‖ ≤ cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * H) ∧
      (IsRealVec g → IsRealVec (cohR ω g)) ∧
      ∀ u : (Fin n → ℂ) → Fin p → ℂ, DifferentiableOn ℂ u (complexStrip n (r - δ)) →
        IsPeriodicOn u (r - δ) → avg u = 0 →
        (∀ θ ∈ complexStrip n (r - δ), fderiv ℂ u θ (fun l => (ω l : ℂ)) = g θ) →
        ∀ θ ∈ complexStrip n (r - δ), u θ = cohR ω g θ) ∧
    (∀ {p q : ℕ} (u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (H : ℝ),
      DifferentiableOn ℂ u (complexStrip n r) → IsPeriodicOn u r → avg u = 0 →
      (∀ θ ∈ complexStrip n r, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) →
      ∀ θ ∈ complexStrip n (r - δ), ‖u θ‖ ≤ cR n τ * γ⁻¹ * δ ^ (-kappa n τ) * H) := by
  obtain ⟨hscalar, hvec⟩ := KAM.cohomological hS.dio hS.gamma_pos (cohomological_tau_nonneg hS)
    hδ hδr
  obtain ⟨-, hop⟩ := KAM.cohomological_operator hS.dio hS.gamma_pos (cohomological_tau_nonneg hS)
    hδ hδr
  refine ⟨fun {p} g H hg hp hH h0 => ?_, fun {p q} u H hu hp h0 hH θ hθ => ?_⟩
  · have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH _ (ofReal_mem_complexStrip hr 0))
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hvec g H hg hp hH h0
    exact ⟨h1, h2, h3, h4,
      fun θ hθ => (h5 θ hθ).trans (Tools.cohConst_div_le_cR hS.gamma_pos hδ hH0), h6, h7⟩
  · have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH _ (ofReal_mem_complexStrip hr 0))
    exact (hop u H hu hp h0 hH θ hθ).trans (Tools.cohConst_div_le_cR hS.gamma_pos hδ hH0)

end KAM.Apost

end
