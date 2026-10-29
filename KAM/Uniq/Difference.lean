/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Uniq.Frame
public import KAM.Uniq.Phase
import KAM.Apost.Hamiltonian
import KAM.Apost.Periodicity
import KAM.Matrix.Calculus
import KAM.Strip.Taylor
import Mathlib.Tactic.Linarith

/-!
# The difference of two invariant tori in the frame of `K₁` (blueprint `bp:p3:difference-equation`)

Blueprint Part 3, Lemma `bp:p3:difference-equation`. For a real phase `ψ` put
`Δ(θ) = K₂(θ + ψ) - K₁(θ)` (`KAM.Uniq.diffMap`, defined in `KAM/Uniq/Phase.lean`, which
`bp:p3:phase` also uses), and on `T_ρ`
`R = X_h(K₁ + Δ) - X_h(K₁) - DX_h(K₁) Δ` (`KAM.Uniq.remainder`),
`ξ = P⁻¹ Δ` (`KAM.Uniq.diffXi`) and `q = P⁻¹ R` (`KAM.Uniq.diffQ`). Under (S1) to (S4) and
`‖Δ‖ < μ` on `T_ρ` (the pointwise form of the blueprint's `‖Δ‖_ρ < μ`),
`KAM.Uniq.difference_equation` states:

* (a) `Δ`, `ξ`, `q` are holomorphic on `T_ρ`; `Δ`, `ξ` are `1`-periodic; `Δ = P ξ`; and the four
  components of `ξ` and `q` are `B Lᵀ Δ`, `-Lᵀ Ω₀ Δ`, `B Lᵀ R`, `-Lᵀ Ω₀ R`;
* (b) `∂_ω ξᴸ = T ξᴺ + qᴸ` and `∂_ω ξᴺ = qᴺ`;
* (c) `|ξ| ≤ C_P |Δ|`, `|Δ| ≤ C_P |ξ|` and `|q| ≤ ½ C_P M |Δ|²`.

The proof follows the four steps of the blueprint, each one declaration in `KAM.Uniq.DiffAux`;
the helper lemmas that do not use the particular form of `Δ` are stated for an arbitrary map `Δ`.

* `step_regularity` (`step:p3:diff-regularity`): `Δ`, `ξ`, `q` holomorphic, `Δ`, `ξ` periodic,
  `Δ = P ξ`. Helpers: `differentiableOn_diffMap`, `differentiableOn_remainder`,
  `differentiableOn_diffXi`, `differentiableOn_diffQ`, `periodic_diffMap`, `periodic_diffXi`,
  `sumVec_eq_mulVec_diffXi`. The point `K₁ + Δ = K₂(· + ψ)` lies in `𝔅` by (S4).
* `step_linearized` (`step:p3:diff-linearized`): `∂_ω Δ = DX_h(K₁) Δ + R`, from the invariance
  equations of `K₁` and `K₂` and `D (K₂(· + ψ)) = DK₂(· + ψ)`.
* `step_triangular` (`step:p3:diff-triangular`): `∂_ω ξ = Λ ξ + q`. The algebraic core is
  `fderiv_diffXi_eq`: the product rule for `Δ = P ξ` (`KAM.fderiv_matrix_mulVec_apply`) and the
  reduction `A P - ∂_ω P = P Λ` of `bp:p3:reducibility`.
* `step_bounds` (`step:p3:diff-bounds`): `norm_remainder_le` is `bp:p1:taylor`
  (`KAM.taylor_iteratedFDeriv`, with the factor `½`) for `X_h` on the open set `𝔅`, with `A = M`;
  the segment from `K₁(θ)` to `K₂(θ + ψ)` lies in the ball of radius `μ` around `K₁(θ)`, which lies
  in `𝔅` by (S3). The matrix bounds are `bp:p3:matrix-norms` (`|P|`, `|P⁻¹| ≤ C_P`).

`KAM.holomorphic_inverse_differentiableOn` applies directly to the `Fin n ⊕ Fin n` frame indices.
The helper `differentiableOn_inv_of_isUnit_det` retains the unit-determinant interface and
delegates to that general finite-index theorem.

The definitions `diffMap`, `remainder`, `diffXi` and `diffQ` are total functions, as required by
the totality convention (`diffMap` lives in `KAM/Uniq/Phase.lean`, copied verbatim from Appendix A
there), so no hypothesis of the lemma is the conclusion of another result.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Uniq

open KAM.Torus

variable {n : ℕ} {τ ρ M σK σB σT μ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}
  {K₁ K₂ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- `R = X_h(K₁ + Δ) - X_h(K₁) - DX_h(K₁) Δ`. -/
def remainder (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K₁ Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  hamiltonianVectorFieldℂ h (K₁ θ + Δ θ) - hamiltonianVectorFieldℂ h (K₁ θ) -
    fderiv ℂ (hamiltonianVectorFieldℂ h) (K₁ θ) (Δ θ)

/-- `ξ = P⁻¹ Δ`. -/
def diffXi (K₁ Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    Fin n ⊕ Fin n → ℂ :=
  (frameMat K₁ θ)⁻¹ *ᵥ sumVec n (Δ θ)

/-- `q = P⁻¹ R`. -/
def diffQ (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K₁ Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (θ : Fin n → ℂ) : Fin n ⊕ Fin n → ℂ :=
  (frameMat K₁ θ)⁻¹ *ᵥ sumVec n (remainder h K₁ Δ θ)

namespace DiffAux

/-! ### Regularity of `Δ`, `R`, `ξ` and `q` (`step:p3:diff-regularity`) -/

section Regularity

/-- For a real shift `ψ`, `T_ρ + ψ = T_ρ`. -/
theorem add_real_mem {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) (ψ : Fin n → ℝ) :
    θ + (fun i => (ψ i : ℂ)) ∈ complexStrip n ρ := by
  intro i
  simpa using hθ i

/-- The point `K₁(θ) + Δ(θ)` is `K₂(θ + ψ)`. -/
theorem add_diffMap (K₁ K₂ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ψ : Fin n → ℝ)
    (θ : Fin n → ℂ) : K₁ θ + diffMap K₁ K₂ ψ θ = K₂ (θ + fun i => (ψ i : ℂ)) := by
  rw [diffMap]
  abel

/-- `Δ` is holomorphic on `T_ρ`, since `T_ρ + ψ = T_ρ`. -/
theorem differentiableOn_diffMap (h3 : S3 ρ σK σB σT μ 𝔅 h ω K₁) (h4 : S4 ρ 𝔅 h ω K₂)
    (ψ : Fin n → ℝ) : DifferentiableOn ℂ (diffMap K₁ K₂ ψ) (complexStrip n ρ) := by
  have hshift : DifferentiableOn ℂ (fun θ : Fin n → ℂ => θ + fun i => (ψ i : ℂ))
      (complexStrip n ρ) := differentiableOn_id.add_const _
  exact (h4.holo.comp hshift (fun θ hθ => add_real_mem hθ ψ)).sub h3.holo

/-- `Δ` is `1`-periodic on `T_ρ`, since `K₁` and `K₂` are primary. -/
theorem periodic_diffMap (hp₁ : IsPrimaryOnStrip K₁ ρ) (hp₂ : IsPrimaryOnStrip K₂ ρ)
    (ψ : Fin n → ℝ) : IsPeriodicOn (diffMap K₁ K₂ ψ) ρ := by
  intro i z hz
  have hz' := add_real_mem hz ψ
  have hcomm : z + Pi.single i 1 + (fun j => (ψ j : ℂ)) =
      z + (fun j => (ψ j : ℂ)) + Pi.single i 1 := by abel
  simp only [diffMap]
  rw [hcomm, primary_coordinatewise hp₂ i hz', primary_coordinatewise hp₁ i hz]
  abel

/-- Holomorphy of the second-order remainder of a holomorphic map `X` along `K` and `K + Δ`,
both with values in the open set `𝔅` where `X` and `DX` are holomorphic. -/
theorem differentiableOn_remainder_aux {S : Set (Fin n → ℂ)}
    {X : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hX : DifferentiableOn ℂ X 𝔅) (hDX : DifferentiableOn ℂ (fderiv ℂ X) 𝔅)
    {K Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K S)
    (hΔ : DifferentiableOn ℂ Δ S) (hK𝔅 : ∀ θ ∈ S, K θ ∈ 𝔅) (hKΔ : ∀ θ ∈ S, K θ + Δ θ ∈ 𝔅) :
    DifferentiableOn ℂ (fun θ => X (K θ + Δ θ) - X (K θ) - fderiv ℂ X (K θ) (Δ θ)) S :=
  ((hX.comp (hK.add hΔ) hKΔ).sub (hX.comp hK hK𝔅)).sub
    ((hDX.comp hK hK𝔅).clm_apply hΔ)

/-- `R` is holomorphic on `T_ρ`: the segment point `K₁ + Δ = K₂(· + ψ)` lies in `𝔅` by (S4). -/
theorem differentiableOn_remainder (hX : DifferentiableOn ℂ (hamiltonianVectorFieldℂ h) 𝔅)
    (hDX : DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) 𝔅)
    (hP : Params n τ ρ M σK σB σT μ) (h3 : S3 ρ σK σB σT μ 𝔅 h ω K₁) (h4 : S4 ρ 𝔅 h ω K₂)
    (ψ : Fin n → ℝ) :
    DifferentiableOn ℂ (remainder h K₁ (diffMap K₁ K₂ ψ)) (complexStrip n ρ) :=
  differentiableOn_remainder_aux hX hDX h3.holo (differentiableOn_diffMap h3 h4 ψ)
    (fun θ hθ => FrameAux.mem_of_S3 hP h3 hθ)
    (fun θ hθ => by rw [add_diffMap]; exact h4.mem _ (add_real_mem hθ ψ))

/-- The inverse of a holomorphic matrix map with unit determinant is holomorphic, for any finite
index type. This compatibility wrapper uses the general matrix-inverse theorem. -/
theorem differentiableOn_inv_of_isUnit_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {m : Type*} [Fintype m] [DecidableEq m] {A : E → Matrix m m ℂ} {S : Set E}
    (hA : DifferentiableOn ℂ A S) (hunit : ∀ z ∈ S, IsUnit (A z).det) :
    DifferentiableOn ℂ (fun z => (A z)⁻¹) S := by
  exact (KAM.holomorphic_inverse_differentiableOn hA
    (fun z hz => (hunit z hz).ne_zero)).2

/-- `ξ = P⁻¹ Δ` is holomorphic where `P⁻¹` and `Δ` are. -/
theorem differentiableOn_diffXi {S : Set (Fin n → ℂ)} {Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hFinv : DifferentiableOn ℂ (fun θ => (frameMat K₁ θ)⁻¹) S) (hΔ : DifferentiableOn ℂ Δ S) :
    DifferentiableOn ℂ (diffXi K₁ Δ) S :=
  hFinv.matrix_mulVec ((sumVecIso n).comp_differentiableOn_iff.2 hΔ)

/-- `q = P⁻¹ R` is holomorphic where `P⁻¹` and `R` are. -/
theorem differentiableOn_diffQ {S : Set (Fin n → ℂ)} {Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hFinv : DifferentiableOn ℂ (fun θ => (frameMat K₁ θ)⁻¹) S)
    (hR : DifferentiableOn ℂ (remainder h K₁ Δ) S) : DifferentiableOn ℂ (diffQ h K₁ Δ) S :=
  hFinv.matrix_mulVec ((sumVecIso n).comp_differentiableOn_iff.2 hR)

/-- `ξ` is `1`-periodic on `T_ρ` when `Δ` is, since `P` is. -/
theorem periodic_diffXi (hp₁ : IsPrimaryOnStrip K₁ ρ)
    {Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hΔp : IsPeriodicOn Δ ρ) :
    IsPeriodicOn (diffXi K₁ Δ) ρ := by
  intro i z hz
  simp only [diffXi]
  rw [Apost.periodic_frameMat hp₁ i z hz, hΔp i z hz]

end Regularity

/-! ### The frame algebra at one point -/

section Algebra

variable {Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

theorem inv_mulVec_mulVec {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ}
    (hu : IsUnit A.det) (x : m → ℂ) : A⁻¹ *ᵥ (A *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem mulVec_inv_mulVec {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ}
    (hu : IsUnit A.det) (x : m → ℂ) : A *ᵥ (A⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

/-- `Δ = P ξ` (item (a)). -/
theorem sumVec_eq_mulVec_diffXi (hu : IsUnit (frameMat K₁ θ).det) :
    sumVec n (Δ θ) = frameMat K₁ θ *ᵥ diffXi K₁ Δ θ :=
  (mulVec_inv_mulVec hu _).symm

/-- The tangential component of `P⁻¹ w` is `B Lᵀ w`. -/
theorem frameInv_mulVec_inl
    (hinv : (frameMat K₁ θ)⁻¹ = Matrix.fromRows ((gramMatrix K₁ θ)⁻¹ * (tangentMat K₁ θ)ᵀ)
      (-((tangentMat K₁ θ)ᵀ * omegaZeroMatrix n))) (w : Fin n ⊕ Fin n → ℂ) :
    (fun i => ((frameMat K₁ θ)⁻¹ *ᵥ w) (Sum.inl i)) =
      ((gramMatrix K₁ θ)⁻¹ * (tangentMat K₁ θ)ᵀ) *ᵥ w := by
  rw [hinv, Matrix.fromRows_mulVec]
  rfl

/-- The normal component of `P⁻¹ w` is `-Lᵀ Ω₀ w`. -/
theorem frameInv_mulVec_inr
    (hinv : (frameMat K₁ θ)⁻¹ = Matrix.fromRows ((gramMatrix K₁ θ)⁻¹ * (tangentMat K₁ θ)ᵀ)
      (-((tangentMat K₁ θ)ᵀ * omegaZeroMatrix n))) (w : Fin n ⊕ Fin n → ℂ) :
    (fun i => ((frameMat K₁ θ)⁻¹ *ᵥ w) (Sum.inr i)) =
      -(((tangentMat K₁ θ)ᵀ * omegaZeroMatrix n) *ᵥ w) := by
  rw [hinv, Matrix.fromRows_mulVec, Matrix.neg_mulVec]
  rfl

end Algebra

/-! ### Bounds (`step:p3:diff-bounds`) -/

section Bounds

variable {Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

/-- `|ξ| ≤ C |Δ|` from `|P⁻¹| ≤ C`. -/
theorem norm_diffXi_le {C : ℝ} (hinv : ‖(frameMat K₁ θ)⁻¹‖ ≤ C) :
    ‖diffXi K₁ Δ θ‖ ≤ C * ‖Δ θ‖ := by
  calc ‖diffXi K₁ Δ θ‖ ≤ ‖(frameMat K₁ θ)⁻¹‖ * ‖sumVec n (Δ θ)‖ :=
        Matrix.linfty_opNorm_mulVec _ _
    _ ≤ C * ‖Δ θ‖ := by
        rw [norm_sumVec]
        exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)

/-- `|Δ| ≤ C |ξ|` from `|P| ≤ C`. -/
theorem norm_diffMap_le {C : ℝ} (hu : IsUnit (frameMat K₁ θ).det)
    (hP : ‖frameMat K₁ θ‖ ≤ C) : ‖Δ θ‖ ≤ C * ‖diffXi K₁ Δ θ‖ := by
  calc ‖Δ θ‖ = ‖sumVec n (Δ θ)‖ := (norm_sumVec _).symm
    _ = ‖frameMat K₁ θ *ᵥ diffXi K₁ Δ θ‖ := by rw [sumVec_eq_mulVec_diffXi hu]
    _ ≤ ‖frameMat K₁ θ‖ * ‖diffXi K₁ Δ θ‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ C * ‖diffXi K₁ Δ θ‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)

/-- `|q| ≤ ½ C M |Δ|²` from `|P⁻¹| ≤ C` and `|R| ≤ (M / 2) |Δ|²`. -/
theorem norm_diffQ_le {C : ℝ} (hC : 0 ≤ C) (hinv : ‖(frameMat K₁ θ)⁻¹‖ ≤ C)
    (hR : ‖remainder h K₁ Δ θ‖ ≤ M / 2 * ‖Δ θ‖ ^ 2) :
    ‖diffQ h K₁ Δ θ‖ ≤ 1 / 2 * C * M * ‖Δ θ‖ ^ 2 := by
  calc ‖diffQ h K₁ Δ θ‖ ≤ ‖(frameMat K₁ θ)⁻¹‖ * ‖sumVec n (remainder h K₁ Δ θ)‖ :=
        Matrix.linfty_opNorm_mulVec _ _
    _ ≤ C * (M / 2 * ‖Δ θ‖ ^ 2) := by
        rw [norm_sumVec]
        exact mul_le_mul hinv hR (norm_nonneg _) hC
    _ = 1 / 2 * C * M * ‖Δ θ‖ ^ 2 := by ring

/-- `bp:p1:taylor` for `X_h` on `𝔅` with `A = M`: `|R| ≤ (M / 2) |Δ|²`, whenever the ball of radius
`μ` around `K₁ θ` lies in `𝔅` and `|Δ θ| < μ`. -/
theorem norm_remainder_le (hX : DifferentiableOn ℂ (hamiltonianVectorFieldℂ h) 𝔅)
    (h1 : S1 M 𝔅 h) (hμ : 0 < μ) (hball : Metric.ball (K₁ θ) μ ⊆ 𝔅) (hΔ : ‖Δ θ‖ < μ) :
    ‖remainder h K₁ Δ θ‖ ≤ M / 2 * ‖Δ θ‖ ^ 2 := by
  have hz : K₁ θ + Δ θ ∈ Metric.ball (K₁ θ) μ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hΔ
  have hseg : segment ℝ (K₁ θ) (K₁ θ + Δ θ) ⊆ 𝔅 :=
    ((convex_ball (K₁ θ) μ).segment_subset (Metric.mem_ball_self hμ) hz).trans hball
  exact taylor_iteratedFDeriv h1.isOpen hX (A := M) (fun x hx => (h1.bounds x hx).2.2.2) hseg

end Bounds

/-! ### The linearized equation (`step:p3:diff-linearized`) -/

section Linearized

/-- Blueprint `step:p3:diff-linearized`: `∂_ω Δ = DX_h(K₁) Δ + R` on `T_ρ`, since both tori solve
the invariance equation and `D (K₂(· + ψ)) = DK₂(· + ψ)`. -/
theorem step_linearized (h3 : S3 ρ σK σB σT μ 𝔅 h ω K₁) (h4 : S4 ρ 𝔅 h ω K₂) (ψ : Fin n → ℝ)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ) :
    fderiv ℂ (diffMap K₁ K₂ ψ) θ (fun l => (ω l : ℂ)) =
      fderiv ℂ (hamiltonianVectorFieldℂ h) (K₁ θ) (diffMap K₁ K₂ ψ θ) +
        remainder h K₁ (diffMap K₁ K₂ ψ) θ := by
  have hθ' := add_real_mem hθ ψ
  have hK₁ : DifferentiableAt ℂ K₁ θ :=
    h3.holo.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)
  have hK₂ : DifferentiableAt ℂ (fun y : Fin n → ℂ => K₂ (y + fun i => (ψ i : ℂ))) θ :=
    (differentiableAt_comp_add_right _).2
      (h4.holo.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ'))
  have hD : fderiv ℂ (diffMap K₁ K₂ ψ) θ = fderiv ℂ K₂ (θ + fun i => (ψ i : ℂ)) -
      fderiv ℂ K₁ θ := by
    have : diffMap K₁ K₂ ψ = fun y => K₂ (y + fun i => (ψ i : ℂ)) - K₁ y := rfl
    rw [this, fderiv_fun_sub hK₂ hK₁, fderiv_comp_add_right]
  have e₂ := h4.invariant _ hθ'
  have e₁ := h3.invariant _ hθ
  simp only [invarianceError, sub_eq_zero] at e₁ e₂
  rw [hD, _root_.sub_apply, ← e₁, ← e₂]
  simp only [remainder, add_diffMap]
  abel

end Linearized

/-! ### The triangular system (`step:p3:diff-triangular`) -/

section Triangular

/-- The algebraic core of `step:p3:diff-triangular`
(`KAM.Uniq.DiffAux.step_triangular` supplies its hypotheses). The product rule for `Δ = P ξ`
turns `∂_ω Δ = A Δ + R` and `A P - ∂_ω P = P Λ` into `∂_ω ξ = Λ ξ + q`. The hypotheses are exactly
the outputs of `bp:p3:reducibility` and of `step_linearized`; `Δ` is an arbitrary holomorphic
map. -/
theorem fderiv_diffXi_eq {S : Set (Fin n → ℂ)} (hS : IsOpen S)
    {Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hPd : DifferentiableOn ℂ (frameMat K₁) S)
    (hξd : DifferentiableOn ℂ (diffXi K₁ Δ) S)
    (hunit : ∀ θ ∈ S, IsUnit (frameMat K₁ θ).det)
    (hlin : ∀ θ ∈ S, linMat h K₁ θ * frameMat K₁ θ - fderiv ℂ (frameMat K₁) θ (fun l => (ω l : ℂ))
      = frameMat K₁ θ * triangularMat (torsion h K₁ ω θ))
    (hΔ : ∀ θ ∈ S, fderiv ℂ Δ θ (fun l => (ω l : ℂ)) =
      fderiv ℂ (hamiltonianVectorFieldℂ h) (K₁ θ) (Δ θ) + remainder h K₁ Δ θ)
    {θ : Fin n → ℂ} (hθ : θ ∈ S) :
    fderiv ℂ (diffXi K₁ Δ) θ (fun l => (ω l : ℂ)) =
      triangularMat (torsion h K₁ ω θ) *ᵥ diffXi K₁ Δ θ + diffQ h K₁ Δ θ := by
  set v : Fin n → ℂ := fun l => (ω l : ℂ) with hv
  have hmem : S ∈ 𝓝 θ := hS.mem_nhds hθ
  have hPθ : DifferentiableAt ℂ (frameMat K₁) θ := (hPd θ hθ).differentiableAt hmem
  have hξθ : DifferentiableAt ℂ (diffXi K₁ Δ) θ := (hξd θ hθ).differentiableAt hmem
  -- `sumVec Δ = P ξ` near `θ`
  have hev : (fun y => sumVec n (Δ y)) =ᶠ[𝓝 θ] fun y => frameMat K₁ y *ᵥ diffXi K₁ Δ y := by
    filter_upwards [hmem] with y hy
    exact sumVec_eq_mulVec_diffXi (hunit y hy)
  have e1 : fderiv ℂ (fun y => sumVec n (Δ y)) θ v =
      fderiv ℂ (fun y => frameMat K₁ y *ᵥ diffXi K₁ Δ y) θ v := by rw [hev.fderiv_eq]
  rw [fderiv_sumVec_apply, fderiv_matrix_mulVec_apply hPθ hξθ, hΔ θ hθ, map_add] at e1
  -- the pieces
  have hA : sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ h) (K₁ θ) (Δ θ)) =
      linMat h K₁ θ *ᵥ (frameMat K₁ θ *ᵥ diffXi K₁ Δ θ) := by
    rw [← sumVec_eq_mulVec_diffXi (hunit θ hθ)]
    exact (sqMat_mulVec _ _).symm
  rw [hA] at e1
  set P := frameMat K₁ θ with hPdef
  set ξ := diffXi K₁ Δ θ with hξdef
  set W := fderiv ℂ (diffXi K₁ Δ) θ v with hWdef
  set r := sumVec n (remainder h K₁ Δ θ) with hrdef
  set DP := fderiv ℂ (frameMat K₁) θ v with hDPdef
  have hu := hunit θ hθ
  have hl : linMat h K₁ θ * P - DP = P * triangularMat (torsion h K₁ ω θ) := hlin θ hθ
  -- `P W = P (Λ ξ + P⁻¹ r)`
  have key : P *ᵥ W = P *ᵥ (triangularMat (torsion h K₁ ω θ) *ᵥ ξ + P⁻¹ *ᵥ r) := by
    have h2 : P *ᵥ (triangularMat (torsion h K₁ ω θ) *ᵥ ξ + P⁻¹ *ᵥ r) =
        (linMat h K₁ θ * P - DP) *ᵥ ξ + r := by
      rw [hl, Matrix.mulVec_add, mulVec_inv_mulVec hu, Matrix.mulVec_mulVec]
    rw [h2, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    have e1' : linMat h K₁ θ *ᵥ (P *ᵥ ξ) + r = DP *ᵥ ξ + P *ᵥ W := e1
    have : P *ᵥ W = linMat h K₁ θ *ᵥ (P *ᵥ ξ) + r - DP *ᵥ ξ := by
      rw [e1']
      abel
    rw [this]
    abel
  have hk : P⁻¹ *ᵥ (P *ᵥ W) =
      P⁻¹ *ᵥ (P *ᵥ (triangularMat (torsion h K₁ ω θ) *ᵥ ξ + P⁻¹ *ᵥ r)) := by rw [key]
  rwa [inv_mulVec_mulVec hu, inv_mulVec_mulVec hu] at hk

end Triangular

/-! ### Components -/

section Components

/-- The derivative of the reindexed map `y ↦ (k ↦ ξ y (g k))` is the reindexed derivative. -/
theorem fderiv_reindex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι κ : Type*}
    [Fintype ι] [Fintype κ] {ξ : E → ι → ℂ} {x : E} (hξ : DifferentiableAt ℂ ξ x) (g : κ → ι)
    (v : E) : fderiv ℂ (fun y k => ξ y (g k)) x v = fun k => fderiv ℂ ξ x v (g k) := by
  let L : (ι → ℂ) →L[ℂ] (κ → ℂ) :=
    ContinuousLinearMap.pi (fun k => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) (g k))
  have h1 : HasFDerivAt (fun y k => ξ y (g k)) (L.comp (fderiv ℂ ξ x)) x :=
    L.hasFDerivAt.comp x hξ.hasFDerivAt
  rw [h1.fderiv]
  rfl

/-- `Λ ξ = (T ξᴺ, 0)`. -/
theorem triangularMat_mulVec_inl (T : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n ⊕ Fin n → ℂ) :
    (fun i => (triangularMat T *ᵥ ξ) (Sum.inl i)) = T *ᵥ (fun i => ξ (Sum.inr i)) := by
  rw [triangularMat, Matrix.fromBlocks_mulVec]
  simp [Function.comp_def]

theorem triangularMat_mulVec_inr (T : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n ⊕ Fin n → ℂ) :
    (fun i => (triangularMat T *ᵥ ξ) (Sum.inr i)) = 0 := by
  rw [triangularMat, Matrix.fromBlocks_mulVec]
  ext i
  simp

end Components

/-! ### The four steps of the blueprint, assembled -/

section Steps

/-- Blueprint `step:p3:diff-regularity`: `Δ`, `ξ`, `q` are holomorphic on `T_ρ`, `Δ` and `ξ` are
`1`-periodic, and `Δ = P ξ`. The point `K₁ + Δ = K₂(· + ψ)` lies in `𝔅` by (S4). -/
theorem step_regularity (hP : Params n τ ρ M σK σB σT μ) (h1 : S1 M 𝔅 h) (h2 : S2 τ ω γ)
    (h3 : S3 ρ σK σB σT μ 𝔅 h ω K₁) (h4 : S4 ρ 𝔅 h ω K₂) (ψ : Fin n → ℝ) :
    DifferentiableOn ℂ (diffMap K₁ K₂ ψ) (complexStrip n ρ) ∧
      DifferentiableOn ℂ (diffXi K₁ (diffMap K₁ K₂ ψ)) (complexStrip n ρ) ∧
      DifferentiableOn ℂ (diffQ h K₁ (diffMap K₁ K₂ ψ)) (complexStrip n ρ) ∧
      IsPeriodicOn (diffMap K₁ K₂ ψ) ρ ∧ IsPeriodicOn (diffXi K₁ (diffMap K₁ K₂ ψ)) ρ ∧
      ∀ θ ∈ complexStrip n ρ,
        sumVec n (diffMap K₁ K₂ ψ θ) = frameMat K₁ θ *ᵥ diffXi K₁ (diffMap K₁ K₂ ψ) θ := by
  have hS := standing_of hP h1 h2
  obtain ⟨-, -, hPd, hred⟩ := reducibility hP h1 h2 h3
  have hunit : ∀ θ ∈ complexStrip n ρ, IsUnit (frameMat K₁ θ).det := fun θ hθ => (hred θ hθ).1
  have hFinv : DifferentiableOn ℂ (fun θ => (frameMat K₁ θ)⁻¹) (complexStrip n ρ) :=
    differentiableOn_inv_of_isUnit_det hPd hunit
  have hΔd := differentiableOn_diffMap h3 h4 ψ
  have hRd := differentiableOn_remainder (Apost.differentiableOn_ham hS)
    (Apost.differentiableOn_fderiv_ham hS) hP h3 h4 ψ
  exact ⟨hΔd, differentiableOn_diffXi hFinv hΔd, differentiableOn_diffQ hFinv hRd,
    periodic_diffMap h3.primary h4.primary ψ,
    periodic_diffXi h3.primary (periodic_diffMap h3.primary h4.primary ψ),
    fun θ hθ => sumVec_eq_mulVec_diffXi (hunit θ hθ)⟩

/-- Blueprint `step:p3:diff-triangular`: `∂_ω ξ = Λ ξ + q` on `T_ρ`, from `Δ = P ξ`
(`step_regularity`), `∂_ω Δ = DX_h(K₁) Δ + R` (`step_linearized`) and `A P - ∂_ω P = P Λ`
(`bp:p3:reducibility`). -/
theorem step_triangular (hP : Params n τ ρ M σK σB σT μ) (h1 : S1 M 𝔅 h) (h2 : S2 τ ω γ)
    (h3 : S3 ρ σK σB σT μ 𝔅 h ω K₁) (h4 : S4 ρ 𝔅 h ω K₂) (ψ : Fin n → ℝ) :
    ∀ θ ∈ complexStrip n ρ,
      fderiv ℂ (diffXi K₁ (diffMap K₁ K₂ ψ)) θ (fun l => (ω l : ℂ)) =
        triangularMat (torsion h K₁ ω θ) *ᵥ diffXi K₁ (diffMap K₁ K₂ ψ) θ +
          diffQ h K₁ (diffMap K₁ K₂ ψ) θ := fun θ hθ => by
  obtain ⟨-, -, hPd, hred⟩ := reducibility hP h1 h2 h3
  exact fderiv_diffXi_eq (isOpen_complexStrip n ρ) hPd (step_regularity hP h1 h2 h3 h4 ψ).2.1
    (fun θ hθ => (hred θ hθ).1) (fun θ hθ => (hred θ hθ).2.2.2.2)
    (fun θ hθ => step_linearized h3 h4 ψ hθ) hθ

/-- Blueprint `step:p3:diff-bounds`: `|ξ| ≤ C_P |Δ|`, `|Δ| ≤ C_P |ξ|` and `|q| ≤ ½ C_P M |Δ|²`
at the points of `T_ρ` where `|Δ| < μ`. `|P|, |P⁻¹| ≤ C_P` is `bp:p3:matrix-norms`, and
`|R| ≤ (M / 2) |Δ|²` is `bp:p1:taylor` for `X_h` on `𝔅`. -/
theorem step_bounds (hP : Params n τ ρ M σK σB σT μ) (h1 : S1 M 𝔅 h) (h2 : S2 τ ω γ)
    (h3 : S3 ρ σK σB σT μ 𝔅 h ω K₁) (Δ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (hΔ : ∀ θ ∈ complexStrip n ρ, ‖Δ θ‖ < μ) :
    ∀ θ ∈ complexStrip n ρ,
      ‖diffXi K₁ Δ θ‖ ≤ C_P n σK σB * ‖Δ θ‖ ∧
      ‖Δ θ‖ ≤ C_P n σK σB * ‖diffXi K₁ Δ θ‖ ∧
      ‖diffQ h K₁ Δ θ‖ ≤ 1 / 2 * C_P n σK σB * M * ‖Δ θ‖ ^ 2 := fun θ hθ => by
  have hX := Apost.differentiableOn_ham (standing_of hP h1 h2)
  obtain ⟨-, -, -, hred⟩ := reducibility hP h1 h2 h3
  obtain ⟨-, -, -, -, -, hPn, hQn⟩ := matrix_norms hP h3 θ hθ
  have hinvn : ‖(frameMat K₁ θ)⁻¹‖ ≤ C_P n σK σB := by rw [(hred θ hθ).2.1]; exact hQn
  have hR := norm_remainder_le hX h1 hP.μ_pos (h3.ball_sub θ hθ) (hΔ θ hθ)
  exact ⟨norm_diffXi_le hinvn, norm_diffMap_le (hred θ hθ).1 hPn,
    norm_diffQ_le (C_P_pos hP).le hinvn hR⟩

end Steps

end DiffAux

open DiffAux

/-- Blueprint `bp:p3:difference-equation`, items (a)–(c), with `Δ = diffMap K₁ K₂ ψ`. -/
theorem difference_equation (hP : Params n τ ρ M σK σB σT μ) (h1 : S1 M 𝔅 h) (h2 : S2 τ ω γ)
    (h3 : S3 ρ σK σB σT μ 𝔅 h ω K₁) (h4 : S4 ρ 𝔅 h ω K₂) (ψ : Fin n → ℝ)
    (hΔ : ∀ θ ∈ complexStrip n ρ, ‖diffMap K₁ K₂ ψ θ‖ < μ) :
    (DifferentiableOn ℂ (diffMap K₁ K₂ ψ) (complexStrip n ρ) ∧
      DifferentiableOn ℂ (diffXi K₁ (diffMap K₁ K₂ ψ)) (complexStrip n ρ) ∧
      DifferentiableOn ℂ (diffQ h K₁ (diffMap K₁ K₂ ψ)) (complexStrip n ρ) ∧
      IsPeriodicOn (diffMap K₁ K₂ ψ) ρ ∧ IsPeriodicOn (diffXi K₁ (diffMap K₁ K₂ ψ)) ρ ∧
      ∀ θ ∈ complexStrip n ρ,
        sumVec n (diffMap K₁ K₂ ψ θ) = frameMat K₁ θ *ᵥ diffXi K₁ (diffMap K₁ K₂ ψ) θ ∧
        (fun i => diffXi K₁ (diffMap K₁ K₂ ψ) θ (Sum.inl i)) =
          ((gramMatrix K₁ θ)⁻¹ * (tangentMat K₁ θ)ᵀ) *ᵥ sumVec n (diffMap K₁ K₂ ψ θ) ∧
        (fun i => diffXi K₁ (diffMap K₁ K₂ ψ) θ (Sum.inr i)) =
          -(((tangentMat K₁ θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (diffMap K₁ K₂ ψ θ)) ∧
        (fun i => diffQ h K₁ (diffMap K₁ K₂ ψ) θ (Sum.inl i)) =
          ((gramMatrix K₁ θ)⁻¹ * (tangentMat K₁ θ)ᵀ) *ᵥ
            sumVec n (remainder h K₁ (diffMap K₁ K₂ ψ) θ) ∧
        (fun i => diffQ h K₁ (diffMap K₁ K₂ ψ) θ (Sum.inr i)) =
          -(((tangentMat K₁ θ)ᵀ * omegaZeroMatrix n) *ᵥ
            sumVec n (remainder h K₁ (diffMap K₁ K₂ ψ) θ))) ∧
    (∀ θ ∈ complexStrip n ρ,
      fderiv ℂ (fun θ' i => diffXi K₁ (diffMap K₁ K₂ ψ) θ' (Sum.inl i)) θ
          (fun l => (ω l : ℂ)) =
        torsion h K₁ ω θ *ᵥ (fun i => diffXi K₁ (diffMap K₁ K₂ ψ) θ (Sum.inr i)) +
          (fun i => diffQ h K₁ (diffMap K₁ K₂ ψ) θ (Sum.inl i)) ∧
      fderiv ℂ (fun θ' i => diffXi K₁ (diffMap K₁ K₂ ψ) θ' (Sum.inr i)) θ
          (fun l => (ω l : ℂ)) =
        fun i => diffQ h K₁ (diffMap K₁ K₂ ψ) θ (Sum.inr i)) ∧
    (∀ θ ∈ complexStrip n ρ,
      ‖diffXi K₁ (diffMap K₁ K₂ ψ) θ‖ ≤ C_P n σK σB * ‖diffMap K₁ K₂ ψ θ‖ ∧
      ‖diffMap K₁ K₂ ψ θ‖ ≤ C_P n σK σB * ‖diffXi K₁ (diffMap K₁ K₂ ψ) θ‖ ∧
      ‖diffQ h K₁ (diffMap K₁ K₂ ψ) θ‖ ≤ 1 / 2 * C_P n σK σB * M * ‖diffMap K₁ K₂ ψ θ‖ ^ 2) := by
  obtain ⟨hΔd, hξd, hqd, hΔp, hξp, hPξ⟩ := step_regularity hP h1 h2 h3 h4 ψ
  obtain ⟨-, -, -, hred⟩ := reducibility hP h1 h2 h3
  have hder := step_triangular hP h1 h2 h3 h4 ψ
  refine ⟨⟨hΔd, hξd, hqd, hΔp, hξp, fun θ hθ => ?_⟩, fun θ hθ => ?_,
    step_bounds hP h1 h2 h3 (diffMap K₁ K₂ ψ) hΔ⟩
  · have hinv := (hred θ hθ).2.1
    exact ⟨hPξ θ hθ, frameInv_mulVec_inl hinv _, frameInv_mulVec_inr hinv _,
      frameInv_mulVec_inl hinv _, frameInv_mulVec_inr hinv _⟩
  · have hξθ : DifferentiableAt ℂ (diffXi K₁ (diffMap K₁ K₂ ψ)) θ :=
      (hξd θ hθ).differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)
    have hl := fderiv_reindex (g := Sum.inl) hξθ (fun l => (ω l : ℂ))
    have hr := fderiv_reindex (g := Sum.inr) hξθ (fun l => (ω l : ℂ))
    rw [hder θ hθ] at hl hr
    refine ⟨?_, ?_⟩
    · rw [hl]
      ext i
      have := congrFun (triangularMat_mulVec_inl (torsion h K₁ ω θ)
        (diffXi K₁ (diffMap K₁ K₂ ψ) θ)) i
      simpa using congrArg₂ (· + ·) this (rfl : diffQ h K₁ (diffMap K₁ K₂ ψ) θ (Sum.inl i) = _)
    · rw [hr]
      ext i
      have := congrFun (triangularMat_mulVec_inr (torsion h K₁ ω θ)
        (diffXi K₁ (diffMap K₁ K₂ ψ) θ)) i
      simpa using congrArg₂ (· + ·) this (rfl : diffQ h K₁ (diffMap K₁ K₂ ψ) θ (Sum.inr i) = _)

end KAM.Uniq

end
