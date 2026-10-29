/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Adapters
public import KAM.Head.MatrixNorms
import KAM.Head.H1

/-!
# The frame side of the unperturbed torus

Blueprint Part 4, `bp:p4:unperturbed`, items (a), (b), (c) and (g), steps `step:p4:unp-frame`,
`step:p4:unp-normal` and `step:p4:unp-ball` (internal module of
`KAM/Head/Unperturbed.lean`). The torus `K⁰_{I_*}(θ) = (θ, ι I_*)` is affine, so the tangent
frame, the Gram matrix and the normal frame are computed directly from the frozen definitions;
nothing here depends on `h`, `f` or `ε` except the ball inclusion (g).

* `KAM.Head.fderiv_unperturbedTorus`: `DK⁰ = (v ↦ (v, 0))`.
* (a) `KAM.Head.differentiable_unperturbedTorus`, `KAM.Head.isPrimaryOnStrip_unperturbedTorus`,
  `KAM.Head.isRealOnReals_unperturbedTorus`, `KAM.Head.tangentMat_unperturbedTorus`,
  `KAM.Head.norm_fderiv_unperturbedTorus`.
* (b) `KAM.Head.gramMatrix_unperturbedTorus`, `KAM.Head.unperturbed_norm_one`.
* (c) `KAM.Head.normalFrame_unperturbedTorus`, `KAM.Head.normalMat_unperturbedTorus`,
  `KAM.Head.fderiv_normalFrame_unperturbedTorus`.
* (g) `KAM.Head.ball_unperturbedTorus_subset_domainD`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology KAM.Torus

namespace KAM.Head

variable {n : ℕ}

/-! ### Item (a): the derivative and the tangent frame -/

theorem unperturbedTorus_hasFDerivAt (I : Fin n → ℝ) (θ : Fin n → ℂ) :
    HasFDerivAt (unperturbedTorus I) (ContinuousLinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ)) θ :=
  (hasFDerivAt_id θ).prodMk (hasFDerivAt_const (fun i => (I i : ℂ)) θ)

/-- `DK⁰(θ) v = (v, 0)` (step `step:p4:unp-frame`). -/
theorem fderiv_unperturbedTorus (I : Fin n → ℝ) (θ : Fin n → ℂ) :
    fderiv ℂ (unperturbedTorus I) θ = ContinuousLinearMap.inl ℂ (Fin n → ℂ) (Fin n → ℂ) :=
  (unperturbedTorus_hasFDerivAt I θ).fderiv

/-- `K⁰` is holomorphic on all of `ℂⁿ`. -/
theorem differentiable_unperturbedTorus (I : Fin n → ℝ) : Differentiable ℂ (unperturbedTorus I) :=
  fun θ => (unperturbedTorus_hasFDerivAt I θ).differentiableAt

/-- `K⁰(θ + k) = K⁰(θ) + (k, 0)`: `K⁰` is primary on every strip. -/
theorem isPrimaryOnStrip_unperturbedTorus (I : Fin n → ℝ) (ρ : ℝ) :
    IsPrimaryOnStrip (unperturbedTorus I) ρ := fun θ _ k =>
  Prod.ext rfl (by simp [unperturbedTorus])

/-- `K⁰(ι x) = ι (x, I_*)`: `K⁰` is real on reals. -/
theorem isRealOnReals_unperturbedTorus (I : Fin n → ℝ) : IsRealOnReals (unperturbedTorus I) :=
  fun θ => ⟨(θ, I), rfl⟩

/-- `DK⁰(θ) = L⁰` as a `2n × n` matrix. -/
theorem tangentMat_unperturbedTorus (I : Fin n → ℝ) (θ : Fin n → ℂ) :
    tangentMat (unperturbedTorus I) θ = frameL0 n := by
  ext (i | i) j
  · simp [tangentMat_apply, fderiv_unperturbedTorus, frameL0, Matrix.one_apply, Pi.single_apply,
      sumVec_apply]
  · simp [tangentMat_apply, fderiv_unperturbedTorus, frameL0, sumVec_apply]

/-- `‖DK⁰(θ)‖ = 1` (operator norm; `n ≥ 1`). -/
theorem norm_fderiv_unperturbedTorus (hn : 0 < n) (I : Fin n → ℝ) (θ : Fin n → ℂ) :
    ‖fderiv ℂ (unperturbedTorus I) θ‖ = 1 := by
  rw [← norm_colMat]
  exact (congrArg norm (tangentMat_unperturbedTorus I θ)).trans (norm_frameL0 hn)

/-! ### Item (b): the Gram matrix -/

/-- `G_{K⁰} = Id`. -/
theorem gramMatrix_unperturbedTorus (I : Fin n → ℝ) (θ : Fin n → ℂ) :
    gramMatrix (unperturbedTorus I) θ = 1 := by
  ext i j
  simp [gramMatrix, fderiv_unperturbedTorus, dotℂ, Matrix.one_apply, Pi.single_apply, eq_comm]

/-- `‖Id‖ = 1` in the row-sum norm, for `n ≥ 1`. -/
theorem unperturbed_norm_one (hn : 0 < n) : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact norm_one

/-! ### Item (c): the normal frame -/

/-- `N⁰(θ) e_j = (0, e_j)`. -/
theorem normalFrame_unperturbedTorus (I : Fin n → ℝ) (θ : Fin n → ℂ) (j : Fin n) :
    normalFrame (unperturbedTorus I) θ j = (0, Pi.single j 1) := by
  simp only [normalFrame, gramMatrix_unperturbedTorus, inv_one, fderiv_unperturbedTorus]
  ext i <;> simp [omegaZero, Matrix.one_apply,
    Pi.single_apply]

/-- `N⁰ = (0; Id)` as a `2n × n` matrix. -/
theorem normalMat_unperturbedTorus (I : Fin n → ℝ) (θ : Fin n → ℂ) :
    normalMat (unperturbedTorus I) θ = frameN0 n := by
  rw [normalMat, tangentMat_unperturbedTorus, gramMatrix_unperturbedTorus, inv_one,
    Matrix.mul_one, omegaZeroMatrix_mul_frameL0]

/-- `DN⁰(θ) v = 0` in every direction (in particular `v = ω`). -/
theorem fderiv_normalFrame_unperturbedTorus (I : Fin n → ℝ) (θ : Fin n → ℂ) (j : Fin n)
    (v : Fin n → ℂ) : fderiv ℂ (fun θ' => normalFrame (unperturbedTorus I) θ' j) θ v = 0 := by
  simp only [normalFrame_unperturbedTorus, fderiv_fun_const]
  rfl

/-! ### Item (g): the ball around `K⁰` -/

/-- Blueprint `bp:p4:unperturbed` (g): for `θ ∈ T_{s/4}` and `I_* ∈ B`, the open ball of radius
`δ_*` around `K⁰(θ)` lies in `𝔇`. -/
theorem ball_unperturbedTorus_subset_domainD {s₀ r₀ : ℝ} (hr₀ : 0 < r₀) {B : Set (Fin n → ℝ)}
    {I : Fin n → ℝ} (hI : I ∈ B) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (stripWidth s₀ / 4)) :
    Metric.ball (unperturbedTorus I θ) (deltaStar s₀ r₀) ⊆ domainD n s₀ r₀ B := by
  intro w hw
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hw
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨fun i => ?_, ⟨I, hI, ?_⟩⟩
  · have h1 : ‖w.1 i - θ i‖ < deltaStar s₀ r₀ :=
      (norm_le_pi_norm (w.1 - θ) i).trans_lt (by simpa [dist_eq_norm] using hw1)
    have h2 : |(w.1 i).im - (θ i).im| < deltaStar s₀ r₀ := by
      have := Complex.abs_im_le_norm (w.1 i - θ i)
      simpa using this.trans_lt h1
    have h3 := hθ i
    have h4 := deltaStar_le_stripWidth_div s₀ r₀
    have h5 : |(w.1 i).im| ≤ |(θ i).im| + |(w.1 i).im - (θ i).im| := by
      calc |(w.1 i).im| = |(θ i).im + ((w.1 i).im - (θ i).im)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    show |(w.1 i).im| < stripWidth s₀ / 2
    linarith
  · have h1 : dist w.2 (fun i => (I i : ℂ)) < deltaStar s₀ r₀ := hw2
    have h2 := deltaStar_le_div s₀ r₀
    rw [dist_eq_norm] at h1
    linarith

end KAM.Head

end
