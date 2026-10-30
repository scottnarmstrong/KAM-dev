/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalL1Sup
public import KAM.Strip.CohomologicalOperator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The weighted ℓ¹ cohomological estimate with the constant `Γ_∞`

For data `g` on `T_ρ` whose torus coefficients `ĝ` are summable with the weight `e^{2πρ|k|₁}`, the
solution `𝓡 g = KAM.cohSolution ω g` has coefficients `solve ω ĝ` and

`‖𝓡 g‖_{ℓ¹, 2π(ρ-δ)} ≤ Γ_∞(ω, δ) ‖ĝ‖_{ℓ¹, 2πρ}`,  `sup_{T_{ρ-δ}} |𝓡 g| ≤ Γ_∞(ω, δ) ‖ĝ‖_{ℓ¹, 2πρ}`

with `Γ_∞ = KAM.smallDivisorSup` (`KAM.summableWeighted_cohSolution_l1`,
`KAM.norm_cohSolution_l1_le`). No lattice counting and no factor `2^{n/2}` appear: the ℓ¹ norm is
the strip norm the estimate is closed in. Since `sup_{T_r} |u| ≤ ‖û‖_{ℓ¹, 2πr}`
(`KAM.norm_le_weightedNorm_of_summableWeighted`), the ℓ¹ route also gives a sup-norm estimate, and
ℓ¹ data satisfy the sup-norm premise of the qualitative lemmas of `KAM.Strip.Cohomological`
(`KAM.norm_le_of_l1`), which are reused unchanged.

* Vector data (`KAM.cohSolutionPi`): componentwise ℓ¹ bounds `≤ A`, sup norm the max over
  components.
* Matrix data (`KAM.cohSolutionMat`): ℓ¹ bounds `≤ A` of the components of `g v` for every `‖v‖ ≤ 1`
  (the ℓ¹ analogue of the operator norm), and the operator norm of the solution.
* A-priori forms: `KAM.cohomological_apriori_l1`, `KAM.cohomological_apriori_operator_l1`.
-/

public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM

variable {n : ℕ}

section Scalar

variable {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ} {g : (Fin n → ℂ) → ℂ}

/-- ℓ¹ data are bounded by their ℓ¹ norm on the strip: the sup-norm premise of the qualitative
lemmas. -/
theorem norm_le_of_l1 (hρ : 0 < ρ) (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hs : Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => g fun j => (x j : ℂ)))
    (hA : Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => g fun j => (x j : ℂ)) ≤ A) :
    ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A :=
  fun z hz => (norm_le_weightedNorm_of_summableWeighted hρ hg hp hs z hz).trans hA

variable (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
  (hs : Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => g fun j => (x j : ℂ)))
include hω hγ hτ hδ hδρ hs

/-- The coefficients of `𝓡 g` are `solve ω ĝ`, summable at radius `2π(ρ - δ)` (no holomorphy of
`g` is needed). -/
theorem torusCoeff_cohSolution_l1 :
    Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
        (Diophantine.solve ω (torusCoeff fun x => g fun j => (x j : ℂ))) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
          (Diophantine.solve ω (torusCoeff fun x => g fun j => (x j : ℂ))) ≤
        smallDivisorSup ω δ *
          Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => g fun j => (x j : ℂ)) ∧
      (torusCoeff fun x => cohSolution ω g fun j => (x j : ℂ)) =
        Diophantine.solve ω (torusCoeff fun x => g fun j => (x j : ℂ)) := by
  have hc : Diophantine.Condition ω γ τ := hω.condition
  have hrad : 2 * Real.pi * ρ - 2 * Real.pi * δ = 2 * Real.pi * (ρ - δ) := by ring
  obtain ⟨h1, h2⟩ := summableWeighted_solve_sup hc hγ hτ hδ hs
  rw [hrad] at h1 h2
  refine ⟨h1, h2, funext fun k => ?_⟩
  rw [cohSolution_eq_fourierSum]
  exact torusCoeff_fourierSum (sub_pos.mpr hδρ).le h1 k

/-- **The weighted ℓ¹ cohomological estimate.**
`‖𝓡 g‖_{ℓ¹, 2π(ρ-δ)} ≤ Γ_∞(ω, δ) ‖ĝ‖_{ℓ¹, 2πρ}`. -/
theorem summableWeighted_cohSolution_l1 :
    Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
        (torusCoeff fun x => cohSolution ω g fun j => (x j : ℂ)) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
          (torusCoeff fun x => cohSolution ω g fun j => (x j : ℂ)) ≤
        smallDivisorSup ω δ *
          Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => g fun j => (x j : ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := torusCoeff_cohSolution_l1 hω hγ hτ hδ hδρ hs
  rw [h3]
  exact ⟨h1, h2⟩

/-- The sup-norm consequence: `|𝓡 g| ≤ Γ_∞(ω, δ) A` on `T_{ρ-δ}` when `‖ĝ‖_{ℓ¹, 2πρ} ≤ A`. -/
theorem norm_cohSolution_l1_le
    (hA : Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => g fun j => (x j : ℂ)) ≤ A)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolution ω g θ‖ ≤ smallDivisorSup ω δ * A := by
  obtain ⟨h1, h2, -⟩ := torusCoeff_cohSolution_l1 hω hγ hτ hδ hδρ hs
  rw [cohSolution_eq_fourierSum]
  exact (norm_fourierSum_le h1 hθ).trans
    (h2.trans (mul_le_mul_of_nonneg_left hA (smallDivisorSup_nonneg ω δ)))

end Scalar

section Vector

variable {p : ℕ} {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ} {g : (Fin n → ℂ) → Fin p → ℂ}

/-- Componentwise ℓ¹ data are bounded by `A` on the strip (max norm). -/
theorem norm_le_of_l1_pi (hρ : 0 < ρ) (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) (hA0 : 0 ≤ A)
    (hs : ∀ l : Fin p,
      Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => g (fun j => (x j : ℂ)) l) ∧
        Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => g (fun j => (x j : ℂ)) l) ≤ A) :
    ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A := fun z hz =>
  (pi_norm_le_iff_of_nonneg hA0).mpr fun l =>
    norm_le_of_l1 (g := fun z => g z l) hρ (differentiableOn_pi.mp hg l)
      (fun i z hz => congrFun (hp i z hz) l) (hs l).1 (hs l).2 z hz

variable (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
  (hA0 : 0 ≤ A)
  (hs : ∀ l : Fin p,
    Fourier.SummableWeighted (2 * Real.pi * ρ) (torusCoeff fun x => g (fun j => (x j : ℂ)) l) ∧
      Fourier.weightedNorm (2 * Real.pi * ρ) (torusCoeff fun x => g (fun j => (x j : ℂ)) l) ≤ A)
include hω hγ hτ hδ hδρ hs

/-- The ℓ¹ estimate for vector-valued data, componentwise. -/
theorem summableWeighted_cohSolutionPi_l1 (l : Fin p) :
    Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
        (torusCoeff fun x => cohSolutionPi ω g (fun j => (x j : ℂ)) l) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
          (torusCoeff fun x => cohSolutionPi ω g (fun j => (x j : ℂ)) l) ≤
        smallDivisorSup ω δ * A := by
  obtain ⟨h1, h2⟩ :=
    summableWeighted_cohSolution_l1 (g := fun z => g z l) hω hγ hτ hδ hδρ (hs l).1
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hs l).2 (smallDivisorSup_nonneg ω δ))⟩

include hA0 in
/-- The ℓ¹ estimate for vector-valued data, in the sup (max) norm. -/
theorem norm_cohSolutionPi_l1_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolutionPi ω g θ‖ ≤ smallDivisorSup ω δ * A :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg (smallDivisorSup_nonneg ω δ) hA0)).mpr fun l =>
    norm_cohSolution_l1_le (g := fun z => g z l) hω hγ hτ hδ hδρ (hs l).1 (hs l).2 hθ

end Vector

section MatrixData

variable {p q : ℕ} {ω : Fin n → ℝ} {γ τ ρ δ A : ℝ} {g : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ}

/-- ℓ¹ data in the operator sense (`‖(g v)_i‖_{ℓ¹} ≤ A` for `‖v‖ ≤ 1`) are bounded by `A` in the
operator norm on the strip. -/
theorem norm_le_of_l1_mat (hρ : 0 < ρ) (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z) (hA0 : 0 ≤ A)
    (hs : ∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
      Fourier.SummableWeighted (2 * Real.pi * ρ)
          (torusCoeff fun x => (g fun j => (x j : ℂ)).mulVec v i) ∧
        Fourier.weightedNorm (2 * Real.pi * ρ)
          (torusCoeff fun x => (g fun j => (x j : ℂ)).mulVec v i) ≤ A) :
    ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A := fun z hz => by
  obtain ⟨v, hv, hMv⟩ := (isGreatest_norm_mulVec (g z)).1
  have hv1 : ‖v‖ ≤ 1 := by simpa using hv
  have hMv' : ‖(g z).mulVec v‖ = ‖g z‖ := hMv
  rw [← hMv']
  exact norm_le_of_l1_pi (g := fun z => (g z).mulVec v) hρ
    (mulVec_transfer hρ hg v (0 : Fin n → ℝ)).1
    (fun i z hz => by simp only [hp i z hz]) hA0 (hs v hv1) z hz

/-- `(𝓡 g) v = 𝓡 (g v)` on `T_{ρ-δ}` (uniqueness), under the sup-norm premises. -/
theorem mulVec_cohSolutionMat (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδρ : δ < ρ) (hg : DifferentiableOn ℂ g (complexStrip n ρ))
    (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
    (hA : ∀ z ∈ complexStrip n ρ, ‖g z‖ ≤ A)
    (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0) {v : Fin q → ℂ}
    (hv1 : ‖v‖ ≤ 1) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    (cohSolutionMat ω g θ).mulVec v = cohSolutionPi ω (fun θ => (g θ).mulVec v) θ := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hr : 0 < ρ - δ := sub_pos.mpr hδρ
  obtain ⟨hG, hGavg, -⟩ := mulVec_transfer hρ hg v ω
  have hGp : ∀ (k : Fin n) z, z ∈ complexStrip n ρ →
      (g (z + Pi.single k 1)).mulVec v = (g z).mulVec v := fun k z hz => by rw [hp k z hz]
  have hGA : ∀ z ∈ complexStrip n ρ, ‖(g z).mulVec v‖ ≤ A := fun z hz =>
    (Matrix.linfty_opNorm_mulVec _ v).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hv1).trans (hA z hz))
  have hG0 : torusAverage (fun x : Fin n → ℝ => (g fun j => (x j : ℂ)).mulVec v) = 0 := by
    rw [hGavg, h0, Matrix.zero_mulVec]
  have hU := differentiableOn_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0
  obtain ⟨hw, hwavg, hwd⟩ := mulVec_transfer hr hU v ω
  exact eq_cohSolutionPi hω hγ hτ hδ hδρ hG hGp hGA hG0
    (v := fun θ => (cohSolutionMat ω g θ).mulVec v) hw
    (fun k z _ => by rw [cohSolutionMat_add_single])
    (by rw [hwavg, torusAverage_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0, Matrix.zero_mulVec])
    (fun θ' hθ' => by
      rw [hwd θ' hθ', fderiv_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0 hθ']) hθ

variable (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
  (hg : DifferentiableOn ℂ g (complexStrip n ρ))
  (hp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z)
  (hA0 : 0 ≤ A)
  (hs : ∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
    Fourier.SummableWeighted (2 * Real.pi * ρ)
        (torusCoeff fun x => (g fun j => (x j : ℂ)).mulVec v i) ∧
      Fourier.weightedNorm (2 * Real.pi * ρ)
        (torusCoeff fun x => (g fun j => (x j : ℂ)).mulVec v i) ≤ A)
  (h0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0)
include hω hγ hτ hδ hδρ hg hp hA0 hs h0

/-- The ℓ¹ estimate for matrix-valued data, in the operator sense:
`‖((𝓡 g) v)_i‖_{ℓ¹, 2π(ρ-δ)} ≤ Γ_∞(ω, δ) A` for every `‖v‖ ≤ 1`. -/
theorem summableWeighted_cohSolutionMat_l1 {v : Fin q → ℂ} (hv1 : ‖v‖ ≤ 1) (i : Fin p) :
    Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
        (torusCoeff fun x => (cohSolutionMat ω g fun j => (x j : ℂ)).mulVec v i) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
          (torusCoeff fun x => (cohSolutionMat ω g fun j => (x j : ℂ)).mulVec v i) ≤
        smallDivisorSup ω δ * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hr : 0 < ρ - δ := sub_pos.mpr hδρ
  have hA := norm_le_of_l1_mat hρ hg hp hA0 hs
  have hco : (fun x : Fin n → ℝ => (cohSolutionMat ω g fun j => (x j : ℂ)).mulVec v i) =
      fun x => cohSolutionPi ω (fun θ => (g θ).mulVec v) (fun j => (x j : ℂ)) i := funext fun x =>
    congrFun (mulVec_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0 hv1
      (ofReal_mem_complexStrip hr x)) i
  rw [hco]
  exact summableWeighted_cohSolutionPi_l1 (g := fun θ => (g θ).mulVec v) hω hγ hτ hδ hδρ
    (hs v hv1) i

/-- The ℓ¹ estimate for matrix-valued data, in the operator norm on `T_{ρ-δ}`. -/
theorem norm_cohSolutionMat_l1_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (ρ - δ)) :
    ‖cohSolutionMat ω g θ‖ ≤ smallDivisorSup ω δ * A := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hA := norm_le_of_l1_mat hρ hg hp hA0 hs
  obtain ⟨v, hv, hMv⟩ := (isGreatest_norm_mulVec (cohSolutionMat ω g θ)).1
  have hv1 : ‖v‖ ≤ 1 := by simpa using hv
  have hMv' : ‖(cohSolutionMat ω g θ).mulVec v‖ = ‖cohSolutionMat ω g θ‖ := hMv
  rw [← hMv', mulVec_cohSolutionMat hω hγ hτ hδ hδρ hg hp hA h0 hv1 hθ]
  exact norm_cohSolutionPi_l1_le (g := fun θ => (g θ).mulVec v) hω hγ hτ hδ hδρ hA0
    (hs v hv1) hθ

end MatrixData

section Apriori

variable {ω : Fin n → ℝ} {γ τ ρ δ H : ℝ}
  (hω : IsDiophantine γ τ ω) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδρ : δ < ρ)
include hω hγ hτ hδ hδρ

/-- **A-priori ℓ¹ bound, scalar-valued.** If `u` is holomorphic, `1`-periodic, with zero average
on `T_ρ` and the coefficients of `∂_ω u` have ℓ¹ norm `≤ H` at radius `2πρ`, then
`‖û‖_{ℓ¹, 2π(ρ-δ)} ≤ Γ_∞(ω, δ) H` and `|u| ≤ Γ_∞(ω, δ) H` on `T_{ρ-δ}`. -/
theorem cohomological_apriori_l1 {u : (Fin n → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hu0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0)
    (hs : Fourier.SummableWeighted (2 * Real.pi * ρ)
      (torusCoeff fun x => fderiv ℂ u (fun j => (x j : ℂ)) (fun l => (ω l : ℂ))))
    (hH : Fourier.weightedNorm (2 * Real.pi * ρ)
      (torusCoeff fun x => fderiv ℂ u (fun j => (x j : ℂ)) (fun l => (ω l : ℂ))) ≤ H) :
    (Fourier.SummableWeighted (2 * Real.pi * (ρ - δ)) (torusCoeff fun x => u fun j => (x j : ℂ)) ∧
      Fourier.weightedNorm (2 * Real.pi * (ρ - δ)) (torusCoeff fun x => u fun j => (x j : ℂ)) ≤
        smallDivisorSup ω δ * H) ∧
    ∀ θ ∈ complexStrip n (ρ - δ), ‖u θ‖ ≤ smallDivisorSup ω δ * H := by
  have hρ : 0 < ρ := hδ.trans hδρ
  have hr : 0 < ρ - δ := sub_pos.mpr hδρ
  have hmono : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun z hz j => by
    have := hz j
    linarith
  set g : (Fin n → ℂ) → ℂ := fun θ => fderiv ℂ u θ (fun l => (ω l : ℂ)) with hg_def
  have hg : DifferentiableOn ℂ g (complexStrip n ρ) :=
    (differentiableOn_fderiv_of_isOpen_pi (isOpen_complexStrip n ρ) hu).clm_apply
      (differentiableOn_const _)
  have hgp : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → g (z + Pi.single i 1) = g z := fun i z hz => by
    simp only [hg_def, fderiv_add_single_of_periodic hup i hz]
  have hg0 : torusAverage (fun x : Fin n → ℝ => g fun j => (x j : ℂ)) = 0 :=
    torusAverage_complex_direction_eq_zero hρ hu hup _
  have hgA := norm_le_of_l1 (g := g) hρ hg hgp hs hH
  have heq : ∀ θ ∈ complexStrip n (ρ - δ), u θ = cohSolution ω g θ := fun θ hθ =>
    eq_cohSolution hω hγ hτ hδ hδρ hg hgp hgA hg0 (hu.mono hmono)
      (fun i z hz => hup i z (hmono hz)) hu0 (fun θ _ => rfl) hθ
  have hco : (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) =
      fun x => cohSolution ω g fun j => (x j : ℂ) :=
    funext fun x => heq _ (ofReal_mem_complexStrip hr x)
  obtain ⟨h1, h2⟩ := summableWeighted_cohSolution_l1 (g := g) hω hγ hτ hδ hδρ hs
  refine ⟨⟨by rw [hco]; exact h1, by
    rw [hco]
    exact h2.trans (mul_le_mul_of_nonneg_left hH (smallDivisorSup_nonneg ω δ))⟩,
    fun θ hθ => ?_⟩
  rw [heq θ hθ]
  exact norm_cohSolution_l1_le (g := g) hω hγ hτ hδ hδρ hs hH hθ

/-- **A-priori ℓ¹ bound in the operator sense.** If `u` is matrix-valued, holomorphic,
`1`-periodic, with zero average on `T_ρ`, and the components of `(∂_ω u) v` have ℓ¹ norm `≤ H` at
radius `2πρ` for every `‖v‖ ≤ 1`, then the components of `u v` have ℓ¹ norm `≤ Γ_∞(ω, δ) H` at
radius `2π(ρ-δ)`, and `‖u‖ ≤ Γ_∞(ω, δ) H` in the operator norm on `T_{ρ-δ}`. -/
theorem cohomological_apriori_operator_l1 {p q : ℕ}
    {u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip n ρ))
    (hup : ∀ (i : Fin n) z, z ∈ complexStrip n ρ → u (z + Pi.single i 1) = u z)
    (hu0 : torusAverage (fun x : Fin n → ℝ => u fun j => (x j : ℂ)) = 0) (hH0 : 0 ≤ H)
    (hs : ∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
      Fourier.SummableWeighted (2 * Real.pi * ρ)
          (torusCoeff fun x => (fderiv ℂ u (fun j => (x j : ℂ)) (fun l => (ω l : ℂ))).mulVec v i) ∧
        Fourier.weightedNorm (2 * Real.pi * ρ)
          (torusCoeff fun x => (fderiv ℂ u (fun j => (x j : ℂ)) (fun l => (ω l : ℂ))).mulVec v i)
            ≤ H) :
    (∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
      Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
          (torusCoeff fun x => (u fun j => (x j : ℂ)).mulVec v i) ∧
        Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
          (torusCoeff fun x => (u fun j => (x j : ℂ)).mulVec v i) ≤ smallDivisorSup ω δ * H) ∧
    ∀ θ ∈ complexStrip n (ρ - δ), ‖u θ‖ ≤ smallDivisorSup ω δ * H := by
  have hρ : 0 < ρ := hδ.trans hδρ
  -- each component of `u v` satisfies the scalar a-priori hypotheses
  have hcomp : ∀ v : Fin q → ℂ, ‖v‖ ≤ 1 → ∀ i : Fin p,
      (Fourier.SummableWeighted (2 * Real.pi * (ρ - δ))
          (torusCoeff fun x => (u fun j => (x j : ℂ)).mulVec v i) ∧
        Fourier.weightedNorm (2 * Real.pi * (ρ - δ))
          (torusCoeff fun x => (u fun j => (x j : ℂ)).mulVec v i) ≤ smallDivisorSup ω δ * H) ∧
      ∀ θ ∈ complexStrip n (ρ - δ), ‖(u θ).mulVec v i‖ ≤ smallDivisorSup ω δ * H := by
    intro v hv1 i
    obtain ⟨hw, hwavg, hwd⟩ := mulVec_transfer hρ hu v ω
    have hw0 : torusAverage (fun x : Fin n → ℝ => (u fun j => (x j : ℂ)).mulVec v) = 0 := by
      rw [hwavg, hu0, Matrix.zero_mulVec]
    obtain ⟨hwi, hwpi, hw0i⟩ := component_holomorphic_periodic hρ hw
      (fun k z hz => by simp only [hup k z hz]) hw0 i
    have hd : ∀ θ ∈ complexStrip n ρ,
        fderiv ℂ (fun z => (u z).mulVec v i) θ (fun l => (ω l : ℂ)) =
          (fderiv ℂ u θ (fun l => (ω l : ℂ))).mulVec v i := fun θ hθ => by
      rw [← fderiv_apply_of_differentiableAt
        (hw.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ)), hwd θ hθ]
    have hco : (fun x : Fin n → ℝ =>
        fderiv ℂ (fun z => (u z).mulVec v i) (fun j => (x j : ℂ)) (fun l => (ω l : ℂ))) =
          fun x => (fderiv ℂ u (fun j => (x j : ℂ)) (fun l => (ω l : ℂ))).mulVec v i :=
      funext fun x => hd _ (ofReal_mem_complexStrip hρ x)
    have hsi := hs v hv1 i
    rw [← hco] at hsi
    exact cohomological_apriori_l1 hω hγ hτ hδ hδρ (u := fun z => (u z).mulVec v i) hwi hwpi hw0i
      hsi.1 hsi.2
  refine ⟨fun v hv1 i => (hcomp v hv1 i).1, fun θ hθ => ?_⟩
  obtain ⟨v, hv, hMv⟩ := (isGreatest_norm_mulVec (u θ)).1
  have hv1 : ‖v‖ ≤ 1 := by simpa using hv
  have hMv' : ‖(u θ).mulVec v‖ = ‖u θ‖ := hMv
  rw [← hMv']
  exact (pi_norm_le_iff_of_nonneg (mul_nonneg (smallDivisorSup_nonneg ω δ) hH0)).mpr fun i =>
    (hcomp v hv1 i).2 θ hθ

end Apriori

end KAM

end
