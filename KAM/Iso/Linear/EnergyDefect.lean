/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Energy

/-!
# Part 1 (isoenergetic linear step): the energy defect of a correction

Blueprint node `bpI:p1:energy-approx`, part (f) (`KAM.Iso.Linear.energy_defect`): for
`ΔK = Pξ`, `ξ = (ξᴸ, ξᴺ)`, one has on `T_{r'}`

`DH(K) ΔK = Y ξᴺ + D(H ∘ K) ξᴸ = Y ξᴺ + (ηᴺ)ᵀ ξᴸ - ωᵀ Ω_K ξᴸ`,

the average of `DH(K) ΔK` splits linearly, and `|⟨D(H ∘ K) ξᴸ⟩| ≤ sup |D(H ∘ K)| · sup |ξᴸ|`.
Here `Y = energyRow H K = DH(K) N` is the last row of the extended torsion.

The auxiliary lemmas live in `KAM.Iso.Linear.Energy`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

namespace Energy

variable {n : ℕ}

/-- `Ω_K = Lᵀ Ω₀ L` is antisymmetric. -/
theorem lagrangeMat_antisymm (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (j l : Fin n) : lagrangeMat K θ j l = -lagrangeMat K θ l j := by
  rw [Exactness.lagrangeMat_apply, Exactness.lagrangeMat_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The combination `N ξ` of the frozen normal frame, as a vector of `ℂⁿ × ℂⁿ`. -/
theorem symm_normalMat_mulVec (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (ξ : Fin n → ℂ) :
    (sumVec n).symm (normalMat K θ *ᵥ ξ) = ∑ j, ξ j • normalFrame K θ j := by
  rw [LinearEquiv.symm_apply_eq]
  ext s
  simp [Matrix.mulVec, dotProduct, map_sum, map_smul, sumVec_normalFrame, mul_comm]

/-- Step `ea-defect`, first identity: `DH(K) P (ξᴸ, ξᴺ) = Y ξᴺ + D(H ∘ K) ξᴸ`. -/
theorem fderiv_frame_apply {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}
    (hH : DifferentiableAt ℂ H (K θ)) (hK : DifferentiableAt ℂ K θ) (ξL ξN : Fin n → ℂ) :
    fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim ξL ξN)) =
      energyRow H K θ ⬝ᵥ ξN + fderiv ℂ (fun y => H (K y)) θ ξL := by
  have h1 : (sumVec n).symm (tangentMat K θ *ᵥ ξL) = fderiv ℂ K θ ξL := by
    rw [tangentMat, colMat_mulVec]
    exact LinearEquiv.symm_apply_apply _ _
  rw [frameMat, Matrix.fromCols_mulVec_sumElim, map_add, map_add, symm_normalMat_mulVec, h1,
    fderiv_comp_apply hH hK, add_comm]
  congr 1
  simp only [map_sum, map_smul, smul_eq_mul, energyRow, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The energy row `Y = DH(K) N` is holomorphic on `T_r`, given the Gram determinant is a unit. -/
theorem differentiableOn_energyRow {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
    (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (energyRow H K) (complexStrip n r) := by
  have hN := differentiableOn_normalMat hK hG
  have hD := (differentiableOn_fderiv_h hS.toStanding).comp hK hKD
  refine differentiableOn_pi.2 fun b => ?_
  have hNF : DifferentiableOn ℂ (fun θ => normalFrame K θ b) (complexStrip n r) := by
    have hfun : (fun θ => normalFrame K θ b) =
        fun θ => (sumVecIso n).symm (fun s => normalMat K θ s b) := funext fun θ => by
      apply (sumVec n).injective
      rw [sumVec_normalFrame]
      exact ((sumVecIso n).apply_symm_apply _).symm
    rw [hfun]
    exact (sumVecIso n).symm.differentiable.comp_differentiableOn
      (differentiableOn_pi.2 fun s => (differentiableOn_matrix_iff_entries.1 hN) s b)
  exact hD.clm_apply hNF

/-- Step `ea-defect`, second identity:
`D(H ∘ K) v = (ηᴺ)ᵀ v - ωᵀ Ω_K v` (HL19 (4.4)). -/
theorem fderiv_comp_eq_etaN {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
    (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n r)
    (v : Fin n → ℂ) :
    fderiv ℂ (fun y => H (K y)) θ v =
      etaN H K ω θ ⬝ᵥ v - (fun l => (ω l : ℂ)) ⬝ᵥ (lagrangeMat K θ *ᵥ v) := by
  have he := fun j => Exactness.etaN_apply hS.toStanding hK hKD hθ j
  have hsw : ∑ j, ∑ l, lagrangeMat K θ j l * (ω l : ℂ) * v j =
      -∑ l, (ω l : ℂ) * ∑ j, lagrangeMat K θ l j * v j := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lagrangeMat_antisymm K θ j l]
    ring
  have hA : ∑ x, v x * fderiv ℂ (fun y => H (K y)) θ (Pi.single x 1) =
      ∑ x, fderiv ℂ (fun y => H (K y)) θ (Pi.single x 1) * v x :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [apply_pi_decomp]
  simp only [dotProduct, Matrix.mulVec, he, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  linear_combination hA + hsw

/-- Step `ea-defect`, size of `D(H ∘ K)`: `|D(H ∘ K)| ≤ n (|ηᴺ| + |ω| |Ω_K|)`. -/
theorem norm_fderiv_comp_le {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
    (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n r) :
    ‖fderiv ℂ (fun y => H (K y)) θ‖ ≤ n * (‖etaN H K ω θ‖ + ‖ω‖ * ‖lagrangeMat K θ‖) := by
  set C : ℝ := ‖etaN H K ω θ‖ + ‖ω‖ * ‖lagrangeMat K θ‖ with hC
  have hC0 : 0 ≤ C := by positivity
  have hcoord : ∀ j, ‖fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1)‖ ≤ C := fun j => by
    have hl : fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1) =
        etaN H K ω θ j + (lagrangeMat K θ *ᵥ fun l => (ω l : ℂ)) j := by
      rw [Exactness.etaN_apply hS.toStanding hK hKD hθ j, Matrix.mulVec, dotProduct]
      ring
    rw [hl]
    refine (norm_add_le _ _).trans (add_le_add (norm_le_pi_norm _ j) ?_)
    refine (norm_le_pi_norm _ j).trans ((Matrix.linfty_opNorm_mulVec _ _).trans ?_)
    rw [FrameAux.norm_ofReal_vec, mul_comm]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [apply_pi_decomp]
  calc ‖∑ j, v j * fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1)‖
      ≤ ∑ j, ‖v j * fderiv ℂ (fun y => H (K y)) θ (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖v‖ * C := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul (norm_le_pi_norm v j) (hcoord j) (norm_nonneg _) (norm_nonneg _)
    _ = n * C * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Energy

section Torus

variable {n : ℕ} {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}

/-- `bpI:p1:energy-approx` (f), the energy defect of `ΔK = Pξ`, `ξ = (ξᴸ, ξᴺ)`. -/
theorem energy_defect (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {r' : ℝ} (hr' : 0 < r')
    (hr'r : r' ≤ r) {ξL ξN : (Fin n → ℂ) → Fin n → ℂ}
    (hξL : DifferentiableOn ℂ ξL (complexStrip n r'))
    (hξN : DifferentiableOn ℂ ξN (complexStrip n r')) :
    (∀ θ ∈ complexStrip n r',
      fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ))) =
        energyRow H K θ ⬝ᵥ ξN θ + fderiv ℂ (fun y => H (K y)) θ (ξL θ) ∧
      fderiv ℂ (fun y => H (K y)) θ (ξL θ) =
        etaN H K ω θ ⬝ᵥ ξL θ - (fun l => (ω l : ℂ)) ⬝ᵥ (lagrangeMat K θ *ᵥ ξL θ) ∧
      ‖fderiv ℂ (fun y => H (K y)) θ‖ ≤ n * (‖etaN H K ω θ‖ + ‖ω‖ * ‖lagrangeMat K θ‖)) ∧
    avg (fun θ => fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ)))) =
      avg (fun θ => energyRow H K θ ⬝ᵥ ξN θ) + avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (ξL θ)) ∧
    ∀ A X : ℝ,
      (∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖fderiv ℂ (fun y => H (K y)) (fun i => (x i : ℂ))‖ ≤ A) →
      (∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        ‖ξL (fun i => (x i : ℂ))‖ ≤ X) →
      ‖avg (fun θ => fderiv ℂ (fun y => H (K y)) θ (ξL θ))‖ ≤ A * X := by
  -- `hKp`, `hKr` are part of the source setting; the proof does not
  -- need them.
  have _ := hKp
  have _ := hKr
  have hrr : complexStrip n r' ⊆ complexStrip n r := Energy.strip_subset hr'r
  have hHd : ∀ θ ∈ complexStrip n r, DifferentiableAt ℂ H (K θ) := fun θ hθ =>
    hS.holo.differentiableAt (hS.isOpen.mem_nhds (hKD θ hθ))
  have hKd : ∀ θ ∈ complexStrip n r, DifferentiableAt ℂ K θ := fun θ hθ =>
    hK.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have hHK : DifferentiableOn ℂ (fun θ => H (K θ)) (complexStrip n r) := hS.holo.comp hK hKD
  have hpt : ∀ θ ∈ complexStrip n r',
      fderiv ℂ H (K θ) ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ))) =
        energyRow H K θ ⬝ᵥ ξN θ + fderiv ℂ (fun y => H (K y)) θ (ξL θ) := fun θ hθ =>
    Energy.fderiv_frame_apply (hHd θ (hrr hθ)) (hKd θ (hrr hθ)) (ξL θ) (ξN θ)
  refine ⟨fun θ hθ => ⟨hpt θ hθ, Energy.fderiv_comp_eq_etaN hS hK hKD (hrr hθ) (ξL θ),
    Energy.norm_fderiv_comp_le hS hK hKD (hrr hθ)⟩, ?_, ?_⟩
  · have hE : Continuous fun x : Fin n → ℝ => energyRow H K fun i => (x i : ℂ) :=
      Exactness.continuous_real_of_differentiableOn hr
        (Energy.differentiableOn_energyRow hS hK hKD hG)
    have hN : Continuous fun x : Fin n → ℝ => ξN fun i => (x i : ℂ) :=
      Exactness.continuous_real_of_differentiableOn hr' hξN
    have hL : Continuous fun x : Fin n → ℝ => ξL fun i => (x i : ℂ) :=
      Exactness.continuous_real_of_differentiableOn hr' hξL
    have hF1 : Continuous fun x : Fin n → ℝ =>
        energyRow H K (fun i => (x i : ℂ)) ⬝ᵥ ξN fun i => (x i : ℂ) := by
      simp only [dotProduct]
      exact continuous_finsetSum _ fun b _ =>
        ((continuous_apply b).comp hE).mul ((continuous_apply b).comp hN)
    have hF2 : Continuous fun x : Fin n → ℝ =>
        fderiv ℂ (fun y => H (K y)) (fun i => (x i : ℂ)) (ξL fun i => (x i : ℂ)) :=
      (continuous_fderiv_real_of_holomorphic hr hHK).clm_apply hL
    have h1 : avg (fun θ => fderiv ℂ H (K θ)
        ((sumVec n).symm (frameMat K θ *ᵥ Sum.elim (ξL θ) (ξN θ)))) =
        avg (fun θ => energyRow H K θ ⬝ᵥ ξN θ + fderiv ℂ (fun y => H (K y)) θ (ξL θ)) :=
      congrArg torusAverage (funext fun x => hpt _ (ofReal_mem_complexStrip hr' x))
    rw [h1]
    exact integral_add (integrableOn_unitCube_of_continuous hF1)
      (integrableOn_unitCube_of_continuous hF2)
  · intro A X hA hX
    refine norm_torusAverage_le fun x hx => ?_
    show ‖fderiv ℂ (fun y => H (K y)) (fun i => (x i : ℂ)) (ξL fun i => (x i : ℂ))‖ ≤ A * X
    calc _ ≤ ‖fderiv ℂ (fun y => H (K y)) (fun i => (x i : ℂ))‖ * ‖ξL fun i => (x i : ℂ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ A * X :=
          mul_le_mul (hA x hx) (hX x hx) (norm_nonneg _) ((norm_nonneg _).trans (hA x hx))

end Torus

end KAM.Iso.Linear

end
