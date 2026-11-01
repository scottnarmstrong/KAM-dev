/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepSolve
public import KAM.Wave.KamStep.StepFieldBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Hessian blocks of a Taylor polynomial (blueprint-W `bpW:w5:taylor` (i), step `t-comp`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepIotaZ z = (0,0,u,v)` with `(z,z̄) = (z,0)`, `stepIotaZb z` with `(z,z̄) = (0,z)`.
`stepPair_z`: `ϖ(Y,W) = 2π(⟨Y_θ,W_y⟩-⟨Y_y,W_θ⟩) + i(⟨Y_z,W_{z̄}⟩-⟨Y_{z̄},W_z⟩)`.
For a linear map `A` (the derivative `DX(w₀)`) the four blocks `blockP, blockP', blockQ, blockQt`
satisfy `⟨P z₁,z₂⟩ = ½ϖ(Aιz₁,ιz₂)` etc., so the symmetries of the class `𝒯` follow from the
symmetry of `ϖ(A·,·)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- The direction `(z, z̄) = (z, 0)`: `(u,v) = (z/√2, -iz/√2)`. -/
def stepIotaZ : HomL2 →L[ℂ] KamPhase :=
  (0 : HomL2 →L[ℂ] (Fin 2 → ℂ)).prod ((0 : HomL2 →L[ℂ] (Fin 2 → ℂ)).prod
    ((homSqrt2⁻¹ • ContinuousLinearMap.id ℂ HomL2).prod
      ((-Complex.I * homSqrt2⁻¹) • ContinuousLinearMap.id ℂ HomL2)))

/-- The direction `(z, z̄) = (0, z)`: `(u,v) = (z/√2, iz/√2)`. -/
def stepIotaZb : HomL2 →L[ℂ] KamPhase :=
  (0 : HomL2 →L[ℂ] (Fin 2 → ℂ)).prod ((0 : HomL2 →L[ℂ] (Fin 2 → ℂ)).prod
    ((homSqrt2⁻¹ • ContinuousLinearMap.id ℂ HomL2).prod
      ((Complex.I * homSqrt2⁻¹) • ContinuousLinearMap.id ℂ HomL2)))

theorem stepIotaZ_apply (z : HomL2) :
    stepIotaZ z = (0, 0, homSqrt2⁻¹ • z, (-Complex.I * homSqrt2⁻¹) • z) := rfl

theorem stepIotaZb_apply (z : HomL2) :
    stepIotaZb z = (0, 0, homSqrt2⁻¹ • z, (Complex.I * homSqrt2⁻¹) • z) := rfl

theorem homSqrt2_inv_sq : homSqrt2⁻¹ * homSqrt2⁻¹ = 1 / 2 := by
  rw [← mul_inv, homSqrt2_sq]; norm_num

theorem stepZ_iotaZ (z : HomL2) : stepZ (stepIotaZ z) = z := by
  rw [stepIotaZ_apply, stepZ_apply]
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  linear_combination (2 * (z j : ℂ)) * homSqrt2_inv_sq +
    (-(homSqrt2⁻¹ * homSqrt2⁻¹ * (z j : ℂ))) * Complex.I_sq

theorem stepZb_iotaZ (z : HomL2) : stepZb (stepIotaZ z) = 0 := by
  rw [stepIotaZ_apply, stepZb_apply]
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    lp.coeFn_zero, Pi.zero_apply]
  linear_combination (homSqrt2⁻¹ * homSqrt2⁻¹ * (z j : ℂ)) * Complex.I_sq

theorem stepZ_iotaZb (z : HomL2) : stepZ (stepIotaZb z) = 0 := by
  rw [stepIotaZb_apply, stepZ_apply]
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
    lp.coeFn_zero, Pi.zero_apply]
  linear_combination (homSqrt2⁻¹ * homSqrt2⁻¹ * (z j : ℂ)) * Complex.I_sq

theorem stepZb_iotaZb (z : HomL2) : stepZb (stepIotaZb z) = z := by
  rw [stepIotaZb_apply, stepZb_apply]
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (2 * (z j : ℂ)) * homSqrt2_inv_sq +
    (-(homSqrt2⁻¹ * homSqrt2⁻¹ * (z j : ℂ))) * Complex.I_sq

variable {a p pb : ℝ}

/-- **The symplectic pairing in `(z, z̄)` coordinates.** -/
theorem stepSymp_z (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (Y W : KamPhase) :
    stepSymp (q := p) (q' := pb) ha hpp Y W =
      2 * Real.pi * ((∑ i, Y.1 i * W.2.1 i) - ∑ i, Y.2.1 i * W.1 i) +
        Complex.I * (stepPr ha hpp (stepZ Y) (stepZb W) - stepPr ha hpp (stepZb Y) (stepZ W)) := by
  have hYu := homU_stepZ Y
  have hYv := homV_stepZ Y
  have hWu := homU_stepZ W
  have hWv := homV_stepZ W
  unfold homU at hYu hWu
  unfold homV at hYv hWv
  unfold stepSymp
  rw [← hYu, ← hYv, ← hWu, ← hWv]
  simp only [map_smul, map_add, map_sub, smul_apply, smul_eq_mul, add_apply, sub_apply]
  have h2 := homSqrt2_inv_sq
  linear_combination (2 * Complex.I * (stepPr ha hpp (stepZ Y) (stepZb W) -
    stepPr ha hpp (stepZb Y) (stepZ W))) * h2

/-- The block `P` from `A = DX(w₀)`: `P = (-i/2) (z̄-part of A ι_z)`. -/
def blockP (A : KamPhase →L[ℂ] KamPhase) : HomOp :=
  (-Complex.I / 2) • stepZb.comp (A.comp stepIotaZ)

/-- The block `P'`: `P' = (i/2) (z-part of A ι_{z̄})`. -/
def blockP' (A : KamPhase →L[ℂ] KamPhase) : HomOp :=
  (Complex.I / 2) • stepZ.comp (A.comp stepIotaZb)

/-- The block `Q`: `Q = i (z-part of A ι_z)`. -/
def blockQ (A : KamPhase →L[ℂ] KamPhase) : HomOp :=
  Complex.I • stepZ.comp (A.comp stepIotaZ)

/-- The block `Q^T`: `Q^T = -i (z̄-part of A ι_{z̄})`. -/
def blockQt (A : KamPhase →L[ℂ] KamPhase) : HomOp :=
  (-Complex.I) • stepZb.comp (A.comp stepIotaZb)

theorem stepSymp_iotaZ (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (Y : KamPhase) (z : HomL2) :
    stepSymp (q := p) (q' := pb) ha hpp Y (stepIotaZ z) = -Complex.I * stepPr ha hpp (stepZb Y) z := by
  rw [stepSymp_z, stepZb_iotaZ, stepZ_iotaZ]
  simp [stepIotaZ_apply]

theorem stepSymp_iotaZb (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (Y : KamPhase) (z : HomL2) :
    stepSymp (q := p) (q' := pb) ha hpp Y (stepIotaZb z) = Complex.I * stepPr ha hpp (stepZ Y) z := by
  rw [stepSymp_z, stepZb_iotaZb, stepZ_iotaZb]
  simp [stepIotaZb_apply]

theorem stepPr_blockP (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (A : KamPhase →L[ℂ] KamPhase) (z₁ z₂ : HomL2) :
    stepPr ha hpp (blockP A z₁) z₂ =
      (1 / 2 : ℂ) * stepSymp (q := p) (q' := pb) ha hpp (A (stepIotaZ z₁)) (stepIotaZ z₂) := by
  rw [stepSymp_iotaZ]
  simp only [blockP, smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  ring

theorem stepPr_blockP' (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (A : KamPhase →L[ℂ] KamPhase)
    (z₁ z₂ : HomL2) :
    stepPr ha hpp (blockP' A z₁) z₂ =
      (1 / 2 : ℂ) * stepSymp (q := p) (q' := pb) ha hpp (A (stepIotaZb z₁)) (stepIotaZb z₂) := by
  rw [stepSymp_iotaZb]
  simp only [blockP', smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  ring

theorem stepPr_blockQ (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (A : KamPhase →L[ℂ] KamPhase)
    (z₁ z₂ : HomL2) :
    stepPr ha hpp (blockQ A z₁) z₂ =
      stepSymp (q := p) (q' := pb) ha hpp (A (stepIotaZ z₁)) (stepIotaZb z₂) := by
  rw [stepSymp_iotaZb]
  simp only [blockQ, smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]

theorem stepPr_blockQt (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (A : KamPhase →L[ℂ] KamPhase)
    (z₁ z₂ : HomL2) :
    stepPr ha hpp (blockQt A z₁) z₂ =
      stepSymp (q := p) (q' := pb) ha hpp (A (stepIotaZb z₁)) (stepIotaZ z₂) := by
  rw [stepSymp_iotaZ]
  simp only [blockQt, smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]

theorem homNormalEntry_eq_pr (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (A : HomOp) (i j : ℕ+) :
    homNormalEntry_gen a p pb A i j =
      ((homWt a p i * homWt a p j : ℝ) : ℂ) *
        stepPr ha (homPP hp hpb) (A (kamBasis ℂ j)) (kamBasis ℂ i) := by
  have h1 := homLam_entry_eq_gen ha hp hpb A i j
  rw [kamEntry_homLamCLM_gen] at h1
  have hw1 : (homWt a p i : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p i).ne'
  have hw2 : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
  have e : stepPr ha (homPP hp hpb) (A (kamBasis ℂ j)) (kamBasis ℂ i) =
      homLamD_gen a p pb i * kamEntry A i j := by
    rw [stepPr_eq_homPairL2, homPairL2_single_right, homLamDiag_apply_gen]
    rfl
  rw [e]
  push_cast
  rw [← mul_assoc, mul_assoc _ (homLamD_gen a p pb i) , h1]
  field_simp

theorem homNormalEntry_symm_of_pr (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {A A' : HomOp}
    (h : ∀ x y, stepPr ha (homPP hp hpb) (A x) y = stepPr ha (homPP hp hpb) (A' y) x)
    (i j : ℕ+) :
    homNormalEntry_gen a p pb A i j = homNormalEntry_gen a p pb A' j i := by
  rw [homNormalEntry_eq_pr ha hp hpb, homNormalEntry_eq_pr ha hp hpb, h (kamBasis ℂ j) (kamBasis ℂ i),
    mul_comm (homWt a p i : ℝ)]

end KAM.Wave
