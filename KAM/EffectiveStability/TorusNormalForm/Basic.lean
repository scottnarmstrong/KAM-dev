/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChart
public import KAM.EffectiveStability.Domains
public import KAM.Frozen.Defs.HamiltonianVectorField
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The normal form `E0 + ω'·J + R` in the torus chart: first-order facts (track B, B5-NF)

For the chart `Ψ = torusChartMap u v` and the torus `K φ = (x φ, v φ)` carrying the linear flow
`fderiv K φ ω' = X_hR (K φ)` on the energy level `hR (K φ) = E0`, the pulled-back Hamiltonian
`G = hR ∘ Ψ` satisfies `G (φ, 0) = E0` and `DG (φ, 0) (0, J) = ω'·J` (`torusNF_dG_J`), so the
remainder `R = G - (E0 + ω'·J)` vanishes to second order in `J` along the zero section
(`torusNFRem_zero`, `torusNFRem_dJ`, `torusNFRem_dphi`, `torusNFRem_d2`), and is angle-periodic
(`torusNFRem_shift`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Matrix

variable {n : ℕ} {u v : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}

/-- The Lagrangian graph torus `φ ↦ (x φ, v φ)` in the real phase space. -/
def torusNFGraph (u v : (Fin n → ℝ) → (Fin n → ℝ)) (φ : Fin n → ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (torusChartX u φ, v φ)

/-- The torus data (outputs of B5-LAG, stated as hypotheses): `hR` is differentiable along the
torus, the torus is invariant under the linear flow `ω'`, and lies on the level `hR = E0`. -/
structure TorusNFTorus (u v : (Fin n → ℝ) → (Fin n → ℝ))
    (hR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (E0 : ℝ) (ω' : Fin n → ℝ) : Prop where
  hRdiff : ∀ φ, DifferentiableAt ℝ hR (torusNFGraph u v φ)
  invariance : ∀ φ, fderiv ℝ (torusNFGraph u v) φ ω' =
    KAM.hamiltonianVectorField hR (torusNFGraph u v φ)
  energy : ∀ φ, hR (torusNFGraph u v φ) = E0

/-- The remainder `R w = hR (Ψ w) - (E0 + ω'·J)`. -/
def torusNFRem (hR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (u v : (Fin n → ℝ) → (Fin n → ℝ))
    (E0 : ℝ) (ω' : Fin n → ℝ) (w : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  hR (torusChartMap u v w) - (E0 + ∑ j, ω' j * w.2 j)

/-- The linear part `w ↦ ω'·w.2` as a continuous linear functional. -/
def torusNFLin (ω' : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, ω' j • (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))

theorem torusNFLin_apply (ω' : Fin n → ℝ) (w : (Fin n → ℝ) × (Fin n → ℝ)) :
    torusNFLin ω' w = ∑ j, ω' j * w.2 j := by
  simp [torusNFLin]

theorem torusNFRem_eq (hR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (E0 : ℝ) (ω' : Fin n → ℝ) :
    torusNFRem hR u v E0 ω' = fun w => (hR ∘ torusChartMap u v) w - (E0 + torusNFLin ω' w) := by
  funext w; simp [torusNFRem, torusNFLin_apply]

/-- A linear functional on `ℝⁿ × ℝⁿ` evaluated on `(0, q)`. -/
theorem clm_apply_zero_snd (L : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] ℝ) (q : Fin n → ℝ) :
    L (0, q) = ∑ k, q k * L (0, Pi.single k 1) := by
  have h : ((0 : Fin n → ℝ), q) =
      ∑ k, q k • ((0 : Fin n → ℝ), (Pi.single k 1 : Fin n → ℝ)) := by
    ext i
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem torusChartMap_fderiv_zero_snd (h : TorusChartData u v κ) (φ J : Fin n → ℝ) :
    fderiv ℝ (torusChartMap u v) (φ, 0) (0, J) = (0, torusChartInvT u φ *ᵥ J) := by
  refine Prod.ext ?_ ?_
  · rw [torusChartMap_fderiv_fst h]; simp
  · rw [torusChartMap_fderiv_snd h]; simp [torusChartDInvT]

section Item1

variable {hR : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {E0 : ℝ} {ω' : Fin n → ℝ}

/-- The derivative of the pulled-back Hamiltonian in the action direction along the zero
section is the frequency: `D(hR ∘ Ψ)(φ, 0)(0, J) = ω'·J`. -/
theorem torusNF_dG_J (h : TorusChartData u v κ) (ht : TorusNFTorus u v hR E0 ω') (φ J : Fin n → ℝ) :
    fderiv ℝ (hR ∘ torusChartMap u v) (φ, 0) (0, J) = ∑ j, ω' j * J j := by
  have hΨ := (torusChartMap_differentiable h) (φ, 0)
  have hK : torusChartMap u v (φ, 0) = torusNFGraph u v φ := torusChartMap_zero φ
  have hRd : DifferentiableAt ℝ hR (torusChartMap u v (φ, 0)) := by
    rw [hK]; exact ht.hRdiff φ
  rw [fderiv_comp _ hRd hΨ, ContinuousLinearMap.comp_apply, torusChartMap_fderiv_zero_snd h, hK,
    clm_apply_zero_snd]
  -- the first component of the invariance identity
  have hinv := congrArg Prod.fst (ht.invariance φ)
  have hxd : DifferentiableAt ℝ (torusChartX u) φ :=
    ((torusChartX_contDiff h.toTorusBaseData).differentiable (by norm_num)) φ
  have hvd : DifferentiableAt ℝ v φ := (h.vSmooth.differentiable (by norm_num)) φ
  have hKd : HasFDerivAt (torusNFGraph u v)
      ((fderiv ℝ (torusChartX u) φ).prod (fderiv ℝ v φ)) φ :=
    hxd.hasFDerivAt.prodMk hvd.hasFDerivAt
  rw [hKd.fderiv] at hinv
  simp only [ContinuousLinearMap.prod_apply] at hinv
  have h1 : ∀ k, fderiv ℝ hR (torusNFGraph u v φ) (0, Pi.single k 1) =
      (torusChartJac u φ *ᵥ ω') k := fun k => by
    rw [torusChartJac_mulVec, hinv]; rfl
  simp only [h1]
  have e1 : ∑ k, (torusChartInvT u φ *ᵥ J) k * (torusChartJac u φ *ᵥ ω') k =
      (torusChartInvT u φ *ᵥ J) ⬝ᵥ (torusChartJac u φ *ᵥ ω') := rfl
  rw [e1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    torusChartJacT_invT_mulVec h.toTorusBaseData]
  simp only [dotProduct, mul_comm]

end Item1

end KAM.EffectiveStability

end
