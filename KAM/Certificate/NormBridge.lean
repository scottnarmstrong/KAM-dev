/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.PhaseBasis
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Norms on `ℂⁿ × ℂⁿ` from partial derivatives

Bridges between the row-sum bounds computed by the certificate checker (sums of norms of partial
derivatives along the phase basis) and the operator norms used by the iso-energetic a-posteriori
theorem: `‖Dƒ‖ ≤ ∑ₐ ‖∂ₐ ƒ‖`, the analogue for second derivatives, `X_H` in partials, and the
row-sum bounds for `DX_H` and `D²X_H`.
-/

@[expose] public section

noncomputable section

namespace KAM.Certificate

open KAM.Torus

variable {n : ℕ}

/-- Expansion of a vector in the phase basis. -/
theorem sum_sumVec_smul_phaseBasis (v : (Fin n → ℂ) × (Fin n → ℂ)) :
    ∑ a : Fin n ⊕ Fin n, sumVec n v a • phaseBasis a = v := by
  apply (sumVec n).injective
  rw [map_sum]
  simp only [phaseBasis, map_smul, LinearEquiv.apply_symm_apply]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem norm_sumVec_apply_le (v : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n ⊕ Fin n) :
    ‖sumVec n v a‖ ≤ ‖v‖ := by
  rw [← norm_sumVec]
  exact norm_le_pi_norm (sumVec n v) a

/-- Operator norm on `ℂⁿ × ℂⁿ` bounded by the sum over the phase basis. -/
theorem norm_clm_le_sum_phaseBasis {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] G) :
    ‖L‖ ≤ ∑ a : Fin n ⊕ Fin n, ‖L (phaseBasis a)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  conv_lhs => rw [← sum_sumVec_smul_phaseBasis v]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul (le_refl _) (norm_sumVec_apply_le v a) (norm_nonneg _) (norm_nonneg _)

theorem norm_fderiv_le_sum_partials {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖fderiv ℂ f z‖ ≤ ∑ a : Fin n ⊕ Fin n, ‖fderiv ℂ f z (phaseBasis a)‖ :=
  norm_clm_le_sum_phaseBasis _

/-- A continuous bilinear form on `ℂⁿ × ℂⁿ` is bounded by its values on the phase basis. -/
theorem norm_cmm_two_le_sum_phaseBasis
    (M : ((Fin n → ℂ) × (Fin n → ℂ)) [×2]→L[ℂ] ℂ) :
    ‖M‖ ≤ ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n, ‖M ![phaseBasis a, phaseBasis b]‖ := by
  have h1 : ‖M‖ = ‖M.curryLeft‖ := (M.curryLeft_norm).symm
  rw [h1]
  refine (norm_clm_le_sum_phaseBasis _).trans (Finset.sum_le_sum fun a _ => ?_)
  set N := M.curryLeft (phaseBasis a)
  have h2 : ‖N‖ = ‖(continuousMultilinearCurryFin1 ℂ ((Fin n → ℂ) × (Fin n → ℂ)) ℂ) N‖ :=
    ((continuousMultilinearCurryFin1 ℂ _ ℂ).norm_map N).symm
  rw [h2]
  refine (norm_clm_le_sum_phaseBasis _).trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_))
  simp only [continuousMultilinearCurryFin1_apply, N, ContinuousMultilinearMap.curryLeft_apply]
  congr 2
  funext i; fin_cases i <;> rfl

theorem norm_iteratedFDeriv_two_le_sum_partials
    {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖iteratedFDeriv ℂ 2 f z‖ ≤
      ∑ a : Fin n ⊕ Fin n, ∑ b : Fin n ⊕ Fin n,
        ‖iteratedFDeriv ℂ 2 f z ![phaseBasis a, phaseBasis b]‖ :=
  norm_cmm_two_le_sum_phaseBasis _

theorem phaseBasis_inl (j : Fin n) : phaseBasis (.inl j) = (Pi.single j 1, 0) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · by_cases h : i = j <;> simp [phaseBasis, sumVec, h]
  · simp [phaseBasis, sumVec]

/-- `X_H` in partials: `(X_H)_{inl i} = ∂_{inr i} H`, `(X_H)_{inr i} = -∂_{inl i} H`. -/
theorem hamiltonianVectorFieldℂ_sumVec (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n ⊕ Fin n) :
    sumVec n (hamiltonianVectorFieldℂ H z) a =
      Sum.elim (fun i => fderiv ℂ H z (phaseBasis (.inr i)))
        (fun i => -fderiv ℂ H z (phaseBasis (.inl i))) a := by
  rcases a with i | i <;>
    simp [hamiltonianVectorFieldℂ, sumVec_apply, phaseBasis_inr, phaseBasis_inl]

/-- Sign of the coordinate `a` of `X_H`. -/
def hamSign (a : Fin n ⊕ Fin n) : ℂ := Sum.elim (fun _ => 1) (fun _ => -1) a

theorem norm_hamSign (a : Fin n ⊕ Fin n) : ‖hamSign a‖ = 1 := by
  rcases a with i | i <;> simp [hamSign]

theorem sumVec_hamiltonianVectorFieldℂ_swap (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (a : Fin n ⊕ Fin n) :
    sumVec n (hamiltonianVectorFieldℂ H z) a = hamSign a * fderiv ℂ H z (phaseBasis a.swap) := by
  rw [hamiltonianVectorFieldℂ_sumVec]
  rcases a with i | i <;> simp [hamSign]

theorem hamiltonianVectorFieldℂ_eq_symm (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    hamiltonianVectorFieldℂ H =
      fun w => (sumVecIso n).symm (fun a => hamSign a * fderiv ℂ H w (phaseBasis a.swap)) := by
  funext w
  apply (sumVecIso n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, sumVecIso_apply]
  funext a
  exact sumVec_hamiltonianVectorFieldℂ_swap H w a

theorem sumVec_fderiv_hamiltonianVectorFieldℂ {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : ContDiffAt ℂ 2 H w) (v : (Fin n → ℂ) × (Fin n → ℂ))
    (a : Fin n ⊕ Fin n) :
    sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ H) w v) a =
      hamSign a * fderiv ℂ (fderiv ℂ H) w v (phaseBasis a.swap) := by
  have hd : DifferentiableAt ℂ (fderiv ℂ H) w :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG : HasFDerivAt (fun w a => hamSign a * fderiv ℂ H w (phaseBasis a.swap))
      (ContinuousLinearMap.pi fun a => hamSign a •
        (ContinuousLinearMap.apply ℂ ℂ (phaseBasis a.swap)).comp (fderiv ℂ (fderiv ℂ H) w)) w := by
    refine hasFDerivAt_pi'.2 fun a => ?_
    exact (((ContinuousLinearMap.apply ℂ ℂ (phaseBasis a.swap)).hasFDerivAt.comp w
      hd.hasFDerivAt)).const_mul (hamSign a)
  have hX := ((sumVecIso n).symm.toContinuousLinearEquiv.hasFDerivAt.comp w hG)
  have hfun : hamiltonianVectorFieldℂ H = ⇑(sumVecIso n).symm.toContinuousLinearEquiv ∘
      fun w a => hamSign a * fderiv ℂ H w (phaseBasis a.swap) :=
    hamiltonianVectorFieldℂ_eq_symm H
  rw [hfun, hX.fderiv]
  exact congrFun ((sumVecIso n).apply_symm_apply _) a

end KAM.Certificate

end
