/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.Inverse

/-!
# Two-scale KAM step: small perturbations of invertible operators

`A + B` with `‖B‖ ‖A⁻¹‖ ≤ 1/2` is invertible, with inverse of the form `A⁻¹ ∘ N⁻¹`, `‖N⁻¹‖ ≤ 2`.
Design package P23-14 (`stepP:p3:st-U`).
-/

@[expose] public noncomputable section

namespace KAM.Planetary

theorem perturb_equiv {n : ℕ} (A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ))
    (B : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (hB : ‖B‖ * ‖(A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ ≤ 1 / 2) :
    ∃ A' : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (A' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) + B ∧
      ∀ w, ∃ u, A'.symm w = A.symm u ∧ ‖u‖ ≤ 2 * ‖w‖ := by
  set C : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := B.comp (A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    with hC
  have hCn : ‖C‖ ≤ 1 / 2 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans hB
  obtain ⟨N, hN, hN2⟩ := ext_neumann C hCn
  refine ⟨A.trans N, ?_, fun w => ⟨N.symm w, rfl, ?_⟩⟩
  · refine ContinuousLinearMap.ext fun x => ?_
    have h1 := congrArg (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T (A x)) hN
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, hC,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] at h1
    show N (A x) = A x + B x
    exact h1
  · exact (ContinuousLinearMap.le_opNorm (N.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) w).trans
      (mul_le_mul_of_nonneg_right hN2 (norm_nonneg _))

end KAM.Planetary

end
