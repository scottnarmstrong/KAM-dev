/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Chart.Shift
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The symmetry hypothesis of the shift for a gradient shift (T2-CONF, N2-Chart)

`bracketSum_comp_shiftChart` assumes `∂_{θ_i} B_l = ∂_{θ_l} B_i` at `φ`, with
`∂_{θ_i} = fderiv · (phiOf (Pi.single i 1))` on functions of `φ`. This file proves it for a gradient
shift `B_l = c_l + ∂_{θ_l} S` (near `φ`), `S` a function of `φ` that is `C²` at `φ`, by the symmetry
of second derivatives (`shift_symm_of_gradient`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Filter Topology

/-- **The symmetry hypothesis for a gradient shift.** If `B φ' l = c l + ∂_{θ_l} S φ'` for `φ'`
near `φ` and `S` is `C²` at `φ`, then `∂_{θ_i} B_l = ∂_{θ_l} B_i` at `φ` for all `i, l : Fin 3`. -/
theorem shift_symm_of_gradient {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {S : (Fin 2 → ℝ) → ℝ}
    {c : Fin 3 → ℝ} {φ : Fin 2 → ℝ} (hS : ContDiffAt ℝ 2 S φ)
    (hB : B =ᶠ[𝓝 φ] fun φ' l => c l + fderiv ℝ S φ' (phiOf (Pi.single l 1))) (i l : Fin 3) :
    fderiv ℝ B φ (phiOf (Pi.single i 1)) l = fderiv ℝ B φ (phiOf (Pi.single l 1)) i := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ S) φ :=
    (hS.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hcomp : ∀ k : Fin 3, HasFDerivAt
      (fun φ' => c k + fderiv ℝ S φ' (phiOf (Pi.single k 1)))
      ((fderiv ℝ (fderiv ℝ S) φ).flip (phiOf (Pi.single k 1))) φ := by
    intro k
    have := (hdiff.hasFDerivAt.clm_apply (hasFDerivAt_const (phiOf (Pi.single k 1)) φ)).const_add
      (c k)
    simpa using this
  have hpi : HasFDerivAt (fun φ' (k : Fin 3) => c k + fderiv ℝ S φ' (phiOf (Pi.single k 1)))
      (ContinuousLinearMap.pi fun k => (fderiv ℝ (fderiv ℝ S) φ).flip (phiOf (Pi.single k 1))) φ :=
    hasFDerivAt_pi.2 hcomp
  have hsymm := hS.isSymmSndFDerivAt (by simp)
  rw [hB.fderiv_eq, hpi.fderiv]
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.flip_apply]
  exact hsymm _ _

end KAM.EffectiveStability.Tube

end
