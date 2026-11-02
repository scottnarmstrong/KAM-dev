/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ModifiedStepSolve
public import KAM.Wave.KamStep.TaylorBlocks
public import KAM.Wave.Homological.ModifiedReweight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reweighting on `KamPhase` (blueprint-W `bpW:w5:w4-modified`, `bpW:w5:step`, modified case)

`stepRhoK a p pb hc`: the diagonal `D_ρ`, `ρ_j = ω_{a,p₊}(j+2)/ω_{a,p+1}(j+2) ≤ 1`, on the normal
components `(u, v)` of `KamPhase` (it converts a `(p+1)`-representative into a `p₊`-representative).
* `kamNorm_stepRhoK_le`: `|D_ρ W|_r ≤ |W|_r`;
* `stepZ_stepRhoK`, `stepZb_stepRhoK`: `z, z̄` commute with `D_ρ`;
* `stepSymp_stepRhoK`: `ϖ_{p₊,p}(D_ρ Y, W) = ϖ_{p+1,p}(Y, W)`;
* `IsSmoothing.rhoK`: `(P, X) ∈ 𝒮_{p+1}` gives `(P, D_ρ ∘ X) ∈ 𝒮_{p₊}`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb : ℝ}

/-- The reweighting `D_ρ` on `KamPhase`: `(θ, y, u, v) ↦ (θ, y, ρu, ρv)`. -/
def stepRhoK (a p pb : ℝ) (hc : pb ≤ p + 1) : KamPhase →L[ℂ] KamPhase :=
  (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)).prodMap ((ContinuousLinearMap.id ℂ (Fin 2 → ℂ)).prodMap
    ((homModRho a p pb hc).prodMap (homModRho a p pb hc)))

theorem stepRhoK_apply (hc : pb ≤ p + 1) (θ y : Fin 2 → ℂ) (u v : HomL2) :
    stepRhoK a p pb hc (θ, y, u, v) = (θ, y, homModRho a p pb hc u, homModRho a p pb hc v) := rfl

theorem stepRhoK_fst (hc : pb ≤ p + 1) (W : KamPhase) : (stepRhoK a p pb hc W).1 = W.1 := rfl

theorem stepRhoK_snd_fst (hc : pb ≤ p + 1) (W : KamPhase) :
    (stepRhoK a p pb hc W).2.1 = W.2.1 := rfl

theorem kamNorm_stepRhoK_le (hc : pb ≤ p + 1) {r : ℝ} (hr : 0 < r) (W : KamPhase) :
    kamNorm r (stepRhoK a p pb hc W) ≤ kamNorm r W := by
  obtain ⟨θ, y, u, v⟩ := W
  rw [stepRhoK_apply]
  unfold kamNorm
  have h1 := norm_homModRho_apply_le (a := a) hc u
  have h2 := norm_homModRho_apply_le (a := a) hc v
  have h3 : ‖homModRho a p pb hc u‖ / r ≤ ‖u‖ / r := div_le_div_of_nonneg_right h1 hr.le
  have h4 : ‖homModRho a p pb hc v‖ / r ≤ ‖v‖ / r := div_le_div_of_nonneg_right h2 hr.le
  simp only at h3 h4 ⊢
  linarith

theorem stepZ_stepRhoK (hc : pb ≤ p + 1) (W : KamPhase) :
    stepZ (stepRhoK a p pb hc W) = homModRho a p pb hc (stepZ W) := by
  obtain ⟨θ, y, u, v⟩ := W
  rw [stepRhoK_apply, stepZ_apply, stepZ_apply, map_smul, map_add, map_smul]

theorem stepZb_stepRhoK (hc : pb ≤ p + 1) (W : KamPhase) :
    stepZb (stepRhoK a p pb hc W) = homModRho a p pb hc (stepZb W) := by
  obtain ⟨θ, y, u, v⟩ := W
  rw [stepRhoK_apply, stepZb_apply, stepZb_apply, map_smul, map_sub, map_smul]

theorem stepZ_comp_stepRhoK (hc : pb ≤ p + 1) :
    stepZ.comp (stepRhoK a p pb hc) = (homModRho a p pb hc).comp stepZ :=
  ContinuousLinearMap.ext fun W => stepZ_stepRhoK hc W

theorem stepZb_comp_stepRhoK (hc : pb ≤ p + 1) :
    stepZb.comp (stepRhoK a p pb hc) = (homModRho a p pb hc).comp stepZb :=
  ContinuousLinearMap.ext fun W => stepZb_stepRhoK hc W

/-- `1/(ω_{p₊}ω_p)` times `ρ` is `1/(ω_{p+1}ω_p)`. -/
theorem stepWinv_mul_ratio (a p pb : ℝ) (j : ℕ+) :
    stepWinv a pb p j * (homModRatio a p pb j : ℂ) = stepWinv a (p + 1) p j := by
  unfold stepWinv homModRatio
  have h0 := homWt_pos a p j
  have h1 := homWt_pos a pb j
  have h2 := homWt_pos a (p + 1) j
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp

theorem stepPairCLM_rho (ha : 0 ≤ a) (hc : pb ≤ p + 1) (h1 : 0 ≤ pb + p) (h2 : 0 ≤ (p + 1) + p)
    (c z : HomL2) :
    stepPairCLM (q := pb) (q' := p) ha h1 (homModRho a p pb hc c) z =
      stepPairCLM (q := p + 1) (q' := p) ha h2 c z := by
  have e : weightedDiagCLM (stepWinv a pb p) (norm_stepWinv_le ha h1) (homModRho a p pb hc c) =
      weightedDiagCLM (stepWinv a (p + 1) p) (norm_stepWinv_le ha h2) c := by
    ext j
    simp only [weightedDiagCLM_apply, homModRho_apply]
    rw [← mul_assoc, stepWinv_mul_ratio]
  show homPairL2 (weightedDiagCLM (stepWinv a pb p) _ (homModRho a p pb hc c)) z =
    homPairL2 (weightedDiagCLM (stepWinv a (p + 1) p) _ c) z
  rw [e]

/-- **Pairing invariance**: `ϖ_{p₊,p}(D_ρ Y, W) = ϖ_{p+1,p}(Y, W)`. -/
theorem stepSymp_stepRhoK (ha : 0 ≤ a) (hc : pb ≤ p + 1) (h1 : 0 ≤ pb + p) (h2 : 0 ≤ (p + 1) + p)
    (Y W : KamPhase) :
    stepSymp (q := pb) (q' := p) ha h1 (stepRhoK a p pb hc Y) W =
      stepSymp (q := p + 1) (q' := p) ha h2 Y W := by
  unfold stepSymp
  rw [stepRhoK_fst, stepRhoK_snd_fst]
  show _ + stepPairCLM (q := pb) (q' := p) ha h1 (homModRho a p pb hc Y.2.2.1) W.2.2.2 -
      stepPairCLM (q := pb) (q' := p) ha h1 (homModRho a p pb hc Y.2.2.2) W.2.2.1 = _
  rw [stepPairCLM_rho ha hc h1 h2, stepPairCLM_rho ha hc h1 h2]

/-- **Smoothing transfers along the reweighting**: `(P, X) ∈ 𝒮_{p+1}` gives
`(P, D_ρ ∘ X) ∈ 𝒮_{p₊}`. -/
theorem IsSmoothing.rhoK {V : Set KamPhase} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}
    (ha : 0 ≤ a) (hc : pb ≤ p + 1) (h1 : 0 ≤ pb + p) (h2 : 0 ≤ (p + 1) + p)
    (h : IsSmoothing (p := p) (pb := p + 1) ha h2 V P X) :
    IsSmoothing (p := p) (pb := pb) ha h1 V P (fun w => stepRhoK a p pb hc (X w)) where
  holoP := h.holoP
  holoX := (stepRhoK a p pb hc).differentiable.comp_differentiableOn h.holoX
  deriv_eq := fun w hw W => by
    rw [h.deriv_eq w hw W, stepSymp_stepRhoK ha hc h1 h2]

end KAM.Wave
