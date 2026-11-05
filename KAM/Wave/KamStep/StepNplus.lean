/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepFreqBound
public import KAM.Wave.KamStep.StepSolve
public import KAM.Wave.KamStep.TaylorReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The new normal form `N_+ = N + N̂` (blueprint-W `bpW:w5:new-ham`, `bpW:w5:step` (iii))

`stepNfun_add_Nhat`: when `[b]` and `[Q]_{jj}` are real (`homCoeff_b_real`, `homCoeff_Q_real`),
`N_{ω,Ω} + N̂ = N_{ω+ω̂, Ω+Ω̂}` with `ω̂ = Re[b]`, `Ω̂_j = Re[Q]_{jj}` (`stepOmegaHat`,
`stepOmegaTail`) as functions on `KamPhase`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem homNOmegaCLM_add {γ K K' K'' : ℝ} {Ω Ω' : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK : 0 ≤ K)
    (hK' : 0 ≤ K') (hK'' : 0 ≤ K'') (hΩ : ∀ j : ℕ+, |Ω j| ≤ K * ((j : ℝ) + 2))
    (hΩ' : ∀ j : ℕ+, |Ω' j| ≤ K' * ((j : ℝ) + 2))
    (hΩ'' : ∀ j : ℕ+, |Ω j + Ω' j| ≤ K'' * ((j : ℝ) + 2)) (z zb : HomL2) :
    homNOmegaCLM hG hK'' (Ω := fun j => Ω j + Ω' j) hΩ'' z zb =
      homNOmegaCLM hG hK hΩ z zb + homNOmegaCLM hG hK' hΩ' z zb := by
  have hD : weightedDiagCLM (homNcoef a p (fun j => Ω j + Ω' j))
        (norm_homNcoef_le hG hK'' hΩ'') z =
      weightedDiagCLM (homNcoef a p Ω) (norm_homNcoef_le hG hK hΩ) z +
        weightedDiagCLM (homNcoef a p Ω') (norm_homNcoef_le hG hK' hΩ') z := by
    ext j
    simp only [weightedDiagCLM_apply, lp.coeFn_add, Pi.add_apply, homNcoef]
    push_cast
    ring
  show homPairL2 (weightedDiagCLM (homNcoef a p (fun j => Ω j + Ω' j))
      (norm_homNcoef_le hG hK'' hΩ'') z) zb = homPairL2 (weightedDiagCLM (homNcoef a p Ω)
      (norm_homNcoef_le hG hK hΩ) z) zb + homPairL2 (weightedDiagCLM (homNcoef a p Ω')
      (norm_homNcoef_le hG hK' hΩ') z) zb
  rw [hD, map_add, ContinuousLinearMap.add_apply]

/-- **`N + N̂ = N_+`** as functions (`bpW:w5:step`, the normal form after the step). -/
theorem stepNfun_add_Nhat {γ K K' K'' : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK : 0 ≤ K)
    (hK' : 0 ≤ K') (hK'' : 0 ≤ K'') (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (T : HomTaylor_gen a p pb s) (hΩ : ∀ j : ℕ+, |Ω j| ≤ K * ((j : ℝ) + 2))
    (hΩ' : ∀ j : ℕ+, |stepOmegaTail T j| ≤ K' * ((j : ℝ) + 2))
    (hΩ'' : ∀ j : ℕ+, |Ω j + stepOmegaTail T j| ≤ K'' * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ)
    (hb : ∀ k, (homCoeff T.b 0 k).im = 0)
    (hQ : ∀ j, (homNormalEntry_gen a p pb (homCoeff T.Q 0) j j).im = 0) (w : KamPhase) :
    stepNfun hG hK hΩ ω w + waveStepFun ha (homPP hp hpb) (homNhatTaylor_gen T) w =
      stepNfun hG hK'' (Ω := fun j => Ω j + stepOmegaTail T j) hΩ''
        (fun k => ω k + stepOmegaHat T k) w := by
  have hN : ∀ z zb : HomL2, homNhat_gen T w.2.1 z zb =
      ∑ k, (stepOmegaHat T k : ℂ) * w.2.1 k + homNOmegaCLM hG hK' hΩ' z zb := by
    intro z zb
    unfold homNhat_gen
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      exact Complex.ext (by simp [stepOmegaHat]) (by simp [hb k])
    · rw [homNOmegaCLM_apply]
      refine tsum_congr fun j => ?_
      have hw : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
      have e : homNormalEntry_gen a p pb (homCoeff T.Q 0) j j = (stepOmegaTail T j : ℂ) :=
        Complex.ext (by simp [stepOmegaTail]) (by simp [hQ j])
      rw [e]
      unfold homNcoef
      field_simp
  rw [stepFun_eq_homRval ha hp hpb, homNhatTaylor_val_gen ha hp hpb, hN]
  unfold stepNfun homNfun
  rw [homNOmegaCLM_add hG hK hK' hK'' hΩ hΩ' hΩ'']
  simp only [homLomega_apply, stepToHom_apply, homPrY, homPrZ, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  simp only [Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  ring

end KAM.Wave
