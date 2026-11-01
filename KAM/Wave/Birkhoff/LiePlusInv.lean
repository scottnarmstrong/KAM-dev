/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LiePlus

/-!
# Invertibility of `DΓ_t` on `𝔚⁺` (blueprint-W `bpW:w3:flow` (iii))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

`lie_plus_inverse`: in the setting of `LiePlus`, `DΓ_t(w) = I + ι Ξ`, it maps `F` into itself
(`A ι = ι (1 + Ξ ι)`), `1 + Ξ ι` is invertible on `F` with inverse `B_F` of norm `≤ 2`, the
inverse `B` of `DΓ_t(w)` on `E` satisfies `B ι = ι B_F`, and `B - I = ι Ξ'` with
`‖Ξ'‖_{E→F} ≤ 20 |t| C ‖w‖²`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (ι : F →L[ℂ] E) (S : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F)
  {C : ℝ} (hC : 0 ≤ C) (hι : ‖ι‖ ≤ 1) (hS : ∀ v : Fin 3 → E, ‖S v‖ ≤ C * ∏ i, ‖v i‖)

include hC hι hS in
theorem lie_plus_inverse (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    ∃ (Ξ : E →L[ℂ] F) (B : E →L[ℂ] E) (BF : F →L[ℂ] F) (Ξ' : E →L[ℂ] F),
      lieGammaD (lieT ι S) t w * B = 1 ∧ B * lieGammaD (lieT ι S) t w = 1 ∧ ‖B‖ ≤ 2 ∧
      ι.comp Ξ = lieGammaD (lieT ι S) t w - 1 ∧ ‖Ξ‖ ≤ 10 * |t| * C * ‖w‖ ^ 2 ∧
      (lieGammaD (lieT ι S) t w).comp ι = ι.comp (1 + Ξ.comp ι) ∧
      (1 + Ξ.comp ι) * BF = 1 ∧ BF * (1 + Ξ.comp ι) = 1 ∧ ‖BF‖ ≤ 2 ∧
      ι.comp BF = B.comp ι ∧ ι.comp Ξ' = B - 1 ∧ ‖Ξ'‖ ≤ 20 * |t| * C * ‖w‖ ^ 2 := by
  have hT := lieT_bound ι S hι hS
  obtain ⟨Ξ, hΞ, hΞn⟩ := exists_lieGammaD_sub ι S hC hι hS t w hq
  obtain ⟨B, hAB, hBA, hB2, -⟩ := lieGammaD_invertible (lieT ι S) hC hT t w hq
  set A := lieGammaD (lieT ι S) t w with hA
  have h0 : 0 ≤ 2 * |t| * C * ‖w‖ ^ 2 := by positivity
  have hΞh : ‖Ξ‖ ≤ 1 / 2 := by nlinarith
  have hXι : ‖Ξ.comp ι‖ ≤ 1 / 2 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖Ξ‖ * ‖ι‖ ≤ ‖Ξ‖ * 1 := mul_le_mul_of_nonneg_left hι (norm_nonneg _)
      _ ≤ 1 / 2 := by linarith
  obtain ⟨BF, hF1, hF2, hF3, -⟩ := neumann_inv (1 + Ξ.comp ι) (by
    rw [add_sub_cancel_left]; exact hXι)
  have hΞpt : ∀ v : E, ι (Ξ v) = A v - v := fun v => by
    have := DFunLike.congr_fun hΞ v
    simpa using this
  have hAι' : ∀ f : F, A (ι f) = ι (f + Ξ (ι f)) := fun f => by
    rw [map_add, hΞpt]; abel
  have hAι : A.comp ι = ι.comp (1 + Ξ.comp ι) := by
    ext f
    exact hAι' f
  have hF1pt : ∀ f : F, BF f + Ξ (ι (BF f)) = f := fun f => by
    have := DFunLike.congr_fun hF1 f
    simpa using this
  have hBApt : ∀ x : E, B (A x) = x := fun x => by
    have := DFunLike.congr_fun hBA x
    simpa using this
  have hιBpt : ∀ f : F, ι (BF f) = B (ι f) := fun f => by
    have h1 : A (ι (BF f)) = ι f := by rw [hAι', hF1pt]
    have h2 := hBApt (ι (BF f))
    rw [h1] at h2
    exact h2.symm
  have hιB : ι.comp BF = B.comp ι := by
    ext f
    exact hιBpt f
  refine ⟨Ξ, B, BF, -(BF.comp Ξ), hAB, hBA, hB2, hΞ, hΞn, hAι, hF1, hF2, hF3, hιB, ?_, ?_⟩
  · ext v
    show ι (-(BF (Ξ v))) = B v - v
    rw [map_neg, hιBpt, hΞpt, map_sub, hBApt]
    abel
  · rw [norm_neg]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖BF‖ * ‖Ξ‖ ≤ 2 * (10 * |t| * C * ‖w‖ ^ 2) :=
          mul_le_mul hF3 hΞn (norm_nonneg _) (by norm_num)
      _ = 20 * |t| * C * ‖w‖ ^ 2 := by ring

end KAM.Wave

end
