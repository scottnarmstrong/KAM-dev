/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.CutoffScale

/-! # P11B smooth cutoff: iterated derivatives of a convolution

For a locally integrable `u` and a compactly supported `C^k` function `g` on `Fin n → ℝ`, the
`k`-th derivative of `u ⋆ g` is `u ⋆` the `k`-th derivative of `g` (evaluated on a fixed tuple of
directions).
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology Convolution
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

theorem selectionConv_iteratedFDeriv {u : (Fin n → ℝ) → ℝ} (hu : LocallyIntegrable u) :
    ∀ (k : ℕ) (g : (Fin n → ℝ) → ℝ), HasCompactSupport g → ContDiff ℝ k g →
      ∀ (y : Fin n → ℝ) (m : Fin k → (Fin n → ℝ)),
        iteratedFDeriv ℝ k (u ⋆[ContinuousLinearMap.mul ℝ ℝ] g) y m =
          ∫ z, u z * iteratedFDeriv ℝ k g (y - z) m := by
  intro k
  induction k with
  | zero =>
    intro g hc hg y m
    simp [iteratedFDeriv_zero_apply, convolution_def]
  | succ k ih =>
    intro g hc hg y m
    set L := ContinuousLinearMap.mul ℝ ℝ with hL
    have hconv : ContDiff ℝ ((k + 1 : ℕ) : ℕ∞) (u ⋆[L] g) :=
      hc.contDiff_convolution_right L hu (by exact_mod_cast hg)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k (u ⋆[L] g)) y :=
      (hconv.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) y
    rw [hd.iteratedFDeriv_succ_apply_left']
    set G : (Fin n → ℝ) → ℝ := fun z => iteratedFDeriv ℝ k g z (Fin.tail m) with hG
    have hgk : ContDiff ℝ (k : ℕ) g := hg.of_le (by exact_mod_cast Nat.le_succ k)
    have hG1 : (fun y => iteratedFDeriv ℝ k (u ⋆[L] g) y (Fin.tail m)) = u ⋆[L] G := by
      funext y
      rw [ih g hc hgk y, convolution_def]
      simp [hG, hL]
    rw [hG1]
    have hGc : ContDiff ℝ 1 G := by
      have h1 : ContDiff ℝ 1 (iteratedFDeriv ℝ k g) := hg.iteratedFDeriv_right
        (by rw [add_comm]; exact_mod_cast le_refl (k + 1))
      exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin n → ℝ) ℝ
        (Fin.tail m)).contDiff.comp h1
    have hGs : HasCompactSupport G :=
      (hc.iteratedFDeriv (𝕜 := ℝ) k).comp_left (g := fun A :
        ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ℝ => A (Fin.tail m)) (by simp)
    have hfd := (hGs.hasFDerivAt_convolution_right L hu hGc y).fderiv
    rw [hfd]
    have hex := hGs.fderiv (𝕜 := ℝ)
    have hint : Integrable (fun t => (L.precompR (Fin n → ℝ) (u t) (fderiv ℝ G (y - t)))) := by
      have := (hex.convolutionExists_right (L.precompR (Fin n → ℝ)) hu
        (hGc.continuous_fderiv one_ne_zero) y)
      exact this
    rw [convolution_def, ContinuousLinearMap.integral_apply hint]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have hdz : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) (y - z) :=
      (hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) _
    have h2 : fderiv ℝ G (y - z) (m 0) = iteratedFDeriv ℝ (k + 1) g (y - z) m := by
      rw [hdz.iteratedFDeriv_succ_apply_left']
    simp [hL, h2]

end KAM.Planetary
