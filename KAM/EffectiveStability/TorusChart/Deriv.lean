/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChart.Map

/-!
# The derivative of the cotangent-lift chart (track B, B5-CHART)

`D Ψ (φ, J) (a₁, a₂) = (Dx a₁, Dv a₁ + (Dx)^{-T} a₂ + (D_{a₁} (Dx)^{-T}) J)`, with the
entrywise directional derivatives `torusChartDInvT`, and the relations between the derivatives of
`Dx` and `(Dx)^{-T}` obtained by differentiating `(Dx)^{-1} Dx = 1`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Matrix

variable {n : ℕ} {u v : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}

/-- Entrywise directional derivative of `(Dx)^{-T}`. -/
def torusChartDInvT (u : (Fin n → ℝ) → (Fin n → ℝ)) (φ a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => fderiv ℝ (fun ψ => torusChartInvT u ψ i k) φ a

/-- Entrywise directional derivative of `Dx`. -/
def torusChartDJac (u : (Fin n → ℝ) → (Fin n → ℝ)) (φ a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i l => fderiv ℝ (fun ψ => torusChartJac u ψ i l) φ a

theorem torusChartMap_differentiable (h : TorusChartData u v κ) :
    Differentiable ℝ (torusChartMap u v) :=
  (torusChartMap_contDiff h).differentiable (by norm_num)

theorem torusChartMap_fderiv_fst (h : TorusChartData u v κ) (w a : (Fin n → ℝ) × (Fin n → ℝ)) :
    (fderiv ℝ (torusChartMap u v) w a).1 = fderiv ℝ (torusChartX u) w.1 a.1 := by
  have h1 := (torusChartMap_differentiable h w).hasFDerivAt.fst
  have hx : DifferentiableAt ℝ (torusChartX u) w.1 :=
    ((torusChartX_contDiff h.toTorusBaseData).differentiable (by norm_num)) w.1
  have h2 : HasFDerivAt (fun w : (Fin n → ℝ) × (Fin n → ℝ) => (torusChartMap u v w).1)
      ((fderiv ℝ (torusChartX u) w.1).comp (ContinuousLinearMap.fst ℝ _ _)) w :=
    hx.hasFDerivAt.comp w hasFDerivAt_fst
  have := congrArg (fun L => L a) (h1.unique h2)
  simpa using this

theorem torusChartMap_fderiv_snd (h : TorusChartData u v κ) (w a : (Fin n → ℝ) × (Fin n → ℝ)) :
    (fderiv ℝ (torusChartMap u v) w a).2 =
      fderiv ℝ v w.1 a.1 + torusChartInvT u w.1 *ᵥ a.2 + torusChartDInvT u w.1 a.1 *ᵥ w.2 := by
  funext i
  have h1 := hasFDerivAt_pi'.mp (torusChartMap_differentiable h w).hasFDerivAt.snd i
  have hv : HasFDerivAt (fun w : (Fin n → ℝ) × (Fin n → ℝ) => v w.1 i)
      ((ContinuousLinearMap.proj i).comp
        ((fderiv ℝ v w.1).comp (ContinuousLinearMap.fst ℝ _ _))) w := by
    have := ((h.vSmooth.differentiable (by norm_num)) w.1).hasFDerivAt.comp w hasFDerivAt_fst
    exact hasFDerivAt_pi'.mp this i
  have hB : ∀ k, HasFDerivAt
      (fun w : (Fin n → ℝ) × (Fin n → ℝ) => torusChartInvT u w.1 i k * w.2 k)
      (torusChartInvT u w.1 i k •
          (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℝ _ _) +
        w.2 k • (fderiv ℝ (fun ψ => torusChartInvT u ψ i k) w.1).comp
          (ContinuousLinearMap.fst ℝ _ _)) w := fun k => by
    have hb := (((torusChartInvT_contDiff h.toTorusBaseData i k).differentiable
      (by norm_num)) w.1).hasFDerivAt.comp w hasFDerivAt_fst
    have hs := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp w
      (hasFDerivAt_snd (𝕜 := ℝ) (E := Fin n → ℝ) (F := Fin n → ℝ) (p := w))
    exact hb.mul hs
  have h2 := hv.add (HasFDerivAt.sum (u := Finset.univ) fun k _ => hB k)
  have h3 := h1.unique (by
    convert h2 using 1
    funext w'
    simp [torusChartMap, Matrix.mulVec, dotProduct])
  have := congrArg (fun L => L a) h3
  simp [Finset.sum_add_distrib] at this
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, torusChartDInvT, Matrix.of_apply]
  rw [this]
  simp [mul_comm]
  ring

end KAM.EffectiveStability
