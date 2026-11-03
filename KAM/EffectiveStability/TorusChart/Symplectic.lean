/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.TorusChart.Deriv
public import KAM.EffectiveStability.TorusChart.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symplecticity of the cotangent-lift chart (track B, B5-CHART)

`torusChartMap_symplectic`: `ω (DΨ w a) (DΨ w b) = ω a b` for the frozen form, from the Lagrangian
condition (`(Dx)ᵀ Dv` symmetric), the symmetry of the second derivative of `x`, and the
differentiated relation `(Dx)^{-1} Dx = 1`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Matrix

variable {n : ℕ} {u v : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}

/-- The Lagrangian condition in vector form. -/
theorem torusChart_lagrangian_vec (h : TorusChartData u v κ) (φ a b : Fin n → ℝ) :
    (fderiv ℝ (torusChartX u) φ a) ⬝ᵥ (fderiv ℝ v φ b) =
      (fderiv ℝ (torusChartX u) φ b) ⬝ᵥ (fderiv ℝ v φ a) := by
  set Jv : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => fderiv ℝ v φ (Pi.single j 1) i
  set Q := (torusChartJac u φ)ᵀ * Jv with hQ
  have hQs : Qᵀ = Q := by
    ext i j
    simp only [Matrix.transpose_apply, hQ, Matrix.mul_apply, Matrix.transpose_apply]
    simpa [Jv, torusChartJac, mul_comm] using (h.lagrangian φ j i)
  have key : ∀ a b : Fin n → ℝ, (fderiv ℝ (torusChartX u) φ a) ⬝ᵥ (fderiv ℝ v φ b) =
      a ⬝ᵥ (Q *ᵥ b) := fun a b => by
    rw [← torusChartJac_mulVec, clm_apply_eq_mulVec (fderiv ℝ v φ) b, ← Matrix.vecMul_transpose
      (torusChartJac u φ) a, ← Matrix.dotProduct_mulVec, hQ, ← Matrix.mulVec_mulVec]
  rw [key, key, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hQs, dotProduct_comm]

/-- The entrywise derivative of `Dx` is the second derivative of `x`. -/
theorem torusChartDJac_mulVec (h : TorusBaseData u κ) (φ a b : Fin n → ℝ) :
    torusChartDJac u φ a *ᵥ b = fderiv ℝ (fderiv ℝ (torusChartX u)) φ a b := by
  have hg : DifferentiableAt ℝ (fderiv ℝ (torusChartX u)) φ :=
    ((torusChartX_contDiff h).fderiv_right (m := 2) (by norm_num)).differentiable
      (by norm_num) φ
  have : torusChartDJac u φ a =
      Matrix.of fun i l => (fderiv ℝ (fderiv ℝ (torusChartX u)) φ a) (Pi.single l 1) i := by
    ext i l
    simp only [torusChartDJac, torusChartJac, Matrix.of_apply]
    have hL := ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single l 1))).hasFDerivAt.comp φ
      hg.hasFDerivAt
    change fderiv ℝ ((⇑((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.apply ℝ (Fin n → ℝ) (Pi.single l 1)))) ∘ fderiv ℝ (torusChartX u))
      φ a = _
    rw [hL.fderiv]
    simp
  rw [this, ← clm_apply_eq_mulVec]

/-- Differentiating `(Dx)^{-1} Dx = 1`. -/
theorem torusChart_diff_identity (h : TorusBaseData u κ) (φ a : Fin n → ℝ) :
    (torusChartDInvT u φ a)ᵀ * torusChartJac u φ + (torusChartInvT u φ)ᵀ * torusChartDJac u φ a
      = 0 := by
  ext k l
  have hBd : ∀ i, DifferentiableAt ℝ (fun ψ => torusChartInvT u ψ i k) φ := fun i =>
    ((torusChartInvT_contDiff h i k).differentiable (by norm_num)) φ
  have hAd : ∀ i, DifferentiableAt ℝ (fun ψ => torusChartJac u ψ i l) φ := fun i =>
    ((torusChartJac_contDiff h i l).differentiable (by norm_num)) φ
  have hs : HasFDerivAt (fun ψ => ∑ i, torusChartInvT u ψ i k * torusChartJac u ψ i l)
      (∑ i, (torusChartInvT u φ i k • fderiv ℝ (fun ψ => torusChartJac u ψ i l) φ +
        torusChartJac u φ i l • fderiv ℝ (fun ψ => torusChartInvT u ψ i k) φ)) φ :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hBd i).hasFDerivAt.mul (hAd i).hasFDerivAt
  have hc : (fun ψ => ∑ i, torusChartInvT u ψ i k * torusChartJac u ψ i l) =
      fun _ => if k = l then (1 : ℝ) else 0 := funext fun ψ => torusChartInvT_entry h ψ k l
  rw [hc] at hs
  have := congrArg (fun L => L a) (hs.unique (hasFDerivAt_const _ _))
  simp only [_root_.zero_apply] at this
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul] at this
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, torusChartDInvT,
    torusChartDJac, Matrix.of_apply, Matrix.zero_apply]
  rw [← this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **Symplecticity** of the cotangent-lift chart `torusChartMap`. -/
theorem torusChartMap_symplectic (h : TorusChartData u v κ) (w a b : (Fin n → ℝ) × (Fin n → ℝ)) :
    KAM.symplecticForm (fderiv ℝ (torusChartMap u v) w a) (fderiv ℝ (torusChartMap u v) w b) =
      KAM.symplecticForm a b := by
  have hb := h.toTorusBaseData
  rw [symplecticForm_eq_dot, symplecticForm_eq_dot, torusChartMap_fderiv_fst h,
    torusChartMap_fderiv_fst h, torusChartMap_fderiv_snd h, torusChartMap_fderiv_snd h,
    ← torusChartJac_mulVec, ← torusChartJac_mulVec]
  have hsx : IsSymmSndFDerivAt ℝ (torusChartX u) w.1 :=
    ((torusChartX_contDiff hb).contDiffAt).isSymmSndFDerivAt (by simp; norm_num)
  refine torusChart_symplectic_algebra (torusChartJac u w.1) (torusChartInvT u w.1)
    (torusChartDInvT u w.1 a.1) (torusChartDInvT u w.1 b.1) (torusChartDJac u w.1 a.1)
    (torusChartDJac u w.1 b.1) a.1 a.2 b.1 b.2 _ _ w.2 ?_ (torusChart_diff_identity hb _ _)
    (torusChart_diff_identity hb _ _) ?_ ?_
  · have := torusChartInvT_entry hb w.1
    ext k l
    simpa [Matrix.mul_apply, Matrix.one_apply] using this k l
  · rw [torusChartDJac_mulVec hb, torusChartDJac_mulVec hb]; exact hsx.eq _ _
  · rw [torusChartJac_mulVec, torusChartJac_mulVec]
    exact torusChart_lagrangian_vec h _ _ _

end KAM.EffectiveStability
