/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.Weighted.Parametric

/-!
# Planar quartic torsion: the complex time-Picard operator (package R2)

Blueprint P, Part 11b (`bpP:p11b:e-ode`, package R2).  For a map `v : ℂⁿ⁺¹ → ℂⁿ`, write a point of
`ℂⁿ⁺¹` as `ζ = (s, w)` (time `ζ 0`, space `fun i => ζ i.succ`) and set
`p11cPicardOp v ζ = w + s • ∫₀¹ v (σ s, w) dσ`.  This is the complex-time Picard operator
`w + ∫₀ˢ v (τ, w) dτ` written along the real segment `σ ↦ σ s`.  We prove that it preserves
holomorphy on the open "time-star-shaped" domains `p11cDom`, using the exact parametric-integral
declaration `KAM.Weighted.holomorphic_parametric_integral` (U5), and give the elementary sup-norm
estimate used for the Picard contraction.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace KAM.Planetary

variable {n : ℕ}

/-- The space coordinates `ζ ↦ (ζ 1, …, ζ n)` of a point of `ℂⁿ⁺¹`. -/
def p11cSp (n : ℕ) : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp] theorem p11cSp_apply (ζ : Fin (n + 1) → ℂ) (i : Fin n) : p11cSp n ζ i = ζ i.succ := rfl

/-- Multiplication of the time coordinate by a real scalar, the space coordinates fixed. -/
def p11cTimeScale (n : ℕ) (σ : ℝ) : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.id ℂ _ +
    ((σ : ℂ) - 1) • (ContinuousLinearMap.proj (0 : Fin (n + 1))).smulRight
      (Pi.single (0 : Fin (n + 1)) (1 : ℂ))

theorem p11cTimeScale_apply (σ : ℝ) (ζ : Fin (n + 1) → ℂ) :
    p11cTimeScale n σ ζ = ζ + (((σ : ℂ) - 1) * ζ 0) • Pi.single (0 : Fin (n + 1)) (1 : ℂ) := by
  simp [p11cTimeScale, smul_smul]

theorem p11cTimeScale_zero (σ : ℝ) (ζ : Fin (n + 1) → ℂ) : p11cTimeScale n σ ζ 0 = σ * ζ 0 := by
  simp [p11cTimeScale_apply]; ring

theorem p11cSp_timeScale (σ : ℝ) (ζ : Fin (n + 1) → ℂ) :
    p11cSp n (p11cTimeScale n σ ζ) = p11cSp n ζ := by
  ext i
  simp [p11cTimeScale_apply, Fin.succ_ne_zero]

theorem p11cTimeScale_one (ζ : Fin (n + 1) → ℂ) : p11cTimeScale n 1 ζ = ζ := by
  simp [p11cTimeScale_apply]

theorem continuous_p11cTimeScale_apply :
    Continuous fun p : ℝ × (Fin (n + 1) → ℂ) => p11cTimeScale n p.1 p.2 := by
  simp only [p11cTimeScale_apply]
  have h0 : Continuous fun p : ℝ × (Fin (n + 1) → ℂ) => p.2 0 := (continuous_apply 0).comp continuous_snd
  exact continuous_snd.add (((Complex.continuous_ofReal.comp continuous_fst).sub continuous_const).mul
    h0 |>.smul continuous_const)

theorem continuous_p11cTimeScale : Continuous fun σ : ℝ => p11cTimeScale n σ := by
  unfold p11cTimeScale
  exact continuous_const.add (((Complex.continuous_ofReal).sub continuous_const).smul continuous_const)

/-- The domain `|s| < T`, `‖w - c‖ < r` in `ℂⁿ⁺¹`. -/
def p11cDom (n : ℕ) (c : Fin n → ℂ) (T r : ℝ) : Set (Fin (n + 1) → ℂ) :=
  {ζ | ‖ζ 0‖ < T ∧ ‖p11cSp n ζ - c‖ < r}

theorem isOpen_p11cDom (c : Fin n → ℂ) (T r : ℝ) : IsOpen (p11cDom n c T r) := by
  refine IsOpen.inter (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const)
    (isOpen_lt (continuous_norm.comp ((p11cSp n).continuous.sub continuous_const))
      continuous_const)

theorem p11cTimeScale_mem {c : Fin n → ℂ} {T r σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1)
    {ζ : Fin (n + 1) → ℂ} (hζ : ζ ∈ p11cDom n c T r) : p11cTimeScale n σ ζ ∈ p11cDom n c T r := by
  refine ⟨?_, by simpa only [p11cSp_timeScale] using hζ.2⟩
  rw [p11cTimeScale_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.1]
  calc σ * ‖ζ 0‖ ≤ 1 * ‖ζ 0‖ := mul_le_mul_of_nonneg_right hσ.2 (norm_nonneg _)
    _ < T := by simpa using hζ.1

/-- The complex-time Picard operator `ζ = (s, w) ↦ w + s • ∫₀¹ v (σ s, w) dσ`. -/
def p11cPicardOp (v : (Fin (n + 1) → ℂ) → Fin n → ℂ) (ζ : Fin (n + 1) → ℂ) : Fin n → ℂ :=
  p11cSp n ζ + ζ 0 • ∫ σ in (0 : ℝ)..1, v (p11cTimeScale n σ ζ)

theorem p11c_continuousOn_fderiv {m : ℕ} {U : Set (Fin m → ℂ)} (hU : IsOpen U)
    {v : (Fin m → ℂ) → Fin n → ℂ} (hv : DifferentiableOn ℂ v U) :
    ContinuousOn (fun z => fderiv ℂ v z) U :=
  ContDiffOn.continuousOn_fderiv_of_isOpen
    ((analyticOnNhd_of_differentiableOn hU hv).contDiffOn (n := 1) hU.uniqueDiffOn) hU le_rfl

theorem p11c_integral_Icc_zero_one {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (g : ℝ → W) : ∫ x in Set.Icc (0 : Fin 1 → ℝ) 1, g (x 0) = ∫ σ in (0 : ℝ)..1, g σ := by
  have hpre : Set.Icc (0 : Fin 1 → ℝ) 1 =
      (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Icc (0 : ℝ) 1 := by
    ext x
    simp [Pi.le_def, Fin.forall_fin_one]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc, hpre]
  exact ((volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) (fun y => g y) (Set.Icc (0 : ℝ) 1))

theorem p11cPicardOp_differentiableOn {c : Fin n → ℂ} {T r : ℝ}
    {v : (Fin (n + 1) → ℂ) → Fin n → ℂ} (hv : DifferentiableOn ℂ v (p11cDom n c T r)) :
    DifferentiableOn ℂ (p11cPicardOp v) (p11cDom n c T r) := by
  set U := p11cDom n c T r with hUdef
  have hU : IsOpen U := isOpen_p11cDom c T r
  have hcont := p11c_continuousOn_fderiv hU hv
  have hmaps : ∀ x ∈ Set.Icc (0 : Fin 1 → ℝ) 1, ∀ ζ ∈ U, p11cTimeScale n (x 0) ζ ∈ U := by
    intro x hx ζ hζ
    refine p11cTimeScale_mem ⟨?_, ?_⟩ hζ
    · exact (Pi.le_def.1 hx.1) 0
    · exact (Pi.le_def.1 hx.2) 0
  have hc0 : Continuous fun y : (Fin 1 → ℝ) × (Fin (n + 1) → ℂ) => y.1 0 :=
    (continuous_apply (0 : Fin 1)).comp continuous_fst
  have hcC : Continuous fun y : (Fin 1 → ℝ) × (Fin (n + 1) → ℂ) =>
      p11cTimeScale n (y.1 0) y.2 :=
    continuous_p11cTimeScale_apply.comp (hc0.prodMk continuous_snd)
  have hmapsC : ContinuousOn (fun y : (Fin 1 → ℝ) × (Fin (n + 1) → ℂ) =>
      p11cTimeScale n (y.1 0) y.2) (Set.Icc (0 : Fin 1 → ℝ) 1 ×ˢ U) := hcC.continuousOn
  have hG : ContinuousOn (fun y : (Fin 1 → ℝ) × (Fin (n + 1) → ℂ) =>
      v (p11cTimeScale n (y.1 0) y.2)) (Set.Icc (0 : Fin 1 → ℝ) 1 ×ˢ U) :=
    hv.continuousOn.comp hmapsC fun y hy => hmaps y.1 hy.1 y.2 hy.2
  have hGd : ∀ x ∈ Set.Icc (0 : Fin 1 → ℝ) 1,
      DifferentiableOn ℂ (fun ζ => v (p11cTimeScale n (x 0) ζ)) U := fun x hx =>
    hv.comp (p11cTimeScale n (x 0)).differentiableOn (hmaps x hx)
  have hfd : ∀ y ∈ Set.Icc (0 : Fin 1 → ℝ) 1 ×ˢ U,
      fderiv ℂ (fun ζ => v (p11cTimeScale n (y.1 0) ζ)) y.2 =
        (fderiv ℂ v (p11cTimeScale n (y.1 0) y.2)).comp (p11cTimeScale n (y.1 0)) := by
    intro y hy
    have h1 : DifferentiableAt ℂ v (p11cTimeScale n (y.1 0) y.2) :=
      hv.differentiableAt (hU.mem_nhds (hmaps y.1 hy.1 y.2 hy.2))
    exact fderiv_comp y.2 h1 (p11cTimeScale n (y.1 0)).differentiableAt |>.trans
      (by rw [ContinuousLinearMap.fderiv])
  have hDG : ContinuousOn (fun y : (Fin 1 → ℝ) × (Fin (n + 1) → ℂ) =>
      fderiv ℂ (fun ζ => v (p11cTimeScale n (y.1 0) ζ)) y.2) (Set.Icc (0 : Fin 1 → ℝ) 1 ×ˢ U) := by
    refine ContinuousOn.congr (f := fun y : (Fin 1 → ℝ) × (Fin (n + 1) → ℂ) =>
      (fderiv ℂ v (p11cTimeScale n (y.1 0) y.2)).comp (p11cTimeScale n (y.1 0))) ?_ hfd
    refine ContinuousOn.clm_comp (hcont.comp hmapsC fun y hy => hmaps y.1 hy.1 y.2 hy.2) ?_
    exact (continuous_p11cTimeScale.comp hc0).continuousOn
  obtain ⟨hd, -⟩ := KAM.Weighted.holomorphic_parametric_integral (W := Fin n → ℂ)
    (isCompact_Icc) hU hG hGd hDG
  have hd' : DifferentiableOn ℂ (fun ζ => ∫ σ in (0 : ℝ)..1, v (p11cTimeScale n σ ζ)) U := by
    refine hd.congr fun ζ _ => ?_
    exact (p11c_integral_Icc_zero_one fun σ => v (p11cTimeScale n σ ζ)).symm
  exact ((p11cSp n).differentiableOn).add
    (((differentiable_apply (0 : Fin (n + 1))).differentiableOn).smul hd')

end KAM.Planetary
