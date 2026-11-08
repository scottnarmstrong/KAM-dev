/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The base map `x = id + u` of a Lagrangian graph torus (track B, B5-CHART)

For periodic `u` with `‖Du‖ ≤ κ < 1` the map `x φ = φ + u φ` of `Fin n → ℝ` is a bijection,
with Lipschitz inverse `torusChartXinv` (a contraction fixed point `φ = y - u φ`), commuting
with the lattice shifts; `Dx φ` is invertible with `‖(Dx φ)⁻¹‖ ≤ 1 / (1 - κ)`, and the inverse
is as smooth as `u`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set Filter
open scoped Topology NNReal

variable {n : ℕ}

/-- The base map `φ ↦ φ + u φ` of the chart. -/
def torusChartX (u : (Fin n → ℝ) → (Fin n → ℝ)) (φ : Fin n → ℝ) : Fin n → ℝ := φ + u φ

/-- The inverse of the base map (a genuine inverse under the contraction hypothesis). -/
def torusChartXinv (u : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) : Fin n → ℝ :=
  Function.invFun (torusChartX u) y

/-- The standing hypotheses on the base map: smooth, `κ`-contractive displacement. -/
structure TorusBaseData (u : (Fin n → ℝ) → (Fin n → ℝ)) (κ : ℝ) : Prop where
  baseSmooth : ContDiff ℝ 3 u
  baseContract : κ < 1
  baseBound : ∀ φ, ‖fderiv ℝ u φ‖ ≤ κ

variable {u : (Fin n → ℝ) → (Fin n → ℝ)} {κ : ℝ}

theorem torusChartX_lipschitz_u (h : TorusBaseData u κ) :
    LipschitzWith (Real.toNNReal κ) u := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact fun φ => (h.baseSmooth.differentiable (by norm_num)) φ
  · intro φ
    rw [← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ (le_trans (norm_nonneg _) (h.baseBound 0))]
    exact h.baseBound φ

theorem torusChartX_kappa_nonneg (h : TorusBaseData u κ) : 0 ≤ κ :=
  le_trans (norm_nonneg _) (h.baseBound 0)

theorem torusChartX_dist_lower (h : TorusBaseData u κ) (φ ψ : Fin n → ℝ) :
    (1 - κ) * ‖φ - ψ‖ ≤ ‖torusChartX u φ - torusChartX u ψ‖ := by
  have hl := (torusChartX_lipschitz_u h).dist_le_mul φ ψ
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (torusChartX_kappa_nonneg h)] at hl
  have : torusChartX u φ - torusChartX u ψ = (φ - ψ) + (u φ - u ψ) := by
    simp [torusChartX]; abel
  rw [this]
  have := norm_sub_norm_le (φ - ψ) (-(u φ - u ψ))
  rw [sub_neg_eq_add, norm_neg] at this
  nlinarith

theorem torusChartX_injective (h : TorusBaseData u κ) : Function.Injective (torusChartX u) := by
  intro φ ψ hφψ
  have := torusChartX_dist_lower h φ ψ
  rw [hφψ, sub_self, norm_zero] at this
  have h1 : 0 < 1 - κ := by linarith [h.baseContract]
  have : ‖φ - ψ‖ ≤ 0 := by nlinarith [norm_nonneg (φ - ψ)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

theorem torusChartX_surjective (h : TorusBaseData u κ) : Function.Surjective (torusChartX u) := by
  intro y
  have hK : (Real.toNNReal κ) < 1 := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (torusChartX_kappa_nonneg h)]
    simpa using h.baseContract
  have hc : ContractingWith (Real.toNNReal κ) (fun φ => y - u φ) :=
    ⟨hK, by
      have := (torusChartX_lipschitz_u h)
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have := this.dist_le_mul a b
      simpa [dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev] using this⟩
  refine ⟨hc.fixedPoint _, ?_⟩
  have hp : y - u (hc.fixedPoint _) = hc.fixedPoint _ := hc.fixedPoint_isFixedPt
  exact (sub_eq_iff_eq_add.mp hp).symm

theorem torusChartXinv_left (h : TorusBaseData u κ) (φ : Fin n → ℝ) :
    torusChartXinv u (torusChartX u φ) = φ :=
  Function.leftInverse_invFun (torusChartX_injective h) φ

theorem torusChartXinv_right (h : TorusBaseData u κ) (y : Fin n → ℝ) :
    torusChartX u (torusChartXinv u y) = y :=
  Function.invFun_eq (torusChartX_surjective h y)

theorem torusChartXinv_lipschitz (h : TorusBaseData u κ) (y z : Fin n → ℝ) :
    (1 - κ) * ‖torusChartXinv u y - torusChartXinv u z‖ ≤ ‖y - z‖ := by
  have := torusChartX_dist_lower h (torusChartXinv u y) (torusChartXinv u z)
  rwa [torusChartXinv_right h, torusChartXinv_right h] at this

theorem torusChartXinv_continuous (h : TorusBaseData u κ) :
    Continuous (torusChartXinv u) := by
  have h1 : 0 < 1 - κ := by linarith [h.baseContract]
  refine (LipschitzWith.of_dist_le_mul (K := (1 - κ)⁻¹.toNNReal) fun y z => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.mpr h1.le)]
  have := torusChartXinv_lipschitz h y z
  rw [inv_mul_eq_div, le_div_iff₀ h1]
  linarith

/-- Periodicity of `u` under the lattice shifts. -/
def TorusPeriodic (u : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ (φ : Fin n → ℝ) (k : Fin n → ℤ), u (φ + fun i => (k i : ℝ)) = u φ

theorem torusChartX_shift (hp : TorusPeriodic u) (φ : Fin n → ℝ) (k : Fin n → ℤ) :
    torusChartX u (φ + fun i => (k i : ℝ)) = torusChartX u φ + fun i => (k i : ℝ) := by
  unfold torusChartX
  rw [hp φ k]; abel

theorem torusChartXinv_shift (h : TorusBaseData u κ) (hp : TorusPeriodic u)
    (y : Fin n → ℝ) (k : Fin n → ℤ) :
    torusChartXinv u (y + fun i => (k i : ℝ)) = torusChartXinv u y + fun i => (k i : ℝ) := by
  apply torusChartX_injective h
  rw [torusChartX_shift hp, torusChartXinv_right h, torusChartXinv_right h]

theorem torusChartX_contDiff (h : TorusBaseData u κ) : ContDiff ℝ 3 (torusChartX u) :=
  contDiff_id.add h.baseSmooth

theorem torusChartX_fderiv (h : TorusBaseData u κ) (φ : Fin n → ℝ) :
    fderiv ℝ (torusChartX u) φ = ContinuousLinearMap.id ℝ _ + fderiv ℝ u φ := by
  unfold torusChartX
  exact ((hasFDerivAt_id φ).add (h.baseSmooth.differentiable (by norm_num) φ).hasFDerivAt).fderiv

theorem torusChartDx_lower (h : TorusBaseData u κ) (φ y : Fin n → ℝ) :
    (1 - κ) * ‖y‖ ≤ ‖fderiv ℝ (torusChartX u) φ y‖ := by
  rw [torusChartX_fderiv h]
  simp only [add_apply, ContinuousLinearMap.id_apply]
  have h1 := (fderiv ℝ u φ).le_opNorm y
  have h2 := h.baseBound φ
  have := norm_sub_norm_le y (-(fderiv ℝ u φ y))
  rw [sub_neg_eq_add, norm_neg] at this
  nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_right h2 (norm_nonneg y)]

/-- `Dx φ` is a continuous linear equivalence. -/
def torusChartDxEquiv (h : TorusBaseData u κ) (φ : Fin n → ℝ) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ (torusChartX u) φ).toLinearMap (by
      intro a b hab
      have h1 : 0 < 1 - κ := by linarith [h.baseContract]
      have hab' : fderiv ℝ (torusChartX u) φ (a - b) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr hab
      have := torusChartDx_lower h φ (a - b)
      rw [hab', norm_zero] at this
      have : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)))

theorem torusChartDxEquiv_coe (h : TorusBaseData u κ) (φ y : Fin n → ℝ) :
    torusChartDxEquiv h φ y = fderiv ℝ (torusChartX u) φ y := by
  simp [torusChartDxEquiv]

/-- `‖(Dx φ)⁻¹‖ ≤ 1 / (1 - κ)`. -/
theorem torusChartDxEquiv_symm_norm (h : TorusBaseData u κ) (φ : Fin n → ℝ) :
    ‖((torusChartDxEquiv h φ).symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ 1 / (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith [h.baseContract]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have := torusChartDx_lower h φ ((torusChartDxEquiv h φ).symm z)
  rw [← torusChartDxEquiv_coe h, ContinuousLinearEquiv.apply_symm_apply] at this
  rw [one_div, inv_mul_eq_div, le_div_iff₀ h1]
  simp only [ContinuousLinearEquiv.coe_coe]
  linarith

/-- The inverse of the base map is `C³`. -/
theorem torusChartXinv_contDiff (h : TorusBaseData u κ) : ContDiff ℝ 3 (torusChartXinv u) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  set a := torusChartXinv u y with ha
  have hy : y = torusChartX u a := (torusChartXinv_right h y).symm
  have hcd : ContDiffAt ℝ 3 (torusChartX u) a := (torusChartX_contDiff h).contDiffAt
  have e : ((torusChartDxEquiv h a : (Fin n → ℝ) ≃L[ℝ] _) :
      (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ (torusChartX u) a := by
    exact ContinuousLinearMap.ext fun y => torusChartDxEquiv_coe h a y
  have hf' : HasFDerivAt (torusChartX u) ((torusChartDxEquiv h a : (Fin n → ℝ) ≃L[ℝ] _) :
      (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) a := by
    rw [e]; exact ((torusChartX_contDiff h).differentiable (by norm_num) a).hasFDerivAt
  have hloc := hcd.to_localInverse hf' (by norm_num)
  have hstrict := hcd.hasStrictFDerivAt' hf' (by norm_num)
  have huniq := hstrict.localInverse_unique
    (g := torusChartXinv u) (Eventually.of_forall fun φ => torusChartXinv_left h φ)
  rw [← hy] at hloc huniq
  exact hloc.congr_of_eventuallyEq (huniq.mono fun z hz => hz)

end KAM.EffectiveStability
