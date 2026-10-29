/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Equation
public import KAM.Kepler.EquationComplex

/-!
# The Kepler tubes

The two instances of the complex Kepler contraction `KeplerData` / `keplerSol`
(`KAM.Kepler.EquationComplex`):

* the regular tube `regularTube = {|Im λ| < 1/4, |v₀| + |v₁| < 1/4}` with strip `|Im F| ≤ 1`
  (`a = v₀, b = v₁, c = λ`, `bpP:p7:regular-kepler` (b)): the holomorphic solution `keplerLongC`,
  its real points (`keplerLong`), the `2π`-shift, the three derivative formulas and the sharp
  Jacobian bound `1 - cosh 1 / 4 ≤ |J|`;
* the thin tube `keplerTube e₁` around the real eccentricities `[-e₁, e₁]` with
  `a = e, b = 0, c = ℓ` and strip `|Im u| ≤ y₀` (`bpI:p7:kepler-eq`): the holomorphic eccentric
  anomaly `eccAnomC`, its real points (`eccAnom`), the `2π`-shift, `eccAnomC (ℓ, 0) = ℓ` and the
  derivatives `∂_ℓ u`, `∂_e u`.

The numerical helper `cosh_one_lt : cosh 1 < 1.55` (so that the contraction constant is `0.39`
and the Jacobian bound exceeds `3/5`) is proved first.
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff Topology

namespace KAM.Kepler

open KAM KAM.Planetary

section Equation

/-! ### Numerical helper -/

/-- Numerical helper: `cosh 1 < 1.55`, so the contraction constant `0.39` and `3/5` hold. -/
theorem cosh_one_lt : Real.cosh 1 < 1.55 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_one_gt_d9
  have h3 : (Real.exp 1)⁻¹ < 0.37 := by
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    have : (0.37 : ℝ)⁻¹ < 2.7182818283 := by norm_num
    linarith
  rw [Real.cosh_eq, Real.exp_neg]
  linarith

/-! ### The regular tube (`bpP:p7:regular-kepler` (b)) -/

/-- `bpP:p7:regular-kepler` (b): the tube `N₀`, strip `|Im F| ≤ 1`. -/
def regularTube : Set (ℂ × (Fin 2 → ℂ)) := {x | |x.1.im| < 1 / 4 ∧ ‖x.2 0‖ + ‖x.2 1‖ < 1 / 4}

/-- The complex solution `F(λ, v)` of the regular Kepler equation on `regularTube`. -/
def keplerLongC (x : ℂ × (Fin 2 → ℂ)) : ℂ := keplerSol 1 (x.2 0) (x.2 1) x.1

namespace Tube

/-- `sinh y ≤ y cosh y` for `y ≥ 0` (`tanh y ≤ y`). -/
theorem sinh_le_mul_cosh {y : ℝ} (hy : 0 ≤ y) : Real.sinh y ≤ y * Real.cosh y := by
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y * Real.cosh y - Real.sinh y) (x * Real.sinh x) x := by
    intro x
    exact (((hasDerivAt_id' x).mul (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x)).congr_deriv (by ring)
  have hmono : MonotoneOn (fun y : ℝ => y * Real.cosh y - Real.sinh y) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici, Set.mem_Ioi] at hx
    rw [(hd x).deriv]
    exact mul_nonneg hx.le (Real.sinh_pos_iff.2 hx).le
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simp only [zero_mul, Real.sinh_zero, sub_zero] at this
  linarith

theorem isOpen_regularTube : IsOpen regularTube := by
  have h1 : IsOpen {x : ℂ × (Fin 2 → ℂ) | |x.1.im| < 1 / 4} :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp continuous_fst)) continuous_const
  have h2 : IsOpen {x : ℂ × (Fin 2 → ℂ) | ‖x.2 0‖ + ‖x.2 1‖ < 1 / 4} :=
    isOpen_lt (by fun_prop) continuous_const
  exact h1.inter h2

/-- The coordinate projections of the Pi factor are continuous linear maps. -/
def coordCLM (i : Fin 2) : ℂ × (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).comp
    (ContinuousLinearMap.snd ℂ ℂ (Fin 2 → ℂ))

theorem coordCLM_apply (i : Fin 2) (x : ℂ × (Fin 2 → ℂ)) : coordCLM i x = x.2 i := rfl

theorem fderiv_coord (i : Fin 2) (x v : ℂ × (Fin 2 → ℂ)) :
    fderiv ℂ (fun y : ℂ × (Fin 2 → ℂ) => y.2 i) x v = v.2 i := by
  have h : HasFDerivAt (fun y : ℂ × (Fin 2 → ℂ) => y.2 i) (coordCLM i) x :=
    (coordCLM i).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem fderiv_first (x v : ℂ × (Fin 2 → ℂ)) :
    fderiv ℂ (fun y : ℂ × (Fin 2 → ℂ) => y.1) x v = v.1 := by
  have h : HasFDerivAt (fun y : ℂ × (Fin 2 → ℂ) => y.1)
      (ContinuousLinearMap.fst ℂ ℂ (Fin 2 → ℂ)) x :=
    (ContinuousLinearMap.fst ℂ ℂ (Fin 2 → ℂ)).hasFDerivAt
  rw [h.fderiv]
  rfl

/-- The contraction data of the regular tube: strip `|Im F| ≤ 1`, constant `0.39`. -/
theorem keplerData_regular :
    KeplerData regularTube (fun x : ℂ × (Fin 2 → ℂ) => x.2 0) (fun x => x.2 1) (fun x => x.1)
      1 (39 / 100) where
  isOpen := isOpen_regularTube
  analytic_a := fun x _ => (coordCLM 0).analyticAt x
  analytic_b := fun x _ => (coordCLM 1).analyticAt x
  analytic_c := fun x _ => analyticAt_fst
  y₀_pos := one_pos
  κ_lt := by norm_num
  invariant := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    have hs : 0 ≤ Real.sinh 1 := Real.sinh_nonneg_iff.2 zero_le_one
    have hc : 0 ≤ Real.cosh 1 := (Real.cosh_pos 1).le
    have hre : |(x.2 0).re| + |(x.2 1).re| ≤ ‖x.2 0‖ + ‖x.2 1‖ :=
      add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
    have him : |(x.2 0).im| + |(x.2 1).im| ≤ ‖x.2 0‖ + ‖x.2 1‖ :=
      add_le_add (Complex.abs_im_le_norm _) (Complex.abs_im_le_norm _)
    have e1 := mul_le_mul_of_nonneg_right hre hs
    have e2 := mul_le_mul_of_nonneg_right him hc
    have he : Real.sinh 1 + Real.cosh 1 = Real.exp 1 := Real.sinh_add_cosh 1
    have hexp := Real.exp_one_lt_d9
    have e3 : (‖x.2 0‖ + ‖x.2 1‖) * Real.exp 1 ≤ 1 / 4 * Real.exp 1 :=
      mul_le_mul_of_nonneg_right h2.le (Real.exp_pos 1).le
    have : (‖x.2 0‖ + ‖x.2 1‖) * Real.exp 1 =
        (‖x.2 0‖ + ‖x.2 1‖) * Real.sinh 1 + (‖x.2 0‖ + ‖x.2 1‖) * Real.cosh 1 := by
      rw [← he]; ring
    show |x.1.im| + (|(x.2 0).re| + |(x.2 1).re|) * Real.sinh 1
      + (|(x.2 0).im| + |(x.2 1).im|) * Real.cosh 1 < 1
    linarith
  contraction := by
    intro x hx
    have hc : 0 ≤ Real.cosh 1 := (Real.cosh_pos 1).le
    have e1 : (‖x.2 0‖ + ‖x.2 1‖) * Real.cosh 1 ≤ 1 / 4 * Real.cosh 1 :=
      mul_le_mul_of_nonneg_right hx.2.le hc
    have := cosh_one_lt
    show (‖x.2 0‖ + ‖x.2 1‖) * Real.cosh 1 ≤ 39 / 100
    norm_num at this
    linarith

theorem keplerLongC_spec {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube) :
    |(keplerLongC x).im| ≤ 1 ∧ keplerOp (x.2 0) (x.2 1) (keplerLongC x) = x.1 ∧
      ∀ G : ℂ, |G.im| ≤ 1 → keplerOp (x.2 0) (x.2 1) G = x.1 → G = keplerLongC x :=
  keplerSol_spec keplerData_regular hx

theorem keplerLongC_analyticOnNhd : AnalyticOnNhd ℂ keplerLongC regularTube :=
  keplerSol_analyticOnNhd keplerData_regular

/-- The sharp lower bound of the Jacobian denominator on the regular tube. -/
theorem jac_bound_aux {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube) :
    1 - Real.cosh 1 / 4 ≤
      ‖1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x)‖ := by
  obtain ⟨hs, -, -⟩ := keplerLongC_spec hx
  have hcon : (‖x.2 0‖ + ‖x.2 1‖) * Real.cosh 1 ≤ Real.cosh 1 / 4 :=
    calc (‖x.2 0‖ + ‖x.2 1‖) * Real.cosh 1 ≤ 1 / 4 * Real.cosh 1 :=
          mul_le_mul_of_nonneg_right hx.2.le (Real.cosh_pos 1).le
      _ = Real.cosh 1 / 4 := by ring
  have hd := EqC.norm_dfix_le hcon hs
  have h1 : ‖(1 : ℂ)‖ - ‖x.2 0 * Complex.cos (keplerLongC x) + x.2 1 * Complex.sin (keplerLongC x)‖
      ≤ ‖1 - (x.2 0 * Complex.cos (keplerLongC x) + x.2 1 * Complex.sin (keplerLongC x))‖ :=
    norm_sub_norm_le _ _
  rw [norm_one] at h1
  rw [sub_sub]
  linarith

theorem jac_ne_zero {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube) :
    1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x) ≠ 0 := by
  intro h
  have h1 := jac_bound_aux hx
  rw [h, norm_zero] at h1
  have := cosh_one_lt
  norm_num at this
  linarith

/-- Implicit differentiation of the regular Kepler equation in a direction `v`. -/
theorem fderiv_keplerLongC_mul {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube)
    (v : ℂ × (Fin 2 → ℂ)) :
    fderiv ℂ keplerLongC x v *
        (1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x)) =
      v.2 0 * Complex.sin (keplerLongC x) - v.2 1 * Complex.cos (keplerLongC x) + v.1 := by
  have h := keplerSol_fderiv keplerData_regular hx v
  rw [fderiv_coord, fderiv_coord, fderiv_first] at h
  exact h

theorem fderiv_keplerLongC_eq {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube)
    (v : ℂ × (Fin 2 → ℂ)) :
    fderiv ℂ keplerLongC x v =
      (v.2 0 * Complex.sin (keplerLongC x) - v.2 1 * Complex.cos (keplerLongC x) + v.1) /
        (1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x)) :=
  (eq_div_iff (jac_ne_zero hx)).2 (fderiv_keplerLongC_mul hx v)

theorem hasFDerivAt_keplerLongC {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube) :
    HasFDerivAt keplerLongC (fderiv ℂ keplerLongC x) x :=
  (keplerLongC_analyticOnNhd x hx).differentiableAt.hasFDerivAt

end Tube

theorem regularKepler_complex :
    DifferentiableOn ℂ keplerLongC regularTube ∧
    (∀ x ∈ regularTube, |(keplerLongC x).im| ≤ 1 ∧
      keplerOp (x.2 0) (x.2 1) (keplerLongC x) = x.1 ∧
      3 / 5 < ‖1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x)‖) ∧
    (∀ x ∈ regularTube, ∀ G : ℂ, |G.im| ≤ 1 → keplerOp (x.2 0) (x.2 1) G = x.1 →
      G = keplerLongC x) := by
  refine ⟨Tube.keplerLongC_analyticOnNhd.differentiableOn, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨h1, h2, -⟩ := Tube.keplerLongC_spec hx
    have h3 := Tube.jac_bound_aux hx
    have h4 := cosh_one_lt
    norm_num at h4
    exact ⟨h1, h2, by linarith⟩
  · exact (Tube.keplerLongC_spec hx).2.2

theorem keplerLongC_ofReal {lam : ℝ} {v : Fin 2 → ℝ} (h : (lam : ℂ) ∈ {z : ℂ | |z.im| < 1 / 4})
    (hv : |v 0| + |v 1| < 1 / 4) :
    keplerLongC ((lam : ℂ), fun i => (v i : ℂ)) = (keplerLong lam v : ℂ) := by
  have hmem : ((lam : ℂ), fun i => (v i : ℂ)) ∈ regularTube := by
    refine ⟨h, ?_⟩
    simpa [Complex.norm_real] using hv
  have hpl : planeLength v < 1 := by
    have hsq : planeSq v ≤ (|v 0| + |v 1|) ^ 2 := by
      simp only [planeSq, Fin.sum_univ_two, sq_abs, add_sq]
      nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_mul_abs_self (v 0), abs_mul_abs_self (v 1)]
    unfold planeLength
    rw [Real.sqrt_lt' one_pos]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]
  have hop : keplerOp ((v 0 : ℝ) : ℂ) ((v 1 : ℝ) : ℂ) ((keplerLong lam v : ℝ) : ℂ) = (lam : ℂ) := by
    have h1 := keplerPhi_keplerLong hpl lam
    unfold keplerPhi at h1
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) h1
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sin,
      Complex.ofReal_cos] at h2
    unfold keplerOp
    exact h2
  have hstrip : |((keplerLong lam v : ℝ) : ℂ).im| ≤ 1 := by simp
  exact ((Tube.keplerLongC_spec hmem).2.2 _ hstrip hop).symm

theorem keplerLongC_shift {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube) :
    keplerLongC (x.1 + 2 * π, x.2) = keplerLongC x + 2 * π := by
  have h := Tube.keplerData_regular
  exact keplerSol_shift
    (EqC.existsUnique_keplerOp h.y₀_pos h.κ_lt (h.invariant x hx) (h.contraction x hx))

/-- Derivative formulas (`bpP:p7:regular-kepler` (b), last clause). -/
theorem hasDerivAt_keplerLongC_lambda {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube) :
    HasDerivAt (fun t : ℂ => keplerLongC (t, x.2))
      (1 / (1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x)))
      x.1 := by
  have hg : HasFDerivAt (fun t : ℂ => (t, x.2)) (ContinuousLinearMap.inl ℂ ℂ (Fin 2 → ℂ)) x.1 :=
    hasFDerivAt_prodMk_left x.1 x.2
  have hc : HasFDerivAt (keplerLongC ∘ fun t : ℂ => (t, x.2))
      (fderiv ℂ keplerLongC x ∘L ContinuousLinearMap.inl ℂ ℂ (Fin 2 → ℂ)) x.1 :=
    (Tube.hasFDerivAt_keplerLongC hx).comp x.1 hg
  refine hc.hasDerivAt.congr_deriv ?_
  have h1 := Tube.fderiv_keplerLongC_eq hx (1, 0)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  rw [h1]
  simp

/-- F2: the other two derivative formulas of `bpP:p7:regular-kepler` (b) in the complex tube
(`∂_{v₀}F = sin F/J`, `∂_{v₁}F = -cos F/J`), and the source's sharp Jacobian bound. -/
theorem fderiv_keplerLongC_vec {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube) :
    fderiv ℂ (fun v => keplerLongC (x.1, v)) x.2 (Pi.single 0 1) =
        Complex.sin (keplerLongC x) /
          (1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x)) ∧
    fderiv ℂ (fun v => keplerLongC (x.1, v)) x.2 (Pi.single 1 1) =
        -Complex.cos (keplerLongC x) /
          (1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x)) := by
  have hg : HasFDerivAt (fun v : Fin 2 → ℂ => (x.1, v)) (ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ))
      x.2 := hasFDerivAt_prodMk_right x.1 x.2
  have hc : HasFDerivAt (keplerLongC ∘ fun v : Fin 2 → ℂ => (x.1, v))
      (fderiv ℂ keplerLongC x ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ)) x.2 :=
    (Tube.hasFDerivAt_keplerLongC hx).comp x.2 hg
  have hf : fderiv ℂ (fun v : Fin 2 → ℂ => keplerLongC (x.1, v)) x.2 =
      fderiv ℂ keplerLongC x ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) := hc.fderiv
  constructor
  · rw [hf]
    have h1 := Tube.fderiv_keplerLongC_eq hx (0, Pi.single 0 1)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [h1]
    simp
  · rw [hf]
    have h1 := Tube.fderiv_keplerLongC_eq hx (0, Pi.single 1 1)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [h1]
    simp

theorem regularKepler_jac_bound {x : ℂ × (Fin 2 → ℂ)} (hx : x ∈ regularTube) :
    1 - Real.cosh 1 / 4 ≤
      ‖1 - x.2 0 * Complex.cos (keplerLongC x) - x.2 1 * Complex.sin (keplerLongC x)‖ ∧
    (3 / 5 : ℝ) < 1 - Real.cosh 1 / 4 := by
  refine ⟨Tube.jac_bound_aux hx, ?_⟩
  have := cosh_one_lt
  norm_num at this
  linarith

/-! ### The thin tube around the real eccentricities (`bpI:p7:kepler-eq`) -/

/-- The constants of `bpI:p7:kepler-eq` for `0 < e₁ < 1`. -/
def keplerE2 (e₁ : ℝ) : ℝ := (1 + e₁) / 2
def keplerTheta (e₁ : ℝ) : ℝ := (1 + keplerE2 e₁) / 2
def keplerY0 (e₁ : ℝ) : ℝ := Real.arcosh (keplerTheta e₁ / keplerE2 e₁)
def keplerDeltaK (e₁ : ℝ) : ℝ := (1 - keplerTheta e₁) * keplerY0 e₁ / 2
def keplerDeltaE (e₁ : ℝ) : ℝ :=
  min (keplerE2 e₁ - e₁) ((1 - keplerTheta e₁) * keplerY0 e₁ / (2 * Real.cosh (keplerY0 e₁)))
/-- The thin tube `𝒫(e₁)` around the real eccentricity interval. -/
def keplerTube (e₁ : ℝ) : Set (ℂ × ℂ) :=
  {x | |x.1.im| < keplerDeltaK e₁ ∧
    Metric.infDist x.2 (Complex.ofReal '' Icc (-e₁) e₁) < keplerDeltaE e₁}
/-- The holomorphic eccentric anomaly `u(ℓ, e)`. -/
def eccAnomC (e₁ : ℝ) (x : ℂ × ℂ) : ℂ := keplerSol (keplerY0 e₁) x.2 0 x.1

namespace Tube

section TrackI

variable {e₁ : ℝ}

theorem e2_pos (h0 : 0 < e₁) : 0 < keplerE2 e₁ := by unfold keplerE2; linarith

theorem e1_lt_e2 (h1 : e₁ < 1) : e₁ < keplerE2 e₁ := by unfold keplerE2; linarith

theorem e2_lt_theta (h1 : e₁ < 1) : keplerE2 e₁ < keplerTheta e₁ := by
  unfold keplerTheta keplerE2; linarith

theorem theta_lt_one (h1 : e₁ < 1) : keplerTheta e₁ < 1 := by
  unfold keplerTheta keplerE2; linarith

theorem one_lt_theta_div (h0 : 0 < e₁) (h1 : e₁ < 1) : 1 < keplerTheta e₁ / keplerE2 e₁ :=
  (one_lt_div (e2_pos h0)).2 (e2_lt_theta h1)

theorem y0_pos (h0 : 0 < e₁) (h1 : e₁ < 1) : 0 < keplerY0 e₁ :=
  Real.arcosh_pos (one_lt_theta_div h0 h1)

theorem cosh_y0 (h0 : 0 < e₁) (h1 : e₁ < 1) :
    Real.cosh (keplerY0 e₁) = keplerTheta e₁ / keplerE2 e₁ :=
  Real.cosh_arcosh (one_lt_theta_div h0 h1).le

/-- `e₂ cosh y₀ = θ`. -/
theorem e2_mul_cosh (h0 : 0 < e₁) (h1 : e₁ < 1) :
    keplerE2 e₁ * Real.cosh (keplerY0 e₁) = keplerTheta e₁ := by
  rw [cosh_y0 h0 h1]
  exact mul_div_cancel₀ _ (e2_pos h0).ne'

theorem deltaK_pos (h0 : 0 < e₁) (h1 : e₁ < 1) : 0 < keplerDeltaK e₁ := by
  have := y0_pos h0 h1
  have := theta_lt_one h1
  unfold keplerDeltaK
  have : 0 < 1 - keplerTheta e₁ := by linarith
  positivity

theorem deltaE_pos (h0 : 0 < e₁) (h1 : e₁ < 1) : 0 < keplerDeltaE e₁ := by
  have hy := y0_pos h0 h1
  have ht := theta_lt_one h1
  have h2 := e1_lt_e2 h1
  have hc := Real.cosh_pos (keplerY0 e₁)
  have : 0 < 1 - keplerTheta e₁ := by linarith
  unfold keplerDeltaE
  refine lt_min (by linarith) ?_
  positivity

theorem deltaE_le_left (e₁ : ℝ) : keplerDeltaE e₁ ≤ keplerE2 e₁ - e₁ := min_le_left _ _

theorem deltaE_cosh_le (e₁ : ℝ) :
    keplerDeltaE e₁ * Real.cosh (keplerY0 e₁) ≤ (1 - keplerTheta e₁) * keplerY0 e₁ / 2 := by
  have hc := Real.cosh_pos (keplerY0 e₁)
  have h2 : keplerDeltaE e₁ ≤
      (1 - keplerTheta e₁) * keplerY0 e₁ / (2 * Real.cosh (keplerY0 e₁)) := min_le_right _ _
  calc keplerDeltaE e₁ * Real.cosh (keplerY0 e₁)
      ≤ (1 - keplerTheta e₁) * keplerY0 e₁ / (2 * Real.cosh (keplerY0 e₁)) *
          Real.cosh (keplerY0 e₁) := mul_le_mul_of_nonneg_right h2 hc.le
    _ = (1 - keplerTheta e₁) * keplerY0 e₁ / 2 := by field_simp

theorem deltaK_lt_y0 (h0 : 0 < e₁) (h1 : e₁ < 1) : keplerDeltaK e₁ < keplerY0 e₁ := by
  have hy := y0_pos h0 h1
  have ht := theta_lt_one h1
  have h2 := e2_pos h0
  have h3 := e2_lt_theta h1
  unfold keplerDeltaK
  nlinarith

theorem isOpen_keplerTube (e₁ : ℝ) : IsOpen (keplerTube e₁) := by
  have h1 : IsOpen {x : ℂ × ℂ | |x.1.im| < keplerDeltaK e₁} :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp continuous_fst)) continuous_const
  have h2 : IsOpen {x : ℂ × ℂ |
      Metric.infDist x.2 (Complex.ofReal '' Icc (-e₁) e₁) < keplerDeltaE e₁} :=
    isOpen_lt (Metric.continuous_infDist_pt _ |>.comp continuous_snd) continuous_const
  exact h1.inter h2

/-- Points of the tube are within `δ_E` of a real eccentricity in `[-e₁, e₁]`. -/
theorem exists_real_near {x : ℂ × ℂ} (h0 : 0 < e₁) (hx : x ∈ keplerTube e₁) :
    ∃ e' : ℝ, |e'| ≤ e₁ ∧ ‖x.2 - (e' : ℂ)‖ < keplerDeltaE e₁ := by
  have hne : (Complex.ofReal '' Icc (-e₁) e₁).Nonempty :=
    ⟨0, 0, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨y, ⟨e', he', rfl⟩, hd⟩ := (Metric.infDist_lt_iff hne).1 hx.2
  exact ⟨e', abs_le.2 he', by rwa [dist_eq_norm] at hd⟩

/-- On the tube, `‖e‖ ≤ e₂` and `|Im e| < δ_E`. -/
theorem tube_bounds {x : ℂ × ℂ} (h0 : 0 < e₁) (hx : x ∈ keplerTube e₁) :
    ‖x.2‖ ≤ keplerE2 e₁ ∧ |x.2.im| ≤ keplerDeltaE e₁ := by
  obtain ⟨e', he', hd⟩ := exists_real_near h0 hx
  have h1 : ‖x.2‖ ≤ ‖(e' : ℂ)‖ + ‖x.2 - (e' : ℂ)‖ := by
    have := norm_add_le (x.2 - (e' : ℂ)) (e' : ℂ)
    rw [sub_add_cancel] at this
    linarith
  have h2 : ‖(e' : ℂ)‖ ≤ e₁ := by rwa [Complex.norm_real]
  have h3 := deltaE_le_left e₁
  refine ⟨by linarith, ?_⟩
  have : (x.2 - (e' : ℂ)).im = x.2.im := by simp
  rw [← this]
  exact (Complex.abs_im_le_norm _).trans hd.le

/-- The contraction data of the thin tube: strip `|Im u| ≤ y₀`, constant `θ`. -/
theorem keplerData_tube (h0 : 0 < e₁) (h1 : e₁ < 1) :
    KeplerData (keplerTube e₁) (fun x : ℂ × ℂ => x.2) (fun _ => (0 : ℂ)) (fun x => x.1)
      (keplerY0 e₁) (keplerTheta e₁) where
  isOpen := isOpen_keplerTube e₁
  analytic_a := fun x _ => analyticAt_snd
  analytic_b := fun x _ => analyticAt_const
  analytic_c := fun x _ => analyticAt_fst
  y₀_pos := y0_pos h0 h1
  κ_lt := theta_lt_one h1
  invariant := by
    intro x hx
    obtain ⟨hn, hi⟩ := tube_bounds h0 hx
    have hy := y0_pos h0 h1
    have hK : |x.1.im| < keplerDeltaK e₁ := hx.1
    have hre : |x.2.re| ≤ keplerE2 e₁ := (Complex.abs_re_le_norm _).trans hn
    have hs : 0 ≤ Real.sinh (keplerY0 e₁) := Real.sinh_nonneg_iff.2 hy.le
    have hc : 0 < Real.cosh (keplerY0 e₁) := Real.cosh_pos _
    have e1 : |x.2.re| * Real.sinh (keplerY0 e₁) ≤ keplerE2 e₁ * Real.sinh (keplerY0 e₁) :=
      mul_le_mul_of_nonneg_right hre hs
    have e2 : keplerE2 e₁ * Real.sinh (keplerY0 e₁) ≤ keplerTheta e₁ * keplerY0 e₁ := by
      calc keplerE2 e₁ * Real.sinh (keplerY0 e₁)
          ≤ keplerE2 e₁ * (keplerY0 e₁ * Real.cosh (keplerY0 e₁)) :=
            mul_le_mul_of_nonneg_left (sinh_le_mul_cosh hy.le) (e2_pos h0).le
        _ = keplerTheta e₁ * keplerY0 e₁ := by rw [← e2_mul_cosh h0 h1]; ring
    have e3 : |x.2.im| * Real.cosh (keplerY0 e₁) ≤ keplerDeltaE e₁ * Real.cosh (keplerY0 e₁) :=
      mul_le_mul_of_nonneg_right hi hc.le
    have e4 := deltaE_cosh_le e₁
    have e5 : keplerDeltaK e₁ = (1 - keplerTheta e₁) * keplerY0 e₁ / 2 := rfl
    show |x.1.im| + (|x.2.re| + |(0 : ℂ).re|) * Real.sinh (keplerY0 e₁)
      + (|x.2.im| + |(0 : ℂ).im|) * Real.cosh (keplerY0 e₁) < keplerY0 e₁
    simp only [Complex.zero_re, Complex.zero_im, abs_zero, add_zero]
    nlinarith
  contraction := by
    intro x hx
    obtain ⟨hn, -⟩ := tube_bounds h0 hx
    have hc := Real.cosh_pos (keplerY0 e₁)
    show (‖x.2‖ + ‖(0 : ℂ)‖) * Real.cosh (keplerY0 e₁) ≤ keplerTheta e₁
    rw [norm_zero, add_zero, ← e2_mul_cosh h0 h1]
    exact mul_le_mul_of_nonneg_right hn hc.le

theorem eccAnomC_spec {x : ℂ × ℂ} (h0 : 0 < e₁) (h1 : e₁ < 1) (hx : x ∈ keplerTube e₁) :
    |(eccAnomC e₁ x).im| ≤ keplerY0 e₁ ∧ keplerOp x.2 0 (eccAnomC e₁ x) = x.1 ∧
      ∀ G : ℂ, |G.im| ≤ keplerY0 e₁ → keplerOp x.2 0 G = x.1 → G = eccAnomC e₁ x :=
  keplerSol_spec (keplerData_tube h0 h1) hx

theorem eccAnomC_analyticOnNhd (h0 : 0 < e₁) (h1 : e₁ < 1) :
    AnalyticOnNhd ℂ (eccAnomC e₁) (keplerTube e₁) :=
  keplerSol_analyticOnNhd (keplerData_tube h0 h1)

theorem keplerOp_zero_right (a G : ℂ) : keplerOp a 0 G = G - a * Complex.sin G := by
  simp [keplerOp]

/-- The lower bound `1 - θ ≤ |1 - e cos u|` on the tube. -/
theorem jac_bound_tube {x : ℂ × ℂ} (h0 : 0 < e₁) (h1 : e₁ < 1) (hx : x ∈ keplerTube e₁) :
    ‖x.2 * Complex.cos (eccAnomC e₁ x)‖ ≤ keplerTheta e₁ ∧
      1 - keplerTheta e₁ ≤ ‖1 - x.2 * Complex.cos (eccAnomC e₁ x)‖ := by
  obtain ⟨hn, -⟩ := tube_bounds h0 hx
  obtain ⟨hs, -, -⟩ := eccAnomC_spec h0 h1 hx
  have hcos := EqC.norm_cos_le hs
  have hc := Real.cosh_pos (keplerY0 e₁)
  have h2 : ‖x.2 * Complex.cos (eccAnomC e₁ x)‖ ≤ keplerTheta e₁ := by
    rw [norm_mul, ← e2_mul_cosh h0 h1]
    exact mul_le_mul hn hcos (norm_nonneg _) (e2_pos h0).le
  refine ⟨h2, ?_⟩
  have h3 : ‖(1 : ℂ)‖ - ‖x.2 * Complex.cos (eccAnomC e₁ x)‖ ≤
      ‖1 - x.2 * Complex.cos (eccAnomC e₁ x)‖ := norm_sub_norm_le _ _
  rw [norm_one] at h3
  linarith

theorem jac_ne_zero_tube {x : ℂ × ℂ} (h0 : 0 < e₁) (h1 : e₁ < 1) (hx : x ∈ keplerTube e₁) :
    1 - x.2 * Complex.cos (eccAnomC e₁ x) ≠ 0 := by
  intro h
  have h2 := (jac_bound_tube h0 h1 hx).2
  rw [h, norm_zero] at h2
  have := theta_lt_one h1
  linarith

/-- Implicit differentiation of Kepler's equation in a direction `v`. -/
theorem fderiv_eccAnomC_eq {x : ℂ × ℂ} (h0 : 0 < e₁) (h1 : e₁ < 1) (hx : x ∈ keplerTube e₁)
    (v : ℂ × ℂ) :
    fderiv ℂ (eccAnomC e₁) x v =
      (v.2 * Complex.sin (eccAnomC e₁ x) + v.1) / (1 - x.2 * Complex.cos (eccAnomC e₁ x)) := by
  have h := keplerSol_fderiv (keplerData_tube h0 h1) hx v
  have ha : fderiv ℂ (fun y : ℂ × ℂ => y.2) x v = v.2 := by
    have h : HasFDerivAt (fun y : ℂ × ℂ => y.2) (ContinuousLinearMap.snd ℂ ℂ ℂ) x :=
      (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt
    rw [h.fderiv]; rfl
  have hc : fderiv ℂ (fun y : ℂ × ℂ => y.1) x v = v.1 := by
    have h : HasFDerivAt (fun y : ℂ × ℂ => y.1) (ContinuousLinearMap.fst ℂ ℂ ℂ) x :=
      (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt
    rw [h.fderiv]; rfl
  rw [ha, hc, fderiv_fun_const] at h
  simp only [Pi.zero_apply, zero_apply, zero_mul, sub_zero] at h
  refine (eq_div_iff (jac_ne_zero_tube h0 h1 hx)).2 ?_
  have h' : fderiv ℂ (eccAnomC e₁) x v * (1 - x.2 * Complex.cos (eccAnomC e₁ x)) =
      v.2 * Complex.sin (eccAnomC e₁ x) + v.1 := by
    exact h
  exact h'

theorem hasFDerivAt_eccAnomC (h0 : 0 < e₁) (h1 : e₁ < 1) {x : ℂ × ℂ} (hx : x ∈ keplerTube e₁) :
    HasFDerivAt (eccAnomC e₁) (fderiv ℂ (eccAnomC e₁) x) x :=
  (eccAnomC_analyticOnNhd h0 h1 x hx).differentiableAt.hasFDerivAt

end TrackI

end Tube

theorem keplerConstants_pos {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) :
    0 < keplerY0 e₁ ∧ 0 < keplerDeltaK e₁ ∧ 0 < keplerDeltaE e₁ ∧ e₁ < keplerE2 e₁ ∧
      keplerE2 e₁ < keplerTheta e₁ ∧ keplerTheta e₁ < 1 :=
  ⟨Tube.y0_pos h0 h1, Tube.deltaK_pos h0 h1, Tube.deltaE_pos h0 h1, Tube.e1_lt_e2 h1,
    Tube.e2_lt_theta h1, Tube.theta_lt_one h1⟩

/-- `bpI:p7:kepler-eq`: existence, uniqueness in the strip, holomorphy, (a), (b), (c). -/
theorem keplerEq_tube {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) :
    IsOpen (keplerTube e₁) ∧ DifferentiableOn ℂ (eccAnomC e₁) (keplerTube e₁) ∧
    (∀ x ∈ keplerTube e₁, |(eccAnomC e₁ x).im| ≤ keplerY0 e₁ ∧
      eccAnomC e₁ x - x.2 * Complex.sin (eccAnomC e₁ x) = x.1 ∧
      ∀ G : ℂ, |G.im| ≤ keplerY0 e₁ → G - x.2 * Complex.sin G = x.1 → G = eccAnomC e₁ x) ∧
    (∀ x ∈ keplerTube e₁, ‖Complex.sin (eccAnomC e₁ x)‖ ≤ Real.cosh (keplerY0 e₁) ∧
      ‖Complex.cos (eccAnomC e₁ x)‖ ≤ Real.cosh (keplerY0 e₁) ∧
      ‖x.2 * Complex.cos (eccAnomC e₁ x)‖ ≤ keplerTheta e₁ ∧
      1 - keplerTheta e₁ ≤ ‖1 - x.2 * Complex.cos (eccAnomC e₁ x)‖) := by
  refine ⟨Tube.isOpen_keplerTube e₁, (Tube.eccAnomC_analyticOnNhd h0 h1).differentiableOn,
    fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨hs, hop, huniq⟩ := Tube.eccAnomC_spec h0 h1 hx
    rw [Tube.keplerOp_zero_right] at hop
    refine ⟨hs, hop, fun G hG hGe => huniq G hG ?_⟩
    rw [Tube.keplerOp_zero_right]
    exact hGe
  · obtain ⟨hs, -, -⟩ := Tube.eccAnomC_spec h0 h1 hx
    obtain ⟨hb1, hb2⟩ := Tube.jac_bound_tube h0 h1 hx
    exact ⟨EqC.norm_sin_le hs, EqC.norm_cos_le hs, hb1, hb2⟩

theorem keplerTube_real_points {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) {ℓ e : ℝ} (he : |e| ≤ e₁) :
    ((ℓ : ℂ), (e : ℂ)) ∈ keplerTube e₁ ∧ eccAnomC e₁ ((ℓ : ℂ), (e : ℂ)) = (eccAnom ℓ e : ℂ) := by
  have hmem : ((ℓ : ℂ), (e : ℂ)) ∈ keplerTube e₁ := by
    refine ⟨?_, ?_⟩
    · simpa using Tube.deltaK_pos h0 h1
    · rw [Metric.infDist_zero_of_mem
        (show (e : ℂ) ∈ Complex.ofReal '' Icc (-e₁) e₁ from ⟨e, abs_le.1 he, rfl⟩)]
      exact Tube.deltaE_pos h0 h1
  refine ⟨hmem, ?_⟩
  have hlt : |e| < 1 := lt_of_le_of_lt he h1
  have h2 := eccAnom_eq ℓ hlt
  have h3 := congrArg (fun r : ℝ => (r : ℂ)) h2
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sin] at h3
  have hop : keplerOp (e : ℂ) 0 ((eccAnom ℓ e : ℝ) : ℂ) = (ℓ : ℂ) := by
    rw [Tube.keplerOp_zero_right]
    exact h3
  have hstrip : |((eccAnom ℓ e : ℝ) : ℂ).im| ≤ keplerY0 e₁ := by
    simpa using (Tube.y0_pos h0 h1).le
  exact ((Tube.eccAnomC_spec h0 h1 hmem).2.2 _ hstrip hop).symm

theorem eccAnomC_periodic {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) {x : ℂ × ℂ}
    (hx : x ∈ keplerTube e₁) :
    (x.1 + 2 * π, x.2) ∈ keplerTube e₁ ∧
      eccAnomC e₁ (x.1 + 2 * π, x.2) = eccAnomC e₁ x + 2 * π := by
  refine ⟨⟨?_, hx.2⟩, ?_⟩
  · have : (x.1 + 2 * (π : ℂ)).im = x.1.im := by simp
    show |(x.1 + 2 * (π : ℂ)).im| < keplerDeltaK e₁
    rw [this]
    exact hx.1
  · have h := Tube.keplerData_tube h0 h1
    exact keplerSol_shift
      (EqC.existsUnique_keplerOp h.y₀_pos h.κ_lt (h.invariant x hx) (h.contraction x hx))

theorem eccAnomC_zero_ecc {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) {ℓ : ℂ}
    (hℓ : |ℓ.im| < keplerDeltaK e₁) : eccAnomC e₁ (ℓ, 0) = ℓ := by
  have hmem : (ℓ, (0 : ℂ)) ∈ keplerTube e₁ := by
    refine ⟨hℓ, ?_⟩
    rw [Metric.infDist_zero_of_mem
      (show (0 : ℂ) ∈ Complex.ofReal '' Icc (-e₁) e₁ from ⟨0, ⟨by linarith, by linarith⟩, by simp⟩)]
    exact Tube.deltaE_pos h0 h1
  have hstrip : |ℓ.im| ≤ keplerY0 e₁ := (hℓ.trans (Tube.deltaK_lt_y0 h0 h1)).le
  have hop : keplerOp (0 : ℂ) 0 ℓ = ℓ := by
    rw [Tube.keplerOp_zero_right]; simp
  exact ((Tube.eccAnomC_spec h0 h1 hmem).2.2 ℓ hstrip hop).symm

theorem hasDerivAt_eccAnomC_ell {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) {x : ℂ × ℂ}
    (hx : x ∈ keplerTube e₁) :
    HasDerivAt (fun t : ℂ => eccAnomC e₁ (t, x.2))
      (1 / (1 - x.2 * Complex.cos (eccAnomC e₁ x))) x.1 := by
  have hg : HasFDerivAt (fun t : ℂ => (t, x.2)) (ContinuousLinearMap.inl ℂ ℂ ℂ) x.1 :=
    hasFDerivAt_prodMk_left x.1 x.2
  have hc : HasFDerivAt (eccAnomC e₁ ∘ fun t : ℂ => (t, x.2))
      (fderiv ℂ (eccAnomC e₁) x ∘L ContinuousLinearMap.inl ℂ ℂ ℂ) x.1 :=
    (Tube.hasFDerivAt_eccAnomC h0 h1 hx).comp x.1 hg
  refine hc.hasDerivAt.congr_deriv ?_
  have h2 := Tube.fderiv_eccAnomC_eq h0 h1 hx (1, 0)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  rw [h2]
  simp

/-- F2: `∂_e u = sin u/(1 - e cos u)` on the tube. -/
theorem hasDerivAt_eccAnomC_ecc {e₁ : ℝ} (h0 : 0 < e₁) (h1 : e₁ < 1) {x : ℂ × ℂ}
    (hx : x ∈ keplerTube e₁) :
    HasDerivAt (fun e : ℂ => eccAnomC e₁ (x.1, e))
      (Complex.sin (eccAnomC e₁ x) / (1 - x.2 * Complex.cos (eccAnomC e₁ x))) x.2 := by
  have hg : HasFDerivAt (fun e : ℂ => (x.1, e)) (ContinuousLinearMap.inr ℂ ℂ ℂ) x.2 :=
    hasFDerivAt_prodMk_right x.1 x.2
  have hc : HasFDerivAt (eccAnomC e₁ ∘ fun e : ℂ => (x.1, e))
      (fderiv ℂ (eccAnomC e₁) x ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) x.2 :=
    (Tube.hasFDerivAt_eccAnomC h0 h1 hx).comp x.2 hg
  refine hc.hasDerivAt.congr_deriv ?_
  have h2 := Tube.fderiv_eccAnomC_eq h0 h1 hx (0, 1)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [h2]
  simp

end Equation

end KAM.Kepler

end
