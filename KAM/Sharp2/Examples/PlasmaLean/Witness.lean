/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.PlasmaLean.Frequency
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A two-wave Hamiltonian at PlasmaLean's frequency

The witness of the non-vacuity of `CALike`, on `ℂ² × ℂ²`:

`h_ε(θ, I) = ω*·I + ½ I·I + ε (cos 2πθ₀ + cos 2π(θ₀ + θ₁))`.

At `ε = 0` it is integrable, with the invariant torus `I = 0` of frequency `ω*`. Everything here is
explicit: `plX ε` is the Hamiltonian vector field (`hamiltonianVectorField_plH`), `plDX ε` its
derivative, and the fourth-order bounds of `CALike` hold on `plB` for `0 ≤ ε ≤ 1/1000`
(`plH_bounds`).
-/

@[expose] public noncomputable section

open Real

namespace KAM.Sharp2.Examples

/-- The phase space. -/
abbrev PS : Type := (Fin 2 → ℂ) × (Fin 2 → ℂ)

/-- The coordinate `I_i`. -/
def pI (i : Fin 2) : PS →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).comp
    (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (Fin 2 → ℂ))

/-- The phase `θ₀` of the first wave. -/
def pA : PS →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).comp
    (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) (Fin 2 → ℂ))

/-- The phase `θ₀ + θ₁` of the second wave. -/
def pB : PS →L[ℂ] ℂ :=
  pA + (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).comp
    (ContinuousLinearMap.fst ℂ (Fin 2 → ℂ) (Fin 2 → ℂ))

/-- The wave vector of the first wave. -/
def vA : Fin 2 → ℂ := ![1, 0]

/-- The wave vector of the second wave. -/
def vB : Fin 2 → ℂ := ![1, 1]

@[simp] theorem pI_apply (i : Fin 2) (z : PS) : pI i z = z.2 i := rfl
@[simp] theorem pA_apply (z : PS) : pA z = z.1 0 := rfl
@[simp] theorem pB_apply (z : PS) : pB z = z.1 0 + z.1 1 := rfl

/-- The Hamiltonian `h_ε`. -/
def plH (ε : ℝ) (z : PS) : ℂ :=
  ∑ i, ((omegaStar i : ℂ) * z.2 i + 1 / 2 * z.2 i ^ 2) +
    ε * (Complex.cos (2 * π * z.1 0) + Complex.cos (2 * π * (z.1 0 + z.1 1)))

/-- The derivative of `h_ε`. -/
def plDh (ε : ℝ) (z : PS) : PS →L[ℂ] ℂ :=
  ((omegaStar 0 + z.2 0 : ℂ)) • pI 0 + ((omegaStar 1 + z.2 1 : ℂ)) • pI 1 -
    ((2 * π * ε * Complex.sin (2 * π * pA z) : ℂ)) • pA -
    ((2 * π * ε * Complex.sin (2 * π * pB z) : ℂ)) • pB

/-- The derivative of `z ↦ cos 2π p(z)`. -/
theorem hasFDerivAt_cos (p : PS →L[ℂ] ℂ) (z : PS) :
    HasFDerivAt (fun z => Complex.cos (2 * π * p z))
      ((-(Complex.sin (2 * π * p z)) * (2 * π) : ℂ) • p) z := by
  have h1 : HasFDerivAt (fun z => (2 * π : ℂ) * p z) ((2 * π : ℂ) • p) z :=
    p.hasFDerivAt.const_mul _
  have := (Complex.hasDerivAt_cos _).comp_hasFDerivAt z h1
  rw [smul_smul] at this
  exact this

/-- The derivative of `z ↦ sin 2π p(z)`. -/
theorem hasFDerivAt_sin (p : PS →L[ℂ] ℂ) (z : PS) :
    HasFDerivAt (fun z => Complex.sin (2 * π * p z))
      ((Complex.cos (2 * π * p z) * (2 * π) : ℂ) • p) z := by
  have h1 : HasFDerivAt (fun z => (2 * π : ℂ) * p z) ((2 * π : ℂ) • p) z :=
    p.hasFDerivAt.const_mul _
  have := (Complex.hasDerivAt_sin _).comp_hasFDerivAt z h1
  rw [smul_smul] at this
  exact this

theorem hasFDerivAt_plH (ε : ℝ) (z : PS) : HasFDerivAt (plH ε) (plDh ε z) z := by
  have hI : ∀ i, HasFDerivAt (fun z : PS => (omegaStar i : ℂ) * z.2 i + 1 / 2 * z.2 i ^ 2)
      ((omegaStar i + z.2 i : ℂ) • pI i) z := fun i => by
    have h1 : HasFDerivAt (fun z : PS => (omegaStar i : ℂ) * pI i z)
        ((omegaStar i : ℂ) • pI i) z := (pI i).hasFDerivAt.const_mul _
    have h2 : HasFDerivAt (fun z : PS => 1 / 2 * pI i z ^ 2)
        (((1 / 2 : ℂ) * ((2 : ℕ) * pI i z ^ 1)) • pI i) z := by
      have := ((pI i).hasFDerivAt (x := z)).pow 2
      have h3 := this.const_mul (1 / 2 : ℂ)
      simpa [smul_smul, mul_comm] using h3
    have h3 := h1.add h2
    refine h3.congr_fderiv ?_
    rw [← add_smul]
    congr 1
    simp
  have hC := ((hasFDerivAt_cos pA z).add (hasFDerivAt_cos pB z)).const_mul (ε : ℂ)
  have hS := ((hI 0).add (hI 1)).add hC
  have e : plH ε = (fun z : PS => (omegaStar 0 : ℂ) * z.2 0 + 1 / 2 * z.2 0 ^ 2 +
      ((omegaStar 1 : ℂ) * z.2 1 + 1 / 2 * z.2 1 ^ 2) + (ε : ℂ) *
      (Complex.cos (2 * π * pA z) + Complex.cos (2 * π * pB z))) := by
    funext w
    simp [plH, Fin.sum_univ_two]
  rw [e]
  refine hS.congr_fderiv ?_
  ext w <;> simp [plDh]
  ring

theorem fderiv_plH (ε : ℝ) (z : PS) : fderiv ℂ (plH ε) z = plDh ε z :=
  (hasFDerivAt_plH ε z).fderiv

theorem differentiable_plH (ε : ℝ) : Differentiable ℂ (plH ε) := fun z =>
  (hasFDerivAt_plH ε z).differentiableAt

/-- The Hamiltonian vector field of `h_ε`, explicitly. -/
def plX (ε : ℝ) (z : PS) : PS :=
  (fun i => (omegaStar i : ℂ) + z.2 i,
    (2 * π * ε * Complex.sin (2 * π * pA z)) • vA + (2 * π * ε * Complex.sin (2 * π * pB z)) • vB)

theorem hamiltonianVectorField_plH (ε : ℝ) : hamiltonianVectorFieldℂ (plH ε) = plX ε := by
  funext z
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [hamiltonianVectorFieldℂ, fderiv_plH]
    fin_cases i <;> simp [plDh, plX]
  · simp only [hamiltonianVectorFieldℂ, fderiv_plH]
    fin_cases i <;> simp [plDh, plX, vA, vB]
    ring

/-- The constant part of `DX`: `(u, v) ↦ (v, 0)`. -/
def pS : PS →L[ℂ] PS :=
  (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).prod 0

/-- The direction of one wave in `DX`: `(u, v) ↦ (0, (2π)² ε p(u, v) w)`. -/
def pT (ε : ℝ) (p : PS →L[ℂ] ℂ) (w : Fin 2 → ℂ) : PS →L[ℂ] PS :=
  (0 : PS →L[ℂ] (Fin 2 → ℂ)).prod (((2 * π : ℂ) ^ 2 * ε) • p.smulRight w)

@[simp] theorem pS_apply (w : PS) : pS w = (w.2, 0) := rfl
@[simp] theorem pT_apply (ε : ℝ) (p : PS →L[ℂ] ℂ) (w : Fin 2 → ℂ) (u : PS) :
    pT ε p w u = (0, ((2 * π : ℂ) ^ 2 * ε * p u) • w) := by
  simp [pT, mul_smul]

/-- The derivative of the Hamiltonian vector field. -/
def plDX (ε : ℝ) (z : PS) : PS →L[ℂ] PS :=
  pS + Complex.cos (2 * π * pA z) • pT ε pA vA + Complex.cos (2 * π * pB z) • pT ε pB vB

theorem hasFDerivAt_plX (ε : ℝ) (z : PS) : HasFDerivAt (plX ε) (plDX ε z) z := by
  have h1 : HasFDerivAt (fun z : PS => (fun i => (omegaStar i : ℂ)) + z.2)
      (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)) z :=
    (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).hasFDerivAt.const_add
      (fun i => (omegaStar i : ℂ))
  have hW : ∀ p : PS →L[ℂ] ℂ, ∀ w : Fin 2 → ℂ,
      HasFDerivAt (fun z => ((2 * π * ε : ℂ) * Complex.sin (2 * π * p z)) • w)
        (((2 * π * ε : ℂ) • (Complex.cos (2 * π * p z) * (2 * π) : ℂ) • p).smulRight w) z :=
    fun p w => ((hasFDerivAt_sin p z).const_mul (2 * π * ε : ℂ)).smul_const w
  have h2 := (hW pA vA).add (hW pB vB)
  refine (h1.prodMk h2).congr_fderiv ?_
  ext w <;> simp [plDX, pS]
  ring_nf

theorem fderiv_plX (ε : ℝ) : fderiv ℂ (plX ε) = plDX ε :=
  funext fun z => (hasFDerivAt_plX ε z).fderiv

/-- The second derivative of the Hamiltonian vector field. -/
def plD2X (ε : ℝ) (z : PS) : PS →L[ℂ] PS →L[ℂ] PS :=
  ((-(Complex.sin (2 * π * pA z)) * (2 * π) : ℂ) • pA).smulRight (pT ε pA vA) +
    ((-(Complex.sin (2 * π * pB z)) * (2 * π) : ℂ) • pB).smulRight (pT ε pB vB)

theorem hasFDerivAt_plDX (ε : ℝ) (z : PS) : HasFDerivAt (plDX ε) (plD2X ε z) z := by
  have h1 := ((hasFDerivAt_cos pA z).smul_const (pT ε pA vA)).add
    ((hasFDerivAt_cos pB z).smul_const (pT ε pB vB))
  have h2 := h1.const_add pS
  have e : plDX ε = fun x => pS + ((fun y => Complex.cos (2 * π * pA y) • pT ε pA vA) +
      fun y => Complex.cos (2 * π * pB y) • pT ε pB vB) x := by
    funext w
    simp only [plDX, Pi.add_apply, add_assoc]
  rw [e]
  exact h2

/-- The domain of the witness. -/
def plB : Set PS := complexStrip 2 (1 / 30) ×ˢ Metric.ball 0 (1 / 10)

theorem exp_le_two {y : ℝ} (h : y ≤ 1 / 2) : Real.exp y ≤ 2 := by
  have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  have h4 : Real.exp (1 / 2) ≤ 2 := by nlinarith
  exact (Real.exp_le_exp.mpr h).trans h4

theorem norm_exp_I_le_two {w : ℂ} (h : |w.im| ≤ 1 / 2) : ‖Complex.exp (w * Complex.I)‖ ≤ 2 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub]
  exact exp_le_two ((neg_le_abs _).trans h)

theorem norm_exp_neg_I_le_two {w : ℂ} (h : |w.im| ≤ 1 / 2) :
    ‖Complex.exp (-w * Complex.I)‖ ≤ 2 := by
  have := norm_exp_I_le_two (w := -w) (by simpa using h)
  simpa using this

theorem norm_cos_le_two {w : ℂ} (h : |w.im| ≤ 1 / 2) : ‖Complex.cos w‖ ≤ 2 := by
  have h1 := norm_add_le (Complex.exp (w * Complex.I)) (Complex.exp (-w * Complex.I))
  rw [← Complex.two_cos, norm_mul] at h1
  have h2 := norm_exp_I_le_two h
  have h3 := norm_exp_neg_I_le_two h
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4] at h1
  linarith

theorem norm_sin_le_two {w : ℂ} (h : |w.im| ≤ 1 / 2) : ‖Complex.sin w‖ ≤ 2 := by
  have h1 := norm_sub_le (Complex.exp (-w * Complex.I)) (Complex.exp (w * Complex.I))
  have h5 : ‖(2 : ℂ) * Complex.sin w‖ =
      ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ := by
    rw [Complex.two_sin, norm_mul]
    simp
  rw [norm_mul] at h5
  have h2 := norm_exp_I_le_two h
  have h3 := norm_exp_neg_I_le_two h
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h4] at h5
  linarith

theorem pi_lt : π < 63 / 20 := by
  have := Real.pi_lt_d2
  norm_num at this ⊢
  linarith

theorem im_pA_le {z : PS} (hz : z ∈ plB) : |(2 * π * pA z : ℂ).im| ≤ 1 / 2 := by
  have h1 : |(z.1 0).im| < 1 / 30 := hz.1 0
  have hpi := pi_lt
  have hpi0 := Real.pi_pos
  have e : (2 * π * pA z : ℂ).im = 2 * π * (z.1 0).im := by simp
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
  nlinarith

theorem im_pB_le {z : PS} (hz : z ∈ plB) : |(2 * π * pB z : ℂ).im| ≤ 1 / 2 := by
  have h1 : |(z.1 0).im| < 1 / 30 := hz.1 0
  have h2 : |(z.1 1).im| < 1 / 30 := hz.1 1
  have hpi := pi_lt
  have hpi0 := Real.pi_pos
  have e : (2 * π * pB z : ℂ).im = 2 * π * ((z.1 0).im + (z.1 1).im) := by simp
  have h3 := abs_add_le (z.1 0).im (z.1 1).im
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
  nlinarith

theorem norm_pI_le (i : Fin 2) : ‖pI i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul, pI_apply]
    exact (norm_le_pi_norm w.2 i).trans (norm_snd_le w)

theorem norm_pA_le : ‖pA‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul, pA_apply]
    exact (norm_le_pi_norm w.1 0).trans (norm_fst_le w)

theorem norm_pB_le : ‖pB‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_two fun w => by
    rw [pB_apply]
    have h0 := (norm_le_pi_norm w.1 0).trans (norm_fst_le w)
    have h1 := (norm_le_pi_norm w.1 1).trans (norm_fst_le w)
    have := norm_add_le (w.1 0) (w.1 1)
    linarith

theorem norm_vA_le : ‖vA‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  fin_cases i <;> simp [vA]

theorem norm_vB_le : ‖vB‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  fin_cases i <;> simp [vB]

theorem norm_pS_le : ‖pS‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul, pS_apply, Prod.norm_def]
    exact max_le (norm_snd_le w) (by simp)

theorem two_pi_sq_le : ‖(2 * π : ℂ) ^ 2‖ ≤ 40 := by
  have hpi := pi_lt
  have hpi0 := Real.pi_pos
  have e : ‖(2 * π : ℂ) ^ 2‖ = (2 * π) ^ 2 := by
    rw [norm_pow, norm_mul, Complex.norm_real]
    simp [abs_of_pos hpi0]
  rw [e]
  nlinarith

theorem norm_pT_le {ε : ℝ} (h0 : 0 ≤ ε) (p : PS →L[ℂ] ℂ) {w : Fin 2 → ℂ} (hw : ‖w‖ ≤ 1) :
    ‖pT ε p w‖ ≤ 40 * ε * ‖p‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => by
    rw [pT_apply, Prod.norm_def, norm_zero, norm_smul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg h0]
    refine max_le (by positivity) ?_
    have h1 := p.le_opNorm u
    have h2 := two_pi_sq_le
    calc ‖(2 * π : ℂ) ^ 2‖ * ε * ‖p u‖ * ‖w‖ ≤ 40 * ε * (‖p‖ * ‖u‖) * 1 := by gcongr
      _ = _ := by ring

theorem norm_two_pi_eps_sin_le {ε : ℝ} (h0 : 0 ≤ ε) {w : ℂ} (hw : |w.im| ≤ 1 / 2) :
    ‖(2 * π * ε * Complex.sin w : ℂ)‖ ≤ 13 * ε := by
  have hpi := pi_lt
  have hpi0 := Real.pi_pos
  have h1 := norm_sin_le_two hw
  have e : ‖(2 * π * ε * Complex.sin w : ℂ)‖ = 2 * π * ε * ‖Complex.sin w‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    simp [abs_of_pos hpi0, abs_of_nonneg h0]
  rw [e]
  have : 2 * π * ε * ‖Complex.sin w‖ ≤ 2 * (63 / 20) * ε * 2 := by gcongr
  linarith

theorem norm_omega_add_le (i : Fin 2) {z : PS} (hz : z ∈ plB) :
    ‖(omegaStar i + z.2 i : ℂ)‖ ≤ 11 / 10 := by
  have hl := sqrt5_lo
  have hh := sqrt5_hi
  have h1 : ‖z.2 i‖ ≤ 1 / 10 := by
    have h2 : ‖z.2‖ < 1 / 10 := by simpa using hz.2
    exact (norm_le_pi_norm z.2 i).trans h2.le
  have h3 : ‖(omegaStar i : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    fin_cases i
    · simp only [omegaStar, Fin.zero_eta, Matrix.cons_val_zero, iota, Real.norm_eq_abs]
      rw [abs_le]
      constructor <;> linarith
    · simp [omegaStar]
  have := norm_add_le (omegaStar i : ℂ) (z.2 i)
  linarith

/-- The bounds of `CALike` on `h_ε`, for `0 ≤ ε ≤ 1/1000`. -/
theorem plH_bounds {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 1000) {z : PS} (hz : z ∈ plB) :
    ‖fderiv ℂ (plH ε) z‖ ≤ 3 ∧ ‖hamiltonianVectorFieldℂ (plH ε) z‖ ≤ 3 ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ (plH ε)) z‖ ≤ 3 ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ (plH ε)) z‖ ≤ 3 := by
  have hA := im_pA_le hz
  have hB := im_pB_le hz
  have sA := norm_two_pi_eps_sin_le h0 hA
  have sB := norm_two_pi_eps_sin_le h0 hB
  have hpA := norm_pA_le
  have hpB := norm_pB_le
  have w0 := norm_omega_add_le 0 hz
  have w1 := norm_omega_add_le 1 hz
  have tA := norm_pT_le h0 pA norm_vA_le
  have tB := norm_pT_le h0 pB norm_vB_le
  have tA' : ‖pT ε pA vA‖ ≤ 40 * ε := by
    have := mul_le_mul_of_nonneg_left hpA (by positivity : 0 ≤ 40 * ε)
    linarith
  have tB' : ‖pT ε pB vB‖ ≤ 80 * ε := by
    have := mul_le_mul_of_nonneg_left hpB (by positivity : 0 ≤ 40 * ε)
    linarith
  rw [hamiltonianVectorField_plH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fderiv_plH]
    have n1 := norm_sub_le
      (((omegaStar 0 + z.2 0 : ℂ)) • pI 0 + ((omegaStar 1 + z.2 1 : ℂ)) • pI 1 -
        ((2 * π * ε * Complex.sin (2 * π * pA z) : ℂ)) • pA)
      (((2 * π * ε * Complex.sin (2 * π * pB z) : ℂ)) • pB)
    have n2 := norm_sub_le (((omegaStar 0 + z.2 0 : ℂ)) • pI 0 + ((omegaStar 1 + z.2 1 : ℂ)) • pI 1)
      (((2 * π * ε * Complex.sin (2 * π * pA z) : ℂ)) • pA)
    have n3 := norm_add_le (((omegaStar 0 + z.2 0 : ℂ)) • pI 0) (((omegaStar 1 + z.2 1 : ℂ)) • pI 1)
    have m0 : ‖((omegaStar 0 + z.2 0 : ℂ)) • pI 0‖ ≤ 11 / 10 := by
      rw [norm_smul]
      calc _ ≤ 11 / 10 * 1 := mul_le_mul w0 (norm_pI_le 0) (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have m1 : ‖((omegaStar 1 + z.2 1 : ℂ)) • pI 1‖ ≤ 11 / 10 := by
      rw [norm_smul]
      calc _ ≤ 11 / 10 * 1 := mul_le_mul w1 (norm_pI_le 1) (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have m2 : ‖((2 * π * ε * Complex.sin (2 * π * pA z) : ℂ)) • pA‖ ≤ 13 * ε := by
      rw [norm_smul]
      calc _ ≤ 13 * ε * 1 := mul_le_mul sA hpA (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have m3 : ‖((2 * π * ε * Complex.sin (2 * π * pB z) : ℂ)) • pB‖ ≤ 26 * ε := by
      rw [norm_smul]
      calc _ ≤ 13 * ε * 2 := mul_le_mul sB hpB (norm_nonneg _) (by positivity)
        _ = _ := by ring
    show ‖plDh ε z‖ ≤ 3
    unfold plDh
    linarith
  · refine (Prod.norm_def _).trans_le (max_le ?_ ?_)
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
      exact (norm_omega_add_le i hz).trans (by norm_num)
    · have n1 := norm_add_le ((2 * π * ε * Complex.sin (2 * π * pA z)) • vA)
        ((2 * π * ε * Complex.sin (2 * π * pB z)) • vB)
      have m2 : ‖(2 * π * ε * Complex.sin (2 * π * pA z) : ℂ) • vA‖ ≤ 13 * ε := by
        rw [norm_smul]
        calc _ ≤ 13 * ε * 1 := mul_le_mul sA norm_vA_le (norm_nonneg _) (by positivity)
          _ = _ := by ring
      have m3 : ‖(2 * π * ε * Complex.sin (2 * π * pB z) : ℂ) • vB‖ ≤ 13 * ε := by
        rw [norm_smul]
        calc _ ≤ 13 * ε * 1 := mul_le_mul sB norm_vB_le (norm_nonneg _) (by positivity)
          _ = _ := by ring
      show ‖(2 * π * ε * Complex.sin (2 * π * pA z)) • vA +
        (2 * π * ε * Complex.sin (2 * π * pB z)) • vB‖ ≤ 3
      linarith
  · rw [fderiv_plX]
    have n1 := norm_add_le (pS + Complex.cos (2 * π * pA z) • pT ε pA vA)
      (Complex.cos (2 * π * pB z) • pT ε pB vB)
    have n2 := norm_add_le pS (Complex.cos (2 * π * pA z) • pT ε pA vA)
    have m1 : ‖Complex.cos (2 * π * pA z) • pT ε pA vA‖ ≤ 80 * ε := by
      rw [norm_smul]
      calc _ ≤ 2 * (40 * ε) := mul_le_mul (norm_cos_le_two hA) tA' (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    have m2 : ‖Complex.cos (2 * π * pB z) • pT ε pB vB‖ ≤ 160 * ε := by
      rw [norm_smul]
      calc _ ≤ 2 * (80 * ε) := mul_le_mul (norm_cos_le_two hB) tB' (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    have hS := norm_pS_le
    show ‖plDX ε z‖ ≤ 3
    unfold plDX
    linarith
  · rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one, fderiv_plX,
      (hasFDerivAt_plDX ε z).fderiv]
    have hpi := pi_lt
    have hpi0 := Real.pi_pos
    have two_pi : ‖(2 * π : ℂ)‖ ≤ 13 / 2 := by
      rw [norm_mul, Complex.norm_real]
      simp only [Real.norm_eq_abs, abs_of_pos hpi0]
      norm_num
      linarith
    have n1 := norm_add_le
      (((-(Complex.sin (2 * π * pA z)) * (2 * π) : ℂ) • pA).smulRight (pT ε pA vA))
      (((-(Complex.sin (2 * π * pB z)) * (2 * π) : ℂ) • pB).smulRight (pT ε pB vB))
    have mS : ∀ {w : ℂ}, |w.im| ≤ 1 / 2 → ‖(-(Complex.sin w) * (2 * π) : ℂ)‖ ≤ 13 := by
      intro w hw
      rw [norm_mul, norm_neg]
      calc _ ≤ 2 * (13 / 2) := mul_le_mul (norm_sin_le_two hw) two_pi (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have m1 : ‖((-(Complex.sin (2 * π * pA z)) * (2 * π) : ℂ) • pA).smulRight (pT ε pA vA)‖ ≤
        520 * ε := by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
      calc _ ≤ 13 * 1 * (40 * ε) := by
            refine mul_le_mul (mul_le_mul (mS hA) hpA (norm_nonneg _) (by norm_num)) tA'
              (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    have m2 : ‖((-(Complex.sin (2 * π * pB z)) * (2 * π) : ℂ) • pB).smulRight (pT ε pB vB)‖ ≤
        2080 * ε := by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
      calc _ ≤ 13 * 2 * (80 * ε) := by
            refine mul_le_mul (mul_le_mul (mS hB) hpB (norm_nonneg _) (by norm_num)) tB'
              (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    show ‖plD2X ε z‖ ≤ 3
    unfold plD2X
    linarith

end KAM.Sharp2.Examples

end
