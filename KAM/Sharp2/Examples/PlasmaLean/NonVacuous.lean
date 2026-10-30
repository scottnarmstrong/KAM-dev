/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.PlasmaLean
public import KAM.Sharp2.Examples.PlasmaLean.Witness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# `plasmaLean_torus` is not vacuous

For the two-wave Hamiltonian `h_ε` of `Witness` and the flat torus `plK θ = (θ, 0)`:
the Gram matrix and the torsion are the identity, so `CALike plB (h_ε) plK ω*` holds for every
`0 ≤ ε ≤ 1/1000` (`caLike_plH`), and in particular:

* `caLike_nonempty`: the hypotheses of `plasmaLean_torus` can be met;
* `plasmaLean_torus_integrable`: at `ε = 0` the torus is invariant, the error is `0`, and the
  theorem applies;
* `plasmaLean_torus_twoWave`: for `0 < ε ≤ 7·10⁻¹⁹` the error is `≤ 26 ε ≤ 1.93·10⁻¹⁷`, it is
  not zero (`invarianceError_plH_ne_zero`), and the theorem produces a true invariant torus of a
  flow for which `plK` is not invariant.
-/

@[expose] public noncomputable section

open Real MeasureTheory
open scoped Matrix.Norms.Operator

namespace KAM.Sharp2.Examples

open KAM KAM.Torus KAM.Apost

/-- The flat torus. -/
def plK (θ : Fin 2 → ℂ) : PS := (θ, 0)

theorem fderiv_plK (θ : Fin 2 → ℂ) :
    fderiv ℂ plK θ = ContinuousLinearMap.inl ℂ (Fin 2 → ℂ) (Fin 2 → ℂ) :=
  (ContinuousLinearMap.inl ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).hasFDerivAt.fderiv

theorem differentiable_plK : Differentiable ℂ plK :=
  (ContinuousLinearMap.inl ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).differentiable

theorem gramMatrix_plK (θ : Fin 2 → ℂ) : gramMatrix plK θ = 1 := by
  ext i j
  simp only [gramMatrix, dotℂ, fderiv_plK, ContinuousLinearMap.inl_apply, Pi.zero_apply,
    mul_zero, add_zero]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]

theorem normalFrame_plK (θ : Fin 2 → ℂ) (j : Fin 2) :
    normalFrame plK θ j = (0, Pi.single j 1) := by
  simp only [normalFrame, gramMatrix_plK, inv_one, fderiv_plK, ContinuousLinearMap.inl_apply,
    omegaZero, Fin.sum_univ_two]
  revert j
  rw [Fin.forall_fin_two]
  constructor <;> simp

theorem rowSum_one (i : Fin 2) : ∑ j, ‖(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ = 1 := by
  revert i
  rw [Fin.forall_fin_two]
  constructor <;> simp [Fin.sum_univ_two]

theorem torsion_plH (ε : ℝ) (θ : Fin 2 → ℂ) : torsion (plH ε) plK omegaStar θ = 1 := by
  ext i j
  simp only [torsion, fderiv_fun_const, Pi.zero_apply, zero_apply, sub_zero,
    hamiltonianVectorField_plH, fderiv_plX, normalFrame_plK]
  fin_cases i <;> fin_cases j <;> simp [plDX, dotℂ, omegaZero, Fin.sum_univ_two]

theorem volume_cube :
    (volume (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1))) = 1 := by
  rw [volume_pi_pi]
  simp

theorem torsionAverage_plH (ε : ℝ) : torsionAverage (plH ε) plK omegaStar = 1 := by
  ext i j
  simp only [torsionAverage, torsion_plH]
  rw [setIntegral_const, Measure.real, volume_cube]
  simp

theorem plB_mem_ball {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (1 / 50)) :
    Metric.ball (plK θ) (1 / 160) ⊆ plB := by
  intro w hw
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hw
  obtain ⟨h1, h2⟩ := hw
  refine ⟨fun i => ?_, ?_⟩
  · have h3 : dist (w.1 i) (θ i) ≤ dist w.1 θ := dist_le_pi_dist _ _ i
    have h4 : |(w.1 i - θ i).im| ≤ ‖w.1 i - θ i‖ := Complex.abs_im_le_norm _
    rw [dist_eq_norm] at h3
    have h5 : |(θ i).im| < 1 / 50 := hθ i
    have h6 : (w.1 i - θ i).im + (θ i).im = (w.1 i).im := by simp
    have h7 := abs_add_le (w.1 i - θ i).im (θ i).im
    rw [h6] at h7
    have h8 : dist w.1 θ < 1 / 160 := h1
    show |(w.1 i).im| < 1 / 30
    linarith
  · have h3 : dist w.2 0 < 1 / 160 := h2
    rw [Metric.mem_ball]
    linarith

/-- The cA-like bounds hold for the two-wave Hamiltonian and the flat torus. -/
theorem caLike_plH {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 1000) :
    CALike plB (plH ε) plK omegaStar where
  isOpen := (isOpen_complexStrip 2 _).prod Metric.isOpen_ball
  transl := fun z hz k => by
    refine ⟨fun i => ?_, hz.2⟩
    have : (z.1 i + (k i : ℂ)).im = (z.1 i).im := by simp
    simpa [this] using hz.1 i
  holo := (differentiable_plH ε).differentiableOn
  periodic := fun z _ k => by
    have e1 : (2 * π * (z.1 0 + (k 0 : ℂ)) : ℂ) = 2 * π * z.1 0 + (k 0 : ℂ) * (2 * π) := by ring
    have e2 : (2 * π * (z.1 0 + (k 0 : ℂ) + (z.1 1 + (k 1 : ℂ))) : ℂ) =
        2 * π * (z.1 0 + z.1 1) + ((k 0 + k 1 : ℤ) : ℂ) * (2 * π) := by
      push_cast
      ring
    simp only [plH, Pi.add_apply, e1, e2, Complex.cos_add_int_mul_two_pi]
  real := fun θ I _ => by
    have e : plH ε ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) =
        ((omegaStar 0 * I 0 + 1 / 2 * I 0 ^ 2 + (omegaStar 1 * I 1 + 1 / 2 * I 1 ^ 2) +
          ε * (Real.cos (2 * π * θ 0) + Real.cos (2 * π * (θ 0 + θ 1))) : ℝ) : ℂ) := by
      simp [plH, Fin.sum_univ_two]
    rw [e, Complex.ofReal_im]
  bounds := fun z hz => plH_bounds h0 h1 hz
  torus_holo := differentiable_plK.differentiableOn
  primary := fun θ _ k => by simp [plK]
  torus_real := fun θ => ⟨(θ, 0), Prod.ext rfl (funext fun _ => by simp [plK])⟩
  ball := fun θ hθ => plB_mem_ball hθ
  deriv_le := fun θ _ => by
    rw [fderiv_plK]
    exact (ContinuousLinearMap.norm_inl_le_one ℂ _ _).trans (by norm_num)
  gram := fun θ _ => by
    rw [gramMatrix_plK, inv_one]
    exact ⟨by simp, fun i => by rw [rowSum_one]; norm_num⟩
  twist_unit := by
    rw [torsionAverage_plH]
    simp
  twist_le := fun i => by
    rw [torsionAverage_plH, inv_one, rowSum_one]
    norm_num
  torsion_le := fun θ _ => by
    rw [torsion_plH]
    exact (norm_le_of_rowSum_le le_rfl fun i => (rowSum_one i).le).trans (by norm_num)

/-- **Non-vacuity of `CALike`.** -/
theorem caLike_nonempty : ∃ (𝔅 : Set PS) (h : PS → ℂ) (K : (Fin 2 → ℂ) → PS),
    CALike 𝔅 h K omegaStar :=
  ⟨plB, plH 0, plK, caLike_plH le_rfl (by norm_num)⟩

/-- The invariance error of the flat torus. -/
theorem invarianceError_plH (ε : ℝ) (θ : Fin 2 → ℂ) :
    invarianceError (plH ε) plK omegaStar θ =
      (0, (2 * π * ε * Complex.sin (2 * π * θ 0)) • vA +
        (2 * π * ε * Complex.sin (2 * π * (θ 0 + θ 1))) • vB) := by
  simp only [invarianceError, hamiltonianVectorField_plH, fderiv_plK]
  refine Prod.ext (funext fun i => ?_) ?_ <;> simp [plX, plK]

/-- At `ε = 0` the flat torus is invariant, and the theorem applies with `e = 0`. -/
theorem plasmaLean_torus_integrable :
    ∃ Kinf : (Fin 2 → ℂ) → PS,
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError (plH 0) Kinf omegaStar θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ plB) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - plK θ‖ ≤ 22226503 * 0 := by
  refine plasmaLean_torus (caLike_plH le_rfl (by norm_num)) (fun θ _ => ?_) (by norm_num)
  rw [invarianceError_plH]
  simp

/-- On the strip `ρ = 1/50` the error of the flat torus is at most `26 ε`. -/
theorem norm_invarianceError_plH_le {ε : ℝ} (h0 : 0 ≤ ε) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (1 / 50)) : ‖invarianceError (plH ε) plK omegaStar θ‖ ≤ 26 * ε := by
  have hz : plK θ ∈ plB := plB_mem_ball hθ (Metric.mem_ball_self (by norm_num))
  have sA := norm_two_pi_eps_sin_le h0 (im_pA_le hz)
  have sB := norm_two_pi_eps_sin_le h0 (im_pB_le hz)
  rw [invarianceError_plH, Prod.norm_def]
  refine max_le (by simp; positivity) ?_
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have m1 : ‖(2 * π * ε * Complex.sin (2 * π * θ 0) : ℂ)‖ * ‖vA‖ ≤ 13 * ε * 1 :=
    mul_le_mul sA norm_vA_le (norm_nonneg _) (by positivity)
  have m2 : ‖(2 * π * ε * Complex.sin (2 * π * (θ 0 + θ 1)) : ℂ)‖ * ‖vB‖ ≤ 13 * ε * 1 :=
    mul_le_mul sB norm_vB_le (norm_nonneg _) (by positivity)
  linarith

/-- The error of the flat torus does not vanish for `ε ≠ 0`, at `θ = (1/4, 1/4)`. -/
theorem invarianceError_plH_ne_zero {ε : ℝ} (hε : ε ≠ 0) :
    invarianceError (plH ε) plK omegaStar (fun _ => 1 / 4) ≠ 0 := by
  rw [invarianceError_plH]
  have e1 : (2 * π * (1 / 4) : ℂ) = π / 2 := by ring
  have e2 : (2 * π * (1 / 4 + 1 / 4) : ℂ) = π := by ring
  simp only [e1, e2, Complex.sin_pi_div_two, Complex.sin_pi, mul_zero, zero_smul, add_zero, mul_one]
  intro h
  have h1 := congrFun (congrArg Prod.snd h) 0
  simp only [Pi.smul_apply, vA, Matrix.cons_val_zero, smul_eq_mul, mul_one, Prod.snd_zero,
    Pi.zero_apply] at h1
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) hε' h1

/-- **A non-trivial instance of `plasmaLean_torus`.** For `0 ≤ ε ≤ 7·10⁻¹⁹` the flat torus is an
approximate torus of `h_ε`, with error `≤ 26 ε ≤ 1.93·10⁻¹⁷`, and a true invariant torus of `h_ε`
of frequency `ω*` lies within `22226503 · 26 ε`. -/
theorem plasmaLean_torus_twoWave {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 7 / 10 ^ 19) :
    ∃ Kinf : (Fin 2 → ℂ) → PS,
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError (plH ε) Kinf omegaStar θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ plB) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - plK θ‖ ≤ 22226503 * (26 * ε) :=
  plasmaLean_torus (caLike_plH h0 (h1.trans (by norm_num)))
    (fun _ hθ => norm_invarianceError_plH_le h0 hθ) (by linarith)

end KAM.Sharp2.Examples

end
