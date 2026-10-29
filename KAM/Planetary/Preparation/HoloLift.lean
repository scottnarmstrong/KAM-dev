/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Holomorphic
public import KAM.Planetary.Preparation.HoloData
public import KAM.Planetary.SecularSpectrum.Lift
public import KAM.Planetary.SecularSpectrum.Diagonalize

/-!
# The lift on real points (P11A-P2b, `stepP:p11:hc-lift`)

The literal inverse lift `p11ChartInput C` of the secular data equals the real inverse lift
`SecularSpectrum.liftInv R` of the real frame `R` after the period conversion
(`p11ChartInput_eq_liftInv`, via `rotDiag_liftInv_assemble` and `p11_fderiv_rho_real`: the complex
derivative of `ρ` along a real direction is the entrywise complexification of the real
derivative of `R`), and the elementary bounds `‖ρ x‖ ≤ B ‖x‖`, `|H_ρ| ≤ n B' ‖y‖ ‖x‖`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology
namespace KAM.Planetary

section Lift

variable {n : ℕ}

theorem p11_mat_entry_hasFDerivAt {𝕜 F E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {Φ : E → Matrix (Fin n) (Fin n) F} {Φ' : E →L[𝕜] Matrix (Fin n) (Fin n) F} {x : E}
    (h : HasFDerivAt Φ Φ' x) (i j : Fin n) :
    HasFDerivAt (fun y => Φ y i j)
      ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => F) j).comp
        ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => Fin n → F) i).comp Φ')) x := by
  have h1 := (hasFDerivAt_pi'.1
    (show HasFDerivAt (fun y => (Φ y : Fin n → Fin n → F)) Φ' x from h)) i
  exact (hasFDerivAt_pi'.1 h1) j

open scoped Matrix.Norms.Elementwise in
/-- The complex derivative of `ρ` along a real direction is the complexified real derivative of
the real frame `R`. -/
theorem p11_fderiv_rho_real {ρ : P11CVec n → Matrix (Fin n) (Fin n) ℂ}
    {R : P11Vec n → Matrix (Fin n) (Fin n) ℝ} {L : P11Vec n}
    (hρ : DifferentiableAt ℂ ρ (KAM.realInclusion n L))
    (hev : ∀ᶠ y in 𝓝 L, ρ (KAM.realInclusion n y) = (R y).map (fun r : ℝ => (r : ℂ)))
    (hR : DifferentiableAt ℝ R L) (v : P11Vec n) :
    fderiv ℂ ρ (KAM.realInclusion n L) (KAM.realInclusion n v) =
      (fderiv ℝ R L v).map (fun r : ℝ => (r : ℂ)) := by
  ext i j
  have hA0 := (hρ.hasFDerivAt.restrictScalars ℝ).comp L (KAM.realInclusion n).hasFDerivAt
  have hA := p11_mat_entry_hasFDerivAt (𝕜 := ℝ) hA0 i j
  have hB := Complex.ofRealCLM.hasFDerivAt.comp L (p11_mat_entry_hasFDerivAt (𝕜 := ℝ)
    hR.hasFDerivAt i j)
  have hA' : HasFDerivAt (fun y => ((R y i j : ℝ) : ℂ)) _ L :=
    hA.congr_of_eventuallyEq (by
      filter_upwards [hev] with y hy
      simp [Function.comp, hy])
  have := congrArg (fun T => T v) (hA'.unique hB)
  exact this

open scoped Matrix.Norms.Elementwise in
/-- `hc-lift` on real points: the literal inverse lift is the real inverse lift after the period
conversion `T₁`. -/
theorem p11ChartInput_eq_liftInv (C : P11SecularData n)
    {R : P11Vec n → Matrix (Fin n) (Fin n) ℝ} (z : Phase (n + n))
    (hρ : DifferentiableAt ℂ C.rho (KAM.realInclusion n (fun i => fast z.2 i / (2 * Real.pi))))
    (hev : ∀ᶠ y in 𝓝 (fun i => fast z.2 i / (2 * Real.pi)),
      C.rho (KAM.realInclusion n y) = (R y).map (fun r : ℝ => (r : ℂ)))
    (hR : DifferentiableAt ℝ R (fun i => fast z.2 i / (2 * Real.pi))) :
    p11ChartInput C z = SecularSpectrum.liftInv R
      (assemble (fun i => fast z.2 i / (2 * Real.pi)) (fun l => 2 * Real.pi * fast z.1 l)
        (slow z.2) (slow z.1)) := by
  set L : P11Vec n := fun i => fast z.2 i / (2 * Real.pi) with hL
  have hρL : C.rho (KAM.realInclusion n L) = (R L).map (fun r : ℝ => (r : ℂ)) := hev.self_of_nhds
  have hder : ∀ l : Fin n, fderiv ℂ C.rho (KAM.realInclusion n L) (Pi.single l 1) =
      (fderiv ℝ R L (Pi.single l 1)).map (fun r : ℝ => (r : ℂ)) := fun l => by
    have h1 := p11_fderiv_rho_real hρ hev hR (Pi.single l 1)
    have h2 : KAM.realInclusion n (Pi.single l (1 : ℝ)) = Pi.single l (1 : ℂ) := by
      ext k; simp [Pi.single_apply]; split_ifs <;> simp
    rwa [h2] at h1
  rw [SecularSpectrum.rotDiag_liftInv_assemble]
  simp only [p11ChartInput]
  rw [← hL, hρL]
  have hmv : ∀ v : P11Vec n, ∀ i,
      (((R L).map (fun r : ℝ => (r : ℂ))).mulVec (KAM.realInclusion n v) i).re =
        (R L).mulVec v i := fun v i => by
    have : ((R L).map (fun r : ℝ => (r : ℂ))).mulVec (KAM.realInclusion n v) i =
        (((R L).mulVec v i : ℝ) : ℂ) := by
      simp [Matrix.mulVec, dotProduct]
    rw [this, Complex.ofReal_re]
  have hTM : ∀ A B : Matrix (Fin n) (Fin n) ℝ,
      (A.map (fun r : ℝ => (r : ℂ))).transpose * B.map (fun r : ℝ => (r : ℂ)) =
        (A.transpose * B).map (fun r : ℝ => (r : ℂ)) := fun A B => by
    ext i j; simp [Matrix.mul_apply]
  have hθ : ∀ l : Fin n, (∑ i, ∑ j, KAM.realInclusion n (slow z.2) i *
      (((R L).map (fun r : ℝ => (r : ℂ))).transpose *
        (fderiv ℝ R L (Pi.single l 1)).map (fun r : ℝ => (r : ℂ))) i j *
      KAM.realInclusion n (slow z.1) j).re =
      ∑ i, slow z.2 i * ((R L).transpose * fderiv ℝ R L (Pi.single l 1)).mulVec (slow z.1) i :=
    fun l => by
    rw [hTM]
    have : (∑ i, ∑ j, KAM.realInclusion n (slow z.2) i *
        (((R L).transpose * fderiv ℝ R L (Pi.single l 1)).map (fun r : ℝ => (r : ℂ))) i j *
        KAM.realInclusion n (slow z.1) j) =
        ((∑ i, slow z.2 i * ((R L).transpose * fderiv ℝ R L (Pi.single l 1)).mulVec
          (slow z.1) i : ℝ) : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, KAM.realInclusion_apply]
      push_cast
      simp [Finset.mul_sum, mul_assoc]
    rw [this, Complex.ofReal_re]
  simp only [hder, hmv, hθ]
  rfl

/-- `hc-lift`: `‖A x‖ ≤ B ‖x‖` from the row-sum bound. -/
theorem p11_mulVec_bound {A : Matrix (Fin n) (Fin n) ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i, ∑ j, ‖A i j‖ ≤ B) (x : P11CVec n) : ‖A.mulVec x‖ ≤ B * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖A.mulVec x i‖ = ‖∑ j, A i j * x j‖ := by simp [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ B * ‖x‖ := mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _)

/-- `hc-lift`: `|H_ρ| ≤ n B' ‖y‖ ‖x‖` for the angle correction `∑ᵢⱼ yᵢ Aᵢⱼ xⱼ`. -/
theorem p11_angle_correction_bound {A : Matrix (Fin n) (Fin n) ℂ} {B : ℝ}
    (hA : ∀ i, ∑ j, ‖A i j‖ ≤ B) (x y : P11CVec n) :
    ‖∑ i, ∑ j, y i * A i j * x j‖ ≤ n * B * (‖y‖ * ‖x‖) := by
  calc ‖∑ i, ∑ j, y i * A i j * x j‖ ≤ ∑ i, ‖∑ j, y i * A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, B * (‖y‖ * ‖x‖) := Finset.sum_le_sum fun i _ => by
        calc ‖∑ j, y i * A i j * x j‖ ≤ ∑ j, ‖y i * A i j * x j‖ := norm_sum_le _ _
          _ ≤ ∑ j, ‖y‖ * ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
              rw [norm_mul, norm_mul]
              exact mul_le_mul (mul_le_mul_of_nonneg_right (norm_le_pi_norm y i) (norm_nonneg _))
                (norm_le_pi_norm x j) (norm_nonneg _) (by positivity)
          _ = ‖y‖ * (∑ j, ‖A i j‖) * ‖x‖ := by
              rw [Finset.mul_sum, Finset.sum_mul]
          _ ≤ B * (‖y‖ * ‖x‖) := by
              have := mul_le_mul_of_nonneg_left (hA i) (norm_nonneg y)
              nlinarith [norm_nonneg x, norm_nonneg y]
    _ = n * B * (‖y‖ * ‖x‖) := by simp [mul_assoc]

/-- The lift bounds `|ρ x| ≤ B_ρ |x|`, `|H_ρ| ≤ n B'_ρ |y| |x|` from the interface. -/
theorem P11HoloData.lift_bounds {D : P11Physical n} (d : P11HoloData D) {J : P11CVec n}
    (hJ : J ∈ Metric.ball ((2 * Real.pi)⁻¹ • KAM.realInclusion n d.J0) (d.rC / Real.pi))
    (x y : P11CVec n) (l : Fin n) :
    ‖(d.rho J).mulVec x‖ ≤ d.Brho * ‖x‖ ∧
    ‖∑ i, ∑ j, y i * ((d.rho J).transpose * fderiv ℂ d.rho J (Pi.single l 1)) i j * x j‖ ≤
      n * d.Bdrho * (‖y‖ * ‖x‖) := by
  obtain ⟨-, hb⟩ := d.rho_bounds
  obtain ⟨-, h1, h2⟩ := hb J hJ
  exact ⟨p11_mulVec_bound (zero_le_one.trans d.one_le_Brho) h1 x,
    p11_angle_correction_bound (h2 l) x y⟩

open scoped Matrix.Norms.Elementwise in
/-- `hc-lift`, interface form: on the real points over the frame ball, the literal inverse lift
of any secular data using the interface's `ρ` is the real inverse lift of the real frame `R`. -/
theorem P11HoloData.chartInput_eq_liftInv {D : P11Physical n} (d : P11HoloData D)
    (C : P11SecularData n) (hC : C.rho = d.rho) (z : Phase (n + n))
    (hz : ‖(fun i => fast z.2 i / (2 * Real.pi)) - (2 * Real.pi)⁻¹ • d.J0‖ < d.t2) :
    p11ChartInput C z = SecularSpectrum.liftInv d.R
      (assemble (fun i => fast z.2 i / (2 * Real.pi)) (fun l => 2 * Real.pi * fast z.1 l)
        (slow z.2) (slow z.1)) := by
  set L : P11Vec n := fun i => fast z.2 i / (2 * Real.pi) with hL
  have hzb : L ∈ Metric.ball ((2 * Real.pi)⁻¹ • d.J0) d.t2 := by rwa [mem_ball_iff_norm]
  have hzc : KAM.realInclusion n L ∈
      Metric.ball (KAM.realInclusion n ((2 * Real.pi)⁻¹ • d.J0)) d.t2 :=
    KAM.realInclusion_mem_ball_iff.2 hzb
  refine p11ChartInput_eq_liftInv C z ?_ ?_ ?_
  · rw [hC]
    have hd : DifferentiableOn ℂ (fun z => (d.rho z : Fin n → Fin n → ℂ))
        (Metric.ball (KAM.realInclusion n ((2 * Real.pi)⁻¹ • d.J0)) d.t2) :=
      differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => d.rho_diff i j
    exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hzc)
  · rw [hC]
    filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy
    exact d.rho_real y (by rwa [mem_ball_iff_norm] at hy)
  · have hb1 : L ∈ Metric.ball ((2 * Real.pi)⁻¹ • d.J0) d.t1 :=
      Metric.ball_subset_ball d.t2_le hzb
    have : ∀ i j, DifferentiableAt ℝ (fun x => d.R x i j) L := fun i j =>
      (d.R_analytic i j L hb1).differentiableAt
    exact differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => this i j

end Lift

end KAM.Planetary

end
