/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Cauchy
public import KAM.Strip.Regularity
public import KAM.Planetary.MaximalStep.Basic

/-!
# First-order Taylor part in the action (P11A-C3, `bpP:p11a:taylor-cutoff`)

For `F` admissible on `D(r,s;B)` with `|F| ≤ M`, the first-order Taylor polynomial `F^{(≤1)}` in
`η` at `η = 0` is admissible, bounded by `2M`, with remainder `≤ M q²/(1-q)` on `D(r,qs;B)`, and
the `η`-derivative at `η = 0` is bounded by `M/s`.

The one-variable input (`stepP:p11a:tc-line`) is the Cauchy power series of
`ζ ↦ F(θ, ζ η, b)` on the disc of radius `1/q`: its coefficients are `≤ M q^j`
(`p11_series_remainder`). The sup bound on the first derivative is the closed-ball Cauchy estimate
(`p11_norm_fderiv_le_of_ball`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KAM.Planetary

/-- `stepP:p11a:tc-line`: remainder of a one-variable power series bounded by `M` on the disc
of radius `1/q`. -/
theorem p11_series_remainder {g : ℂ → ℂ} {M q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : DifferentiableOn ℂ g (closedBall 0 (1 / q)))
    (hb : ∀ ζ ∈ closedBall (0 : ℂ) (1 / q), ‖g ζ‖ ≤ M) :
    ‖g 1 - g 0 - deriv g 0‖ ≤ M * q ^ 2 / (1 - q) := by
  have hR : (0 : ℝ) < 1 / q := one_div_pos.mpr hq0
  set R : ℝ≥0 := (1 / q).toNNReal with hRdef
  have hRc : (R : ℝ) = 1 / q := Real.coe_toNNReal _ hR.le
  have hRpos : 0 < R := by
    rw [← NNReal.coe_pos, hRc]; exact hR
  have hp := (hRc ▸ hd : DifferentiableOn ℂ g (closedBall 0 R)).hasFPowerSeriesOnBall hRpos
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_closedBall_self hR.le))
  have hcoeff : ∀ n, ‖cauchyPowerSeries g 0 R n‖ ≤ M * q ^ n := by
    intro n
    refine (norm_cauchyPowerSeries_le g 0 R n).trans ?_
    have hint : ∫ θ in (0 : ℝ)..2 * Real.pi, ‖g (circleMap 0 R θ)‖ ≤ M * (2 * Real.pi) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := 2 * Real.pi) (C := M) (f := fun θ => ‖g (circleMap 0 R θ)‖)
        (fun θ _ => by
          rw [norm_norm]
          refine hb _ ?_
          rw [← hRc]
          exact sphere_subset_closedBall (circleMap_mem_sphere 0 hRpos.le θ))
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      convert this using 2
      rw [abs_of_nonneg (by linarith [Real.pi_pos])]; ring
    have hinv : |(R : ℝ)|⁻¹ = q := by
      rw [hRc, abs_of_pos hR]; field_simp
    rw [hinv]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖g (circleMap 0 R θ)‖ ≤ M := by
      calc _ ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) := by gcongr
        _ = M := by field_simp
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hq0.le _)
  have hsum := hp.hasSum (y := 1) (by
    rw [Metric.mem_eball, edist_zero_right]
    have : ‖(1 : ℂ)‖₊ < R := by
      rw [← NNReal.coe_lt_coe, hRc]
      simp only [coe_nnnorm, norm_one]
      rw [lt_div_iff₀ hq0]; linarith
    exact ENNReal.coe_lt_coe.mpr this)
  rw [zero_add] at hsum
  have hsum2 := (hasSum_nat_add_iff' 2).mpr hsum
  have hgeo : HasSum (fun n : ℕ => M * q ^ 2 * q ^ n) (M * q ^ 2 * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
  have h0 : cauchyPowerSeries g 0 R 0 (fun _ => 1) = g 0 := hp.hasFPowerSeriesAt.coeff_zero _
  have h1 : cauchyPowerSeries g 0 R 1 (fun _ => 1) = deriv g 0 :=
    hp.hasFPowerSeriesAt.deriv.symm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, h0, h1] at hsum2
  have := hsum2.norm_le_of_bounded hgeo (fun n => by
    calc ‖cauchyPowerSeries g 0 R (n + 2) fun _ => 1‖
        ≤ ‖cauchyPowerSeries g 0 R (n + 2)‖ * ∏ _i : Fin (n + 2), ‖(1 : ℂ)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ M * q ^ (n + 2) := by simpa using hcoeff (n + 2)
      _ = M * q ^ 2 * q ^ n := by ring)
  rw [div_eq_mul_inv]
  convert this using 2
  rw [sub_sub]

/-- `stepP:p11a:tc-a`: Cauchy bound `M / s` for the derivative at the centre of a ball. -/
theorem p11_norm_fderiv_le_of_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {φ : E → ℂ} {s M : ℝ} (hs : 0 < s) (hd : DifferentiableOn ℂ φ (ball 0 s))
    (hb : ∀ w ∈ ball (0 : E) s, ‖φ w‖ ≤ M) : ‖fderiv ℂ φ 0‖ ≤ M / s := by
  have hδ : ∀ δ, 0 < δ → δ < s → ‖fderiv ℂ φ 0‖ * δ ≤ M := by
    intro δ h0 h1
    have hsub : closedBall (0 : E) δ ⊆ ball 0 s := closedBall_subset_ball h1
    have := KAM.norm_fderiv_le_of_closedBall_bound isOpen_ball hd h0 hsub
      (fun w hw => hb w (hsub hw))
    rwa [le_div_iff₀ h0] at this
  rw [le_div_iff₀ hs]
  by_contra hcon'
  have hcon := not_le.mp hcon'
  have hL : 0 < ‖fderiv ℂ φ 0‖ := by
    by_contra h0
    have : ‖fderiv ℂ φ 0‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_ball_self hs))
    rw [this] at hcon
    linarith
  have h2 := hδ ((M / ‖fderiv ℂ φ 0‖ + s) / 2) (by
      have : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_ball_self hs))
      positivity) (by
      have : M / ‖fderiv ℂ φ 0‖ < s := by rwa [div_lt_iff₀ hL, mul_comm]
      linarith)
  have h3 : M < ‖fderiv ℂ φ 0‖ * ((M / ‖fderiv ℂ φ 0‖ + s) / 2) := by
    have : M / ‖fderiv ℂ φ 0‖ < s := by rwa [div_lt_iff₀ hL, mul_comm]
    have e : ‖fderiv ℂ φ 0‖ * (M / ‖fderiv ℂ φ 0‖) = M := mul_div_cancel₀ _ hL.ne'
    nlinarith
  linarith

/-- `stepP:p11a:tc-b`: second-order remainder of a function bounded by `M` on `ball 0 s`,
evaluated at `‖η‖ < q s`. -/
theorem p11_taylor_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {φ : E → ℂ} {s M q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : DifferentiableOn ℂ φ (ball 0 s)) (hb : ∀ w ∈ ball (0 : E) s, ‖φ w‖ ≤ M)
    {η : E} (hη : ‖η‖ < q * s) :
    ‖φ η - φ 0 - fderiv ℂ φ 0 η‖ ≤ M * q ^ 2 / (1 - q) := by
  have hs : 0 < s := by
    by_contra h
    have := norm_nonneg η
    nlinarith
  have hmem : ∀ ζ ∈ closedBall (0 : ℂ) (1 / q), ζ • η ∈ ball (0 : E) s := by
    intro ζ hζ
    rw [mem_ball_zero_iff, norm_smul]
    have hζ' : ‖ζ‖ ≤ 1 / q := mem_closedBall_zero_iff.mp hζ
    calc ‖ζ‖ * ‖η‖ ≤ (1 / q) * ‖η‖ := by gcongr
      _ < (1 / q) * (q * s) := by gcongr
      _ = s := by field_simp
  have hdiffg : ∀ ζ ∈ closedBall (0 : ℂ) (1 / q), DifferentiableAt ℂ (fun ζ : ℂ => φ (ζ • η)) ζ := by
    intro ζ hζ
    exact ((hd.differentiableAt (isOpen_ball.mem_nhds (hmem ζ hζ))).comp ζ
      (differentiableAt_id.smul_const η))
  have h := p11_series_remainder (g := fun ζ : ℂ => φ (ζ • η)) hq0 hq1
    (fun ζ hζ => (hdiffg ζ hζ).differentiableWithinAt)
    (fun ζ hζ => hb _ (hmem ζ hζ)) (M := M)
  have hφ0 : DifferentiableAt ℂ φ 0 := hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hs))
  have hder : deriv (fun ζ : ℂ => φ (ζ • η)) 0 = fderiv ℂ φ 0 η := by
    have h1 : HasDerivAt (fun ζ : ℂ => ζ • η) η 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const η
    have h2 : HasFDerivAt φ (fderiv ℂ φ 0) ((fun ζ : ℂ => ζ • η) 0) := by
      simpa using hφ0.hasFDerivAt
    exact (h2.comp_hasDerivAt 0 h1).deriv
  simpa [hder] using h

theorem p11_mem_domain_def {n : ℕ} {r s : ℝ} {B : Set (P11CVec n)} {θ η b : P11CVec n} :
    ((θ, η), b) ∈ domain_def n r s B ↔ θ ∈ KAM.complexStrip n r ∧ ‖η‖ < s ∧ b ∈ B := by
  simp [domain_def, KAM.Weighted.Dom, KAM.Weighted.polyNbhd, and_assoc]

theorem p11_isOpen_domain_def {n : ℕ} (r s : ℝ) {B : Set (P11CVec n)} (hB : IsOpen B) :
    IsOpen (domain_def n r s B) :=
  (KAM.Weighted.isOpen_Dom _ _ _).prod hB

/-- The `η`-slice of an admissible function is holomorphic on `ball 0 s`. -/
theorem p11_slice_differentiableOn {n : ℕ} {r s : ℝ} {B : Set (P11CVec n)}
    {F : P11Family n → ℂ} (hF : DifferentiableOn ℂ F (domain_def n r s B))
    {θ b : P11CVec n} (hθ : θ ∈ KAM.complexStrip n r) (hb : b ∈ B) :
    DifferentiableOn ℂ (fun η => F ((θ, η), b)) (ball 0 s) := by
  refine hF.comp (f := fun η : P11CVec n => ((θ, η), b)) (by fun_prop) ?_
  intro η hη
  exact p11_mem_domain_def.mpr ⟨hθ, mem_ball_zero_iff.mp hη, hb⟩

/-- The derivative of the `η`-slice at `0`, as a function of the base point. -/
theorem p11_fderiv_slice {n : ℕ} {F : P11Family n → ℂ} {θ b : P11CVec n}
    (hF : DifferentiableAt ℂ F ((θ, 0), b)) :
    fderiv ℂ (fun η => F ((θ, η), b)) 0 =
      (fderiv ℂ F ((θ, 0), b)).comp
        (((0 : P11CVec n →L[ℂ] P11CVec n).prod (ContinuousLinearMap.id ℂ _)).prod
          (0 : P11CVec n →L[ℂ] P11CVec n)) := by
  have hψ : HasFDerivAt (fun η : P11CVec n => ((θ, η), b))
      (((0 : P11CVec n →L[ℂ] P11CVec n).prod (ContinuousLinearMap.id ℂ _)).prod
        (0 : P11CVec n →L[ℂ] P11CVec n)) 0 :=
    ((hasFDerivAt_const θ 0).prodMk (hasFDerivAt_id 0)).prodMk (hasFDerivAt_const b 0)
  exact (hF.hasFDerivAt.comp 0 hψ).fderiv

theorem p11_taylor_admissible {n : ℕ} {r s : ℝ} (hs : 0 < s) {B : Set (P11CVec n)}
    (hB : IsOpen B) {F : P11Family n → ℂ} (hF : p11Admissible r s B F) :
    p11Admissible r s B (p11Taylor F) := by
  set D := domain_def n r s B with hD
  have hDo : IsOpen D := p11_isOpen_domain_def r s hB
  have hc : ∀ z ∈ D, ((z.1.1, (0 : P11CVec n)), z.2) ∈ D := by
    rintro ⟨⟨θ, η⟩, b⟩ hz
    obtain ⟨h1, -, h3⟩ := p11_mem_domain_def.mp hz
    exact p11_mem_domain_def.mpr ⟨h1, by simpa using hs, h3⟩
  refine ⟨?_, ?_⟩
  · have hcd : DifferentiableOn ℂ (fun z : P11Family n => ((z.1.1, (0 : P11CVec n)), z.2)) D :=
      by fun_prop
    have hF1 := hF.1.comp hcd hc
    have hF2 := (KAM.differentiableOn_fderiv_of_isOpen hDo hF.1).comp hcd hc
    have hL : DifferentiableOn ℂ (fun z : P11Family n =>
        (((0 : P11CVec n →L[ℂ] P11CVec n).prod (ContinuousLinearMap.id ℂ _)).prod
          (0 : P11CVec n →L[ℂ] P11CVec n)) z.1.2) D := by fun_prop
    have := hF1.add (hF2.clm_apply hL)
    refine this.congr ?_
    rintro ⟨⟨θ, η⟩, b⟩ hz
    have hz' := hc _ hz
    simp only [p11Taylor]
    rw [p11_fderiv_slice (hF.1.differentiableAt (hDo.mem_nhds hz'))]
    rfl
  · rintro j ⟨⟨θ, η⟩, b⟩ hz
    obtain ⟨h1, h2, h3⟩ := p11_mem_domain_def.mp hz
    have hper := hF.2 j
    have hstrip : θ + Pi.single j 1 ∈ KAM.complexStrip n r := by
      intro i
      simpa [Pi.single_apply, apply_ite Complex.im] using h1 i
    have hev : (fun η' => F ((θ + Pi.single j 1, η'), b)) =ᶠ[nhds 0]
        (fun η' => F ((θ, η'), b)) := by
      filter_upwards [ball_mem_nhds (0 : P11CVec n) hs] with η' hη'
      exact hper ((θ, η'), b) (p11_mem_domain_def.mpr ⟨h1, mem_ball_zero_iff.mp hη', h3⟩)
    have h0 := hper ((θ, 0), b) (p11_mem_domain_def.mpr ⟨h1, by simpa using hs, h3⟩)
    simp only [p11Taylor] at h0 ⊢
    rw [hev.fderiv_eq, h0]

/-- `bpP:p11a:taylor-cutoff`. -/
theorem taylor_cutoff {n : ℕ} {r s M q : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hM : 0 ≤ M) (hq : 0 < q) (hq1 : q < 1)
    {B : Set (P11CVec n)} (hB : IsOpen B) {F : P11Family n → ℂ}
    (hF : p11Admissible r s B F) (hb : p11Bound (domain_def n r s B) F M) :
    p11Admissible r s B (p11Taylor F) ∧
    p11Bound (domain_def n r s B) (p11Taylor F) (2*M) ∧
    p11Bound (domain_def n r (q*s) B) (F-p11Taylor F) (M*q^2/(1-q)) ∧
    ∀ theta ∈ KAM.complexStrip n r, ∀ b ∈ B,
      ‖fderiv ℂ (fun eta => F ((theta,eta),b)) 0‖ ≤ M/s := by
  have hslice : ∀ θ ∈ KAM.complexStrip n r, ∀ b ∈ B,
      ‖fderiv ℂ (fun eta => F ((θ, eta), b)) 0‖ ≤ M / s := fun θ hθ b hb' =>
    p11_norm_fderiv_le_of_ball hs (p11_slice_differentiableOn hF.1 hθ hb')
      (fun w hw => hb _ (p11_mem_domain_def.mpr ⟨hθ, mem_ball_zero_iff.mp hw, hb'⟩))
  refine ⟨p11_taylor_admissible hs hB hF, ?_, ?_, fun θ hθ b hb' => hslice θ hθ b hb'⟩
  · rintro ⟨⟨θ, η⟩, b⟩ hz
    obtain ⟨h1, h2, h3⟩ := p11_mem_domain_def.mp hz
    have h0 := hb ((θ, 0), b) (p11_mem_domain_def.mpr ⟨h1, by simpa using hs, h3⟩)
    have hd := hslice θ h1 b h3
    simp only [p11Taylor]
    calc ‖F ((θ, 0), b) + (fderiv ℂ (fun eta => F ((θ, eta), b)) 0) η‖
        ≤ ‖F ((θ, 0), b)‖ + ‖fderiv ℂ (fun eta => F ((θ, eta), b)) 0‖ * ‖η‖ :=
          (norm_add_le _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
      _ ≤ M + M / s * s := by gcongr
      _ = 2 * M := by field_simp; ring
  · rintro ⟨⟨θ, η⟩, b⟩ hz
    obtain ⟨h1, h2, h3⟩ := p11_mem_domain_def.mp hz
    have h2' : ‖η‖ < s := h2.trans_le (by nlinarith)
    have := p11_taylor_remainder (φ := fun eta => F ((θ, eta), b)) (s := s) (M := M) hq hq1
      (p11_slice_differentiableOn hF.1 h1 h3)
      (fun w hw => hb _ (p11_mem_domain_def.mpr ⟨h1, mem_ball_zero_iff.mp hw, h3⟩)) h2
    simp only [Pi.sub_apply, p11Taylor]
    convert this using 2
    ring

end KAM.Planetary
