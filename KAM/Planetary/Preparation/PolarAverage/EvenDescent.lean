/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PolarAverage.ParamIntegral

/-!
# Descent of an even holomorphic function to its square (P11A-P6 helper)

If `h(s, p)` is holomorphic on `D(0, R) × Ω` and even in `s`, then `(u, p) ↦ h(√u, p)` is
holomorphic on `D(0, R²) × Ω`, with the principal square root `Complex.sqrt` and no branch
condition on `u`.

On the polydisc `‖u‖ < R'²` the function is the parameter Cauchy integral
`(2πi)⁻¹ ∮_{|w| = R'} h(w, p) · w / (w² - u) dw`: partial fractions split the kernel into
`(w - s)⁻¹ + (w + s)⁻¹` with `s² = u`, and evenness identifies the two Cauchy values. The integral
is holomorphic in `(u, p)` by `p11_differentiableOn_paramIntegral`.
-/

@[expose] public section

open Set MeasureTheory Metric Filter
open scoped Topology Real

namespace KAM.Planetary

theorem p11_sqrt_sq (a : ℂ) : Complex.sqrt a ^ 2 = a := by
  simp [Complex.sqrt]

theorem p11_norm_sqrt_sq (a : ℂ) : ‖Complex.sqrt a‖ ^ 2 = ‖a‖ := by
  rw [← norm_pow, p11_sqrt_sq]

/-- Cauchy value of the descent kernel on a circle. -/
theorem p11_circle_descent {φ : ℂ → ℂ} {R' : ℝ} (hR' : 0 < R')
    (hφ : DifferentiableOn ℂ φ (closedBall 0 R')) (hev : ∀ s ∈ ball (0 : ℂ) R', φ (-s) = φ s)
    {u : ℂ} (hu : ‖u‖ < R' ^ 2) :
    (2 * π * Complex.I)⁻¹ • (∮ w in C(0, R'), φ w * (w / (w ^ 2 - u))) = φ (Complex.sqrt u) := by
  set s := Complex.sqrt u with hs
  have hsq : s ^ 2 = u := p11_sqrt_sq u
  have hsR : ‖s‖ < R' := by
    have h1 : ‖s‖ ^ 2 < R' ^ 2 := by rw [hs, p11_norm_sqrt_sq]; exact hu
    exact lt_of_pow_lt_pow_left₀ 2 hR'.le h1
  have hsm : s ∈ ball (0 : ℂ) R' := by simpa using hsR
  have hsm' : -s ∈ ball (0 : ℂ) R' := by simpa using hsR
  have hdc : DiffContOnCl ℂ φ (ball 0 R') := hφ.diffContOnCl_ball (Subset.refl _)
  have hc1 := hdc.circleIntegral_sub_inv_smul hsm
  have hc2 := hdc.circleIntegral_sub_inv_smul hsm'
  have hne : ∀ w ∈ sphere (0 : ℂ) R', w - s ≠ 0 ∧ w - -s ≠ 0 := by
    intro w hw
    have hwn : ‖w‖ = R' := by simpa using hw
    constructor
    · intro h0
      have : w = s := sub_eq_zero.mp h0
      rw [this] at hwn; linarith
    · intro h0
      have : w = -s := sub_eq_zero.mp h0
      rw [this, norm_neg] at hwn; linarith
  have hcont : ∀ x : ℂ, ‖x‖ < R' → ContinuousOn (fun w => (w - x)⁻¹ • φ w) (sphere 0 R') := by
    intro x hx
    refine ContinuousOn.smul ((continuousOn_id.sub continuousOn_const).inv₀ ?_)
      (hφ.continuousOn.mono sphere_subset_closedBall)
    intro w hw h0
    have hwn : ‖w‖ = R' := by simpa using hw
    have : w = x := sub_eq_zero.mp h0
    rw [this] at hwn; linarith
  have hi1 : CircleIntegrable (fun w => (w - s)⁻¹ • φ w) 0 R' :=
    (hcont s hsR).circleIntegrable hR'.le
  have hi2 : CircleIntegrable (fun w => (w - -s)⁻¹ • φ w) 0 R' :=
    (hcont (-s) (by simpa using hsR)).circleIntegrable hR'.le
  have hcongr : (∮ w in C(0, R'), φ w * (w / (w ^ 2 - u))) =
      (1 / 2 : ℂ) • ((∮ w in C(0, R'), (w - s)⁻¹ • φ w) +
        ∮ w in C(0, R'), (w - -s)⁻¹ • φ w) := by
    rw [← circleIntegral.integral_add hi1 hi2, ← circleIntegral.integral_smul]
    refine circleIntegral.integral_congr hR'.le fun w hw => ?_
    obtain ⟨h1, h2⟩ := hne w hw
    have h3 : w ^ 2 - u = (w - s) * (w - -s) := by rw [← hsq]; ring
    simp only [smul_eq_mul]
    rw [h3]
    field_simp
    ring
  rw [hcongr, hc1, hc2, hev s hsm]
  have h2pi : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Even holomorphic functions descend through the principal square root. -/
theorem p11_even_descent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] {Ω : Set E} (hΩ : IsOpen Ω)
    {R : ℝ} (hR : 0 < R) {h : ℂ × E → ℂ} (hd : DifferentiableOn ℂ h (ball (0 : ℂ) R ×ˢ Ω))
    (hev : ∀ s ∈ ball (0 : ℂ) R, ∀ p ∈ Ω, h (-s, p) = h (s, p)) :
    DifferentiableOn ℂ (fun q : ℂ × E => h (Complex.sqrt q.1, q.2))
      (ball (0 : ℂ) (R ^ 2) ×ˢ Ω) := by
  intro q₀ hq₀
  obtain ⟨hu₀, hp₀⟩ := hq₀
  set s₀ := Complex.sqrt q₀.1 with hs₀def
  have hs₀ : ‖s₀‖ < R := by
    have h1 : ‖s₀‖ ^ 2 < R ^ 2 := by
      rw [hs₀def, p11_norm_sqrt_sq]; simpa using hu₀
    exact lt_of_pow_lt_pow_left₀ 2 hR.le h1
  set R' : ℝ := (‖s₀‖ + R) / 2 with hR'def
  have hR'0 : 0 < R' := by positivity
  have hR'R : R' < R := by rw [hR'def]; linarith
  have hs₀R' : ‖s₀‖ < R' := by rw [hR'def]; linarith
  have hV : q₀ ∈ ball (0 : ℂ) (R' ^ 2) ×ˢ Ω := by
    refine ⟨?_, hp₀⟩
    rw [mem_ball_zero_iff, ← p11_norm_sqrt_sq q₀.1, ← hs₀def]
    exact pow_lt_pow_left₀ hs₀R' (norm_nonneg _) two_ne_zero
  have hVo : IsOpen (ball (0 : ℂ) (R' ^ 2) ×ˢ Ω) := isOpen_ball.prod hΩ
  -- the integrand
  let f : (ℂ × E) × ℂ → ℂ := fun x =>
    (x.2 * Complex.I) * (h (x.2, x.1.2) * (x.2 / (x.2 ^ 2 - x.1.1)))
  let W : Set ((ℂ × E) × ℂ) := {x | (x.2, x.1.2) ∈ ball (0 : ℂ) R ×ˢ Ω ∧ x.2 ^ 2 ≠ x.1.1}
  have hWo : IsOpen W := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_ball.prod hΩ).preimage (by fun_prop)
    · exact isOpen_ne_fun (f := fun x : (ℂ × E) × ℂ => x.2 ^ 2) (g := fun x => x.1.1)
        (by fun_prop) (by fun_prop)
  have hfd : DifferentiableOn ℂ f W := by
    have h1 : DifferentiableOn ℂ (fun x : (ℂ × E) × ℂ => h (x.2, x.1.2)) W :=
      hd.comp (by fun_prop) (fun x hx => hx.1)
    have h2 : DifferentiableOn ℂ (fun x : (ℂ × E) × ℂ => x.2 / (x.2 ^ 2 - x.1.1)) W := by
      have hn : DifferentiableOn ℂ (fun x : (ℂ × E) × ℂ => x.2) W := by fun_prop
      have hdn : DifferentiableOn ℂ (fun x : (ℂ × E) × ℂ => x.2 ^ 2 - x.1.1) W := by fun_prop
      have hinv : DifferentiableOn ℂ (fun x : (ℂ × E) × ℂ => (x.2 ^ 2 - x.1.1)⁻¹) W :=
        differentiableOn_inv.comp hdn (fun x (hx : x ∈ W) => sub_ne_zero.mpr hx.2)
      exact (hn.mul hinv).congr fun x _ => by simp [div_eq_mul_inv]
    exact (by fun_prop : DifferentiableOn ℂ (fun x : (ℂ × E) × ℂ => x.2 * Complex.I) W).mul
      (h1.mul h2)
  have hmem : ∀ q ∈ ball (0 : ℂ) (R' ^ 2) ×ˢ Ω, ∀ t ∈ Icc (0 : ℝ) (2 * π),
      (q, circleMap 0 R' t) ∈ W := by
    intro q hq t _
    obtain ⟨hq1, hq2⟩ := hq
    have hw : ‖circleMap 0 R' t‖ = R' := by simp [abs_of_pos hR'0]
    refine ⟨⟨?_, hq2⟩, ?_⟩
    · rw [mem_ball_zero_iff, hw]; exact hR'R
    · intro heq
      have : ‖q.1‖ = R' ^ 2 := by rw [← heq, norm_pow, hw]
      rw [mem_ball_zero_iff] at hq1
      linarith
  have hint := p11_differentiableOn_paramIntegral (μ := volume) (K := Icc (0 : ℝ) (2 * π))
    isCompact_Icc (γ := circleMap 0 R') (continuous_circleMap 0 R') hVo hWo hfd hmem
  have hint' := hint.const_smul (2 * π * Complex.I : ℂ)⁻¹
  have hEq : ∀ q ∈ ball (0 : ℂ) (R' ^ 2) ×ˢ Ω,
      h (Complex.sqrt q.1, q.2) =
        (2 * π * Complex.I)⁻¹ • ∫ t in Icc (0 : ℝ) (2 * π), f (q, circleMap 0 R' t) := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := hq
    have hφ : DifferentiableOn ℂ (fun w => h (w, q.2)) (closedBall 0 R') := by
      refine hd.comp (by fun_prop) fun w hw => ⟨?_, hq2⟩
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (mem_closedBall_zero_iff.mp hw) hR'R
    have hevq : ∀ s ∈ ball (0 : ℂ) R', h (-s, q.2) = h (s, q.2) := fun s hs =>
      hev s (ball_subset_ball hR'R.le hs) q.2 hq2
    have key := p11_circle_descent hR'0 hφ hevq (u := q.1) (by simpa using hq1)
    rw [← key]
    congr 1
    unfold circleIntegral
    rw [intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    simp only [f, deriv_circleMap, smul_eq_mul]
  have hH := hint'.congr hEq
  exact (hH.differentiableAt (hVo.mem_nhds hV)).differentiableWithinAt

end KAM.Planetary
