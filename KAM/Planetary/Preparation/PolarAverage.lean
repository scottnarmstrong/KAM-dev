/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.AnalyticTaylor
public import KAM.Strip.Averages
public import KAM.Planetary.MaximalStep.Basic
public import KAM.Planetary.Preparation.PolarAverage.Iterate
public import KAM.Planetary.Preparation.PolarAverage.Order

/-!
# The polar average (P11A-P6, `bpP:p11:polar-avg`, `bpP:p11:e5`)

`p11PolarAverage G (J, ρ)` is the torus average of `G (J, (w_i sin 2πθ_i, w_i cos 2πθ_i))` with
`w_i = √(ρ_i/π)` (principal root). The route avoids multi-index Taylor series:

* In the radial variable `w` the average is holomorphic (`p11PolarW_differentiableOn`, a parameter
  integral over the real torus) and even in each `w_j` (the shift `θ_j ↦ θ_j + 1/2` flips both
  `sin` and `cos`).
* An even holomorphic function descends to a holomorphic function of the square, with no branch
  condition (`p11_even_descent`, a parameter Cauchy integral); iterating over the coordinates,
  `p11PolarAverage G` is holomorphic on `D × B(0, π r²)`. In particular the extension `AG` of
  `polar_avg` is the raw average itself, on all of its domain.
* Bound (a): the raw average is a mean of values of `G` in `B(0, r)`. Bound (c): the radial
  Schwarz lemma bounds the integrand by `S (‖(x,y)‖/r)^k`, hence along real rays the average
  decays like `√t^k`, which forces vanishing order `⌈k/2⌉` in `ρ`
  (`p11_vanish_of_decay`); the one-variable Schwarz lemma of `P11A-P0` finishes.
* `polar_extension_unique` is the identity theorem on the connected action polydisc.
* `e5` is the reflection `t ↦ 1 - t` (odd `a`) or `t ↦ 1/2 - t` (odd `b`) on a period.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

theorem e5 (a b : ℕ) (h : Odd a ∨ Odd b) :
    (∫ t in (0 : ℝ)..1, Real.sin (2*Real.pi*t)^a*Real.cos (2*Real.pi*t)^b)=0 := by
  set f : ℝ → ℝ := fun t => Real.sin (2 * Real.pi * t) ^ a * Real.cos (2 * Real.pi * t) ^ b with hf
  have hper : Function.Periodic f 1 := fun t => by
    have : 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi := by ring
    simp only [hf, this, Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hrefl : ∀ c : ℝ, (∫ t in (0 : ℝ)..1, f (c - t)) = ∫ t in (0 : ℝ)..1, f t := by
    intro c
    rw [intervalIntegral.integral_comp_sub_left f c]
    have := hper.intervalIntegral_add_eq (c - 1) 0
    simpa using this
  have hneg : ∀ c : ℝ, (∀ t, f (c - t) = -f t) → (∫ t in (0 : ℝ)..1, f t) = 0 := by
    intro c hc
    have h1 := hrefl c
    simp only [hc, intervalIntegral.integral_neg] at h1
    linarith
  rcases h with ha | hb
  · refine hneg 1 fun t => ?_
    have e1 : 2 * Real.pi * (1 - t) = 2 * Real.pi - 2 * Real.pi * t := by ring
    simp only [hf, e1, Real.sin_two_pi_sub, Real.cos_two_pi_sub, ha.neg_pow]
    ring
  · refine hneg (1 / 2) fun t => ?_
    have e1 : 2 * Real.pi * (1 / 2 - t) = Real.pi - 2 * Real.pi * t := by ring
    simp only [hf, e1, Real.sin_pi_sub, Real.cos_pi_sub, hb.neg_pow]
    ring

/-- Polar average as a linear operator on holomorphic germs; its value at zero has no
square-root singularity. -/
def p11PolarAverage {n : ℕ} (G : P11CVec n × P11Phase n → ℂ)
    (z : P11CVec n × P11CVec n) : ℂ :=
  KAM.torusAverage (fun theta : P11Vec n =>
    G (z.1,((fun i => Complex.sqrt (z.2 i/Real.pi)*Complex.sin (2*Real.pi*(theta i))),
      fun i => Complex.sqrt (z.2 i/Real.pi)*Complex.cos (2*Real.pi*(theta i)))))

theorem p11_torusAverage_const {n : ℕ} (c : ℂ) :
    KAM.torusAverage (fun _ : Fin n → ℝ => c) = c := by
  unfold KAM.torusAverage
  rw [setIntegral_const, measureReal_def, KAM.volume_unitCube]
  simp

theorem p11_torusAverage_lin {n : ℕ} {f g : (Fin n → ℝ) → ℂ} (hf : Continuous f)
    (hg : Continuous g) (a b : ℂ) :
    KAM.torusAverage (fun θ => a * f θ + b * g θ) =
      a * KAM.torusAverage f + b * KAM.torusAverage g := by
  unfold KAM.torusAverage
  rw [integral_add (KAM.integrableOn_unitCube_of_continuous (hf.const_mul a))
    (KAM.integrableOn_unitCube_of_continuous (hg.const_mul b)), integral_const_mul,
    integral_const_mul]

theorem p11_norm_sqrt_eq (a : ℂ) : ‖Complex.sqrt a‖ = Real.sqrt ‖a‖ := by
  rw [← p11_norm_sqrt_sq a, Real.sqrt_sq (norm_nonneg _)]

/-- The radial variable `w_i = √(ρ_i/π)`. -/
def p11Rad {n : ℕ} (ρ : P11CVec n) : P11CVec n := fun i => Complex.sqrt (ρ i / Real.pi)

theorem p11_rad_norm_le {n : ℕ} (ρ : P11CVec n) :
    ‖p11Rad ρ‖ ≤ Real.sqrt (‖ρ‖ / Real.pi) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [p11Rad, p11_norm_sqrt_eq, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  exact Real.sqrt_le_sqrt (by gcongr; exact norm_le_pi_norm ρ i)

theorem p11_rad_norm_lt {n : ℕ} {r : ℝ} (hr : 0 < r) {ρ : P11CVec n}
    (hρ : ‖ρ‖ < Real.pi * r ^ 2) : ‖p11Rad ρ‖ < r := by
  refine (p11_rad_norm_le ρ).trans_lt ?_
  rw [Real.sqrt_lt' hr, div_lt_iff₀ Real.pi_pos]
  linarith

theorem p11PolarAverage_eq {n : ℕ} (G : P11CVec n × P11Phase n → ℂ) (z : P11CVec n × P11CVec n) :
    p11PolarAverage G z = p11PolarW G (z.1, p11Rad z.2) := rfl

/-- The raw average is holomorphic on `D × B(0, π r²)`. -/
theorem p11PolarAverage_differentiableOn {n : ℕ} {D : Set (P11CVec n)} (hD : IsOpen D) {r : ℝ}
    (hr : 0 < r) {G : P11CVec n × P11Phase n → ℂ}
    (hG : DifferentiableOn ℂ G (D ×ˢ Metric.ball 0 r)) :
    DifferentiableOn ℂ (p11PolarAverage G)
      (D ×ˢ Metric.ball (0 : P11CVec n) (Real.pi * r ^ 2)) := by
  have h := p11PolarW_sqrt_differentiableOn hD hr hG
  have hmap : DifferentiableOn ℂ
      (fun p : P11CVec n × P11CVec n => (p.1, ((Real.pi : ℂ)⁻¹) • p.2))
      (D ×ˢ Metric.ball (0 : P11CVec n) (Real.pi * r ^ 2)) := by fun_prop
  have hc := h.comp hmap (fun p hp => by
    refine ⟨hp.1, ?_⟩
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, inv_mul_lt_iff₀ Real.pi_pos]
    exact mem_ball_zero_iff.mp hp.2)
  refine hc.congr fun p _ => ?_
  rw [p11PolarAverage_eq]
  simp only [Function.comp]
  congr 2
  funext i
  simp only [p11Rad, div_eq_inv_mul, Pi.smul_apply, smul_eq_mul]

/-- Pointwise bound of the raw average by the sup of `G` on `D × B(0, r)`, refined by the
radial Schwarz bound when the jets of order `< k` vanish. -/
theorem p11PolarAverage_norm_le_pow {n : ℕ} {D : Set (P11CVec n)} {r S : ℝ} (hr : 0 < r)
    (hS : 0 ≤ S) {G : P11CVec n × P11Phase n → ℂ}
    (hG : DifferentiableOn ℂ G (D ×ˢ Metric.ball 0 r))
    (hb : p11Bound (D ×ˢ Metric.ball 0 r) G S) {k : ℕ}
    (hj : ∀ J ∈ D, ∀ j < k, iteratedFDeriv ℂ j (fun z => G (J, z)) 0 = 0)
    {J : P11CVec n} (hJ : J ∈ D) {ρ : P11CVec n} (hρ : ‖ρ‖ < Real.pi * r ^ 2) :
    ‖p11PolarAverage G (J, ρ)‖ ≤ S * (Real.sqrt (‖ρ‖ / Real.pi) / r) ^ k := by
  have hGJ : DifferentiableOn ℂ (fun z => G (J, z)) (Metric.ball 0 r) :=
    hG.comp (by fun_prop : DifferentiableOn ℂ (fun z : P11Phase n => (J, z)) _)
      (fun z hz => ⟨hJ, hz⟩)
  have hbJ : ∀ z ∈ Metric.ball (0 : P11Phase n) r, ‖G (J, z)‖ ≤ S := fun z hz => hb _ ⟨hJ, hz⟩
  have sw := p11_radial_schwarz_gen hr hGJ hbJ (hj J hJ)
  have hw := p11_rad_norm_lt hr hρ
  show ‖p11PolarW G (J, p11Rad ρ)‖ ≤ _
  refine KAM.norm_torusAverage_le fun θ _ => ?_
  have hpt := p11_polarPt_mem_ball hw θ
  refine (sw _ hpt).trans ?_
  have h1 : ‖p11PolarPt (p11Rad ρ) (fun i => (θ i : ℂ))‖ / r ≤ Real.sqrt (‖ρ‖ / Real.pi) / r :=
    div_le_div_of_nonneg_right ((p11_norm_polarPt_le _ θ).trans (p11_rad_norm_le ρ)) hr.le
  gcongr

theorem polar_avg {n : ℕ} {D : Set (P11CVec n)} (hD : IsOpen D) {r S : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hS : 0 < S)
    {G : P11CVec n × P11Phase n → ℂ}
    (hG : DifferentiableOn ℂ G (D ×ˢ Metric.ball 0 r))
    (hb : p11Bound (D ×ˢ Metric.ball 0 r) G S) :
    ∃ AG : P11CVec n × P11CVec n → ℂ,
      DifferentiableOn ℂ AG (D ×ˢ Metric.ball 0 (Real.pi*r^2/4)) ∧
      p11Bound (D ×ˢ Metric.ball 0 (Real.pi*r^2/4)) AG (2^(2*n)*S) ∧
      (∀ z ∈ D ×ˢ Metric.ball 0 (Real.pi*r^2/4), (∀ i, 0 < (z.2 i).re) →
        AG z=p11PolarAverage G z) ∧
      ∀ k : ℕ, (∀ J ∈ D, ∀ j < k, iteratedFDeriv ℂ j (fun z => G (J,z)) 0=0) →
        ∀ z ∈ D ×ˢ Metric.ball 0 (Real.pi*r^2/4),
          ‖AG z‖ ≤ 2^(2*n)*S*(4*‖z.2‖/(Real.pi*r^2))^((k+1)/2) := by
  have hpi := Real.pi_pos
  have hsub : Metric.ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4) ⊆
      Metric.ball 0 (Real.pi * r ^ 2) :=
    Metric.ball_subset_ball (by nlinarith [mul_pos hpi (pow_pos hr 2)])
  have hAGd : DifferentiableOn ℂ (p11PolarAverage G)
      (D ×ˢ Metric.ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4)) :=
    (p11PolarAverage_differentiableOn hD hr hG).mono (prod_mono subset_rfl hsub)
  have h2n : (1 : ℝ) ≤ 2 ^ (2 * n) := one_le_pow₀ (by norm_num)
  have hbound : ∀ z ∈ D ×ˢ Metric.ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4),
      ‖p11PolarAverage G z‖ ≤ 2 ^ (2 * n) * S := by
    intro z hz
    have := p11PolarAverage_norm_le_pow (k := 0) hr hS.le hG hb (fun J hJ j hj => by omega)
      hz.1 (mem_ball_zero_iff.mp (hsub hz.2))
    simp only [pow_zero, mul_one] at this
    exact this.trans (le_mul_of_one_le_left hS.le h2n)
  refine ⟨p11PolarAverage G, hAGd, hbound, fun z _ _ => rfl, ?_⟩
  intro k hk z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hρ : ‖z.2‖ < Real.pi * r ^ 2 / 4 := mem_ball_zero_iff.mp hz2
  have hraw := fun ρ' (h : ‖ρ'‖ < Real.pi * r ^ 2) =>
    p11PolarAverage_norm_le_pow hr hS.le hG hb hk hz1 h
  set M : ℝ := 2 ^ (2 * n) * S with hM
  by_cases hρ0 : z.2 = 0
  · have hz0 : z = (z.1, 0) := Prod.ext rfl hρ0
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have := hbound z ⟨hz1, hz2⟩
      simpa using this
    · have h0 := hraw 0 (by simpa using mul_pos hpi (pow_pos hr 2))
      rw [hz0]
      have hm : (k + 1) / 2 ≠ 0 := by omega
      simp only [norm_zero, zero_div, mul_zero, zero_div, zero_pow hm]
      have h0'' : ‖p11PolarAverage G (z.1, 0)‖ ≤ 0 := by
        simpa [zero_pow hkpos.ne'] using h0
      simpa using h0''
  · have hN : 0 < ‖z.2‖ := norm_pos_iff.mpr hρ0
    set N := ‖z.2‖ with hNdef
    set R : ℝ := (Real.pi * r ^ 2 / 4) / N with hR
    have hR0 : 0 < R := div_pos (by positivity) hN
    have hlt : ∀ lam : ℂ, ‖lam‖ < R → ‖lam • z.2‖ < Real.pi * r ^ 2 / 4 := by
      intro lam hlam
      rw [norm_smul]
      calc ‖lam‖ * N < R * N := by gcongr
        _ = Real.pi * r ^ 2 / 4 := by rw [hR]; field_simp
    have hgd : DifferentiableOn ℂ (fun lam : ℂ => p11PolarAverage G (z.1, lam • z.2))
        (Metric.ball 0 R) := by
      refine hAGd.comp (by fun_prop : DifferentiableOn ℂ (fun lam : ℂ => (z.1, lam • z.2)) _)
        (fun lam hlam => ⟨hz1, mem_ball_zero_iff.mpr (hlt lam (mem_ball_zero_iff.mp hlam))⟩)
    have hgb : ∀ lam ∈ Metric.ball (0 : ℂ) R, ‖p11PolarAverage G (z.1, lam • z.2)‖ ≤ M := by
      intro lam hlam
      exact hbound _ ⟨hz1, mem_ball_zero_iff.mpr (hlt lam (mem_ball_zero_iff.mp hlam))⟩
    have hdec : ∀ t : ℝ, 0 < t → t < R →
        ‖p11PolarAverage G (z.1, (t : ℂ) • z.2)‖ ≤
          S * (Real.sqrt (N / Real.pi) / r) ^ k * Real.sqrt t ^ k := by
      intro t ht htR
      have hnt : ‖(t : ℂ) • z.2‖ = t * N := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht.le]
      have hl := hlt (t : ℂ) (by rw [Complex.norm_real, Real.norm_of_nonneg ht.le]; exact htR)
      have := hraw ((t : ℂ) • z.2) (by
        refine lt_of_lt_of_le hl ?_
        nlinarith [mul_pos hpi (pow_pos hr 2)])
      refine this.trans (le_of_eq ?_)
      rw [hnt]
      have hsq : Real.sqrt (t * N / Real.pi) = Real.sqrt t * Real.sqrt (N / Real.pi) := by
        rw [← Real.sqrt_mul ht.le]; congr 1; ring
      rw [hsq, mul_div_right_comm, mul_pow]
      ring
    have hvan := p11_vanish_of_decay hR0 hgd hdec
    have hj : ∀ j < (k + 1) / 2,
        iteratedDeriv j (fun lam : ℂ => p11PolarAverage G (z.1, lam • z.2)) 0 = 0 :=
      fun j hj' => hvan j (by omega)
    have h1R : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, norm_one, hR, lt_div_iff₀ hN]
      linarith
    have key := p11_schwarz_one hR0 hgd hgb hj (w := 1) (mem_ball_zero_iff.mp h1R)
    simp only [one_smul, norm_one] at key
    have e : 1 / R = 4 * N / (Real.pi * r ^ 2) := by
      rw [hR]; field_simp
    rw [e] at key
    exact key

theorem polar_average_linear {n : ℕ} {D : Set (P11CVec n)}
    (hD : IsOpen D) {r : ℝ} (hr : 0 < r)
    {G H : P11CVec n × P11Phase n → ℂ}
    (hG : DifferentiableOn ℂ G (D ×ˢ Metric.ball 0 r))
    (hH : DifferentiableOn ℂ H (D ×ˢ Metric.ball 0 r))
    (a b : ℂ) :
    ∀ z ∈ D ×ˢ Metric.ball 0 (Real.pi*r^2/4),
      (∀ i, 0 < (z.2 i).re) →
      p11PolarAverage (a • G+b • H) z =
        a*p11PolarAverage G z+b*p11PolarAverage H z := by
  intro z hz _
  have hpi := Real.pi_pos
  have hρ : ‖z.2‖ < Real.pi * r ^ 2 :=
    lt_of_lt_of_le (mem_ball_zero_iff.mp hz.2) (by nlinarith [mul_pos hpi (pow_pos hr 2)])
  have hw := p11_rad_norm_lt hr hρ
  have hGc := p11_continuous_polar_integrand hG hz.1 hw
  have hHc := p11_continuous_polar_integrand hH hz.1 hw
  show KAM.torusAverage (fun θ : P11Vec n =>
      (a • G + b • H) (z.1, p11PolarPt (p11Rad z.2) (fun i => (θ i : ℂ)))) =
    a * p11PolarW G (z.1, p11Rad z.2) + b * p11PolarW H (z.1, p11Rad z.2)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact p11_torusAverage_lin hGc hHc a b

theorem polar_average_normalization {n : ℕ}
    (C : P11CVec n → ℂ) (z : P11CVec n × P11CVec n) :
    p11PolarAverage (fun y => C y.1) z = C z.1 ∧
    ∀ i : Fin n,
      p11PolarAverage (fun y => (y.2.1 i^2+y.2.2 i^2)/2) z =
        z.2 i/(2*Real.pi) := by
  refine ⟨p11_torusAverage_const (C z.1), fun i => ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpt : ∀ θ : P11Vec n, (((p11PolarPt (p11Rad z.2) (fun i => (θ i : ℂ))).1 i) ^ 2 +
      ((p11PolarPt (p11Rad z.2) (fun i => (θ i : ℂ))).2 i) ^ 2) / 2 = z.2 i / (2 * Real.pi) := by
    intro θ
    have h1 : (Complex.sqrt (z.2 i / Real.pi)) ^ 2 = z.2 i / Real.pi := p11_sqrt_sq _
    have h2 := Complex.sin_sq_add_cos_sq (2 * Real.pi * (θ i : ℂ))
    simp only [p11PolarPt, p11Rad]
    calc ((Complex.sqrt (z.2 i / Real.pi) * Complex.sin (2 * Real.pi * (θ i : ℂ))) ^ 2 +
          (Complex.sqrt (z.2 i / Real.pi) * Complex.cos (2 * Real.pi * (θ i : ℂ))) ^ 2) / 2
        = (Complex.sqrt (z.2 i / Real.pi)) ^ 2 *
            (Complex.sin (2 * Real.pi * (θ i : ℂ)) ^ 2 + Complex.cos (2 * Real.pi * (θ i : ℂ)) ^ 2)
            / 2 := by ring
      _ = z.2 i / (2 * Real.pi) := by rw [h2, h1]; field_simp
  show KAM.torusAverage (fun θ : P11Vec n =>
    (((p11PolarPt (p11Rad z.2) (fun i => (θ i : ℂ))).1 i) ^ 2 +
      ((p11PolarPt (p11Rad z.2) (fun i => (θ i : ℂ))).2 i) ^ 2) / 2) = _
  simp only [hpt]
  exact p11_torusAverage_const _

theorem polar_extension_unique {n : ℕ} {D : Set (P11CVec n)}
    (hD : IsOpen D) {R : ℝ} (hR : 0 < R)
    {A B : P11CVec n × P11CVec n → ℂ}
    (hA : DifferentiableOn ℂ A (D ×ˢ Metric.ball 0 R))
    (hB : DifferentiableOn ℂ B (D ×ˢ Metric.ball 0 R))
    (heq : ∀ z ∈ D ×ˢ Metric.ball 0 R, (∀ i, 0 < (z.2 i).re) → A z=B z) :
    EqOn A B (D ×ˢ Metric.ball 0 R) := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  have hfib : ∀ F : P11CVec n × P11CVec n → ℂ, DifferentiableOn ℂ F (D ×ˢ Metric.ball 0 R) →
      AnalyticOnNhd ℂ (fun ρ : P11CVec n => F (z.1, ρ)) (Metric.ball 0 R) := by
    intro F hF
    exact KAM.analyticOnNhd_of_differentiableOn Metric.isOpen_ball
      (hF.comp (by fun_prop : DifferentiableOn ℂ (fun ρ : P11CVec n => (z.1, ρ)) _)
        (fun ρ hρ => ⟨hz1, hρ⟩))
  set x0 : P11CVec n := fun _ => ((R / 2 : ℝ) : ℂ) with hx0
  have hx0R : x0 ∈ Metric.ball (0 : P11CVec n) R := by
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
      (half_lt_self hR)
    simp [hx0, abs_of_pos hR]
  have hopen : IsOpen {ρ : P11CVec n | ∀ i, 0 < (ρ i).re} := by
    have : {ρ : P11CVec n | ∀ i, 0 < (ρ i).re} = ⋂ i, {ρ : P11CVec n | 0 < (ρ i).re} := by
      ext ρ; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply i))
  have hpos : x0 ∈ {ρ : P11CVec n | ∀ i, 0 < (ρ i).re} := by
    intro i
    simp [hx0, hR]
  have hev : (fun ρ : P11CVec n => A (z.1, ρ)) =ᶠ[nhds x0] (fun ρ => B (z.1, ρ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx0R, hopen.mem_nhds hpos] with ρ h1 h2
    exact heq (z.1, ρ) ⟨hz1, h1⟩ h2
  exact (hfib A hA).eqOn_of_preconnected_of_eventuallyEq (hfib B hB)
    (convex_ball (0 : P11CVec n) R).isPreconnected hx0R hev hz2

end KAM.Planetary
