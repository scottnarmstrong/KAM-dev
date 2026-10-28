/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Planar quartic torsion: reduction of Laplace coefficients (P11C, package T3)

The normalized radian Laplace integral `p11c_laplace`, the three recurrences `laplace_red`
(integration by parts over the period), the upward recurrences `laplace_up`, and the rational
reduction `laplace_rational_reduction` of every half-integer coefficient to `b_{1/2}^{(0)}`,
`b_{1/2}^{(1)}` with polynomial coefficients over `ℚ`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary

/-- Purely local integral adapter for Part 8's laplace_def, to be identified by a bridge. -/
def p11c_laplace (s : ℝ) (k : ℤ) (a : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), cos ((k : ℝ) * t) / (1 + a ^ 2 - 2 * a * cos t) ^ s

/-! ### The kernel -/

/-- The positive kernel `1 + a² - 2 a cos t`. -/
def p11cKer (a t : ℝ) : ℝ := 1 + a ^ 2 - 2 * a * cos t

theorem p11cKer_pos {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (t : ℝ) : 0 < p11cKer a t := by
  unfold p11cKer
  nlinarith [cos_le_one t, ha.1, ha.2, sq_nonneg (1 - a)]

theorem p11cKer_contDiff (a : ℝ) : Continuous (p11cKer a) := by
  unfold p11cKer; fun_prop

theorem p11c_cont_div {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (c : ℝ → ℝ) (hc : Continuous c) :
    Continuous fun t => c t / p11cKer a t ^ s := by
  refine hc.div ((p11cKer_contDiff a).rpow_const fun t => Or.inl (p11cKer_pos ha t).ne') ?_
  intro t
  exact (Real.rpow_pos_of_pos (p11cKer_pos ha t) s).ne'

/-- The raw integral. -/
def p11cI (s : ℝ) (k : ℤ) (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * π), cos ((k : ℝ) * t) / p11cKer a t ^ s

theorem p11c_laplace_eq (s : ℝ) (k : ℤ) (a : ℝ) :
    p11c_laplace s k a = (2 * π)⁻¹ * p11cI s k a := rfl

theorem p11cI_cont {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    Continuous fun t => cos ((k : ℝ) * t) / p11cKer a t ^ s :=
  p11c_cont_div ha s _ (by fun_prop)

/-! ### First recurrence -/

theorem p11cI_red1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    p11cI (s - 1) k a = (1 + a ^ 2) * p11cI s k a -
      a * (p11cI s (k + 1) a + p11cI s (k - 1) a) := by
  have key : ∀ t, cos ((k : ℝ) * t) / p11cKer a t ^ (s - 1) =
      (1 + a ^ 2) * (cos ((k : ℝ) * t) / p11cKer a t ^ s) -
        a * (cos (((k + 1 : ℤ) : ℝ) * t) / p11cKer a t ^ s +
          cos (((k - 1 : ℤ) : ℝ) * t) / p11cKer a t ^ s) := by
    intro t
    have hp := p11cKer_pos ha t
    have h1 : p11cKer a t ^ (s - 1) = p11cKer a t ^ s / p11cKer a t := Real.rpow_sub_one hp.ne' s
    have h2 := Real.rpow_pos_of_pos hp s
    have e1 : cos (((k + 1 : ℤ) : ℝ) * t) =
        cos ((k : ℝ) * t) * cos t - sin ((k : ℝ) * t) * sin t := by
      rw [← cos_add]; push_cast; ring_nf
    have e2 : cos (((k - 1 : ℤ) : ℝ) * t) =
        cos ((k : ℝ) * t) * cos t + sin ((k : ℝ) * t) * sin t := by
      rw [← cos_sub]; push_cast; ring_nf
    rw [h1, e1, e2]
    unfold p11cKer at *
    field_simp
    ring
  unfold p11cI
  simp_rw [key]
  have i1 := (p11cI_cont ha s k).intervalIntegrable (μ := volume) 0 (2 * π)
  have i2 := (p11cI_cont ha s (k + 1)).intervalIntegrable (μ := volume) 0 (2 * π)
  have i3 := (p11cI_cont ha s (k - 1)).intervalIntegrable (μ := volume) 0 (2 * π)
  rw [intervalIntegral.integral_sub (i1.const_mul _) ((i2.add i3).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add i2 i3]

/-! ### Second recurrence (integration by parts over the period) -/

theorem p11cI_red2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    (k : ℝ) * p11cI (s - 1) k a =
      (s - 1) * a * (p11cI s (k - 1) a - p11cI s (k + 1) a) := by
  set G : ℝ → ℝ := fun t => sin ((k : ℝ) * t) * p11cKer a t ^ (1 - s) with hG
  set G' : ℝ → ℝ := fun t => (k : ℝ) * (cos ((k : ℝ) * t) / p11cKer a t ^ (s - 1)) +
    (1 - s) * a * (cos (((k - 1 : ℤ) : ℝ) * t) / p11cKer a t ^ s -
      cos (((k + 1 : ℤ) : ℝ) * t) / p11cKer a t ^ s) with hG'
  have hder : ∀ t, HasDerivAt G (G' t) t := by
    intro t
    have hp := p11cKer_pos ha t
    have hK : HasDerivAt (p11cKer a) (2 * a * sin t) t := by
      unfold p11cKer
      have := ((hasDerivAt_cos t).const_mul (2 * a)).const_sub (1 + a ^ 2)
      convert this using 1
      ring
    have hs := hK.rpow_const (p := 1 - s) (Or.inl hp.ne')
    have hsin : HasDerivAt (fun t => sin ((k : ℝ) * t)) (cos ((k : ℝ) * t) * (k : ℝ)) t := by
      simpa using ((hasDerivAt_id t).const_mul (k : ℝ)).sin
    convert hsin.mul hs using 1
    have h2 := Real.rpow_pos_of_pos hp s
    have e1 : cos (((k + 1 : ℤ) : ℝ) * t) =
        cos ((k : ℝ) * t) * cos t - sin ((k : ℝ) * t) * sin t := by
      rw [← cos_add]; push_cast; ring_nf
    have e2 : cos (((k - 1 : ℤ) : ℝ) * t) =
        cos ((k : ℝ) * t) * cos t + sin ((k : ℝ) * t) * sin t := by
      rw [← cos_sub]; push_cast; ring_nf
    have h3 : p11cKer a t ^ (s - 1) = p11cKer a t ^ s / p11cKer a t := Real.rpow_sub_one hp.ne' s
    have h4 : p11cKer a t ^ (1 - s) = (p11cKer a t ^ (s - 1))⁻¹ := by
      rw [← Real.rpow_neg hp.le]; ring_nf
    have h5 : p11cKer a t ^ (1 - s - 1) = (p11cKer a t ^ s)⁻¹ := by
      rw [← Real.rpow_neg hp.le]; ring_nf
    simp only [hG']
    rw [h5, h4, h3, e1, e2]
    have hpe : p11cKer a t = 1 + a ^ 2 - 2 * a * cos t := rfl
    rw [hpe] at *
    field_simp
    ring
  have hcont : Continuous G' := by
    simp only [hG']
    exact (continuous_const.mul (p11cI_cont ha (s - 1) k)).add
      (continuous_const.mul ((p11cI_cont ha s _).sub (p11cI_cont ha s _)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
    (hcont.intervalIntegrable 0 (2 * π))
  have hz : G (2 * π) - G 0 = 0 := by
    simp only [hG]
    have : sin ((k : ℝ) * (2 * π)) = 0 := by
      have := Real.sin_int_mul_pi (2 * k)
      rw [← this]; push_cast; ring_nf
    rw [this]; simp
  rw [hz] at hFTC
  simp only [hG'] at hFTC
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub] at hFTC
  · unfold p11cI at *; linarith
  · exact (p11cI_cont ha s _).intervalIntegrable 0 (2 * π)
  · exact (p11cI_cont ha s _).intervalIntegrable 0 (2 * π)
  · exact (continuous_const.mul (p11cI_cont ha (s - 1) k)).intervalIntegrable 0 (2 * π)
  · exact (continuous_const.mul ((p11cI_cont ha s _).sub (p11cI_cont ha s _))).intervalIntegrable
      0 (2 * π)

/-! ### Statements -/

theorem p11c_laplace_red1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    p11c_laplace (s - 1) k a = (1 + a ^ 2) * p11c_laplace s k a -
      a * (p11c_laplace s (k + 1) a + p11c_laplace s (k - 1) a) := by
  simp only [p11c_laplace_eq, p11cI_red1 ha]
  ring

theorem p11c_laplace_red2 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    (k : ℝ) * p11c_laplace (s - 1) k a = (s - 1) * a *
      (p11c_laplace s (k - 1) a - p11c_laplace s (k + 1) a) := by
  simp only [p11c_laplace_eq]
  have := p11cI_red2 ha s k
  linear_combination (2 * π)⁻¹ * this

theorem p11c_laplace_red3 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : ℝ) (k : ℤ) :
    (s - 1 - k) * a * p11c_laplace s (k + 1) a =
      (k + s - 1) * a * p11c_laplace s (k - 1) a - k * (1 + a ^ 2) * p11c_laplace s k a := by
  have h1 := p11c_laplace_red1 ha s k
  have h2 := p11c_laplace_red2 ha s k
  rw [h1] at h2
  linear_combination h2

theorem laplace_red (s a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    p11c_laplace (s - 1) k a = (1 + a ^ 2) * p11c_laplace s k a -
      a * (p11c_laplace s ((k : ℤ) + 1) a + p11c_laplace s ((k : ℤ) - 1) a) ∧
    (k : ℝ) * p11c_laplace (s - 1) k a = (s - 1) * a *
      (p11c_laplace s ((k : ℤ) - 1) a - p11c_laplace s ((k : ℤ) + 1) a) ∧
    (1 ≤ k → (s - 1 - k) * a * p11c_laplace s ((k : ℤ) + 1) a =
      (k + s - 1) * a * p11c_laplace s ((k : ℤ) - 1) a - k * (1 + a ^ 2) * p11c_laplace s k a) := by
  refine ⟨p11c_laplace_red1 ha s k, ?_, fun _ => ?_⟩
  · simpa using p11c_laplace_red2 ha s k
  · simpa using p11c_laplace_red3 ha s k

/-! ### Upward recurrences -/

theorem laplace_up (s a : ℝ) (hs : 1 / 2 ≤ s) (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (s + 1) 0 a = ((1 + a ^ 2) * p11c_laplace s 0 a +
      2 * a * (1 - 1 / s) * p11c_laplace s 1 a) / (1 - a ^ 2) ^ 2 ∧
    p11c_laplace (s + 1) 1 a = ((1 + a ^ 2) * (1 - 1 / s) * p11c_laplace s 1 a +
      2 * a * p11c_laplace s 0 a) / (1 - a ^ 2) ^ 2 ∧
    ∀ k : ℕ, 1 ≤ k → p11c_laplace (s + 1) ((k : ℤ) + 1) a =
      p11c_laplace (s + 1) ((k : ℤ) - 1) a - k * p11c_laplace s k a / (s * a) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have ha0 : a ≠ 0 := ha.1.ne'
  have hD : (1 - a ^ 2) ^ 2 ≠ 0 := by
    have : 0 < 1 - a ^ 2 := by nlinarith [ha.1, ha.2]
    positivity
  have hsub : s + 1 - 1 = s := by ring
  have R1 : ∀ k : ℤ, p11c_laplace s k a = (1 + a ^ 2) * p11c_laplace (s + 1) k a -
      a * (p11c_laplace (s + 1) (k + 1) a + p11c_laplace (s + 1) (k - 1) a) := by
    intro k; have := p11c_laplace_red1 ha (s + 1) k; rwa [hsub] at this
  have R2 : ∀ k : ℤ, (k : ℝ) * p11c_laplace s k a = s * a *
      (p11c_laplace (s + 1) (k - 1) a - p11c_laplace (s + 1) (k + 1) a) := by
    intro k; have := p11c_laplace_red2 ha (s + 1) k; rwa [hsub] at this
  have sym : p11c_laplace (s + 1) (-1) a = p11c_laplace (s + 1) 1 a := by
    simp only [p11c_laplace]
    congr 2; ext t
    simp
  have a0 := R1 0
  have a1 := R1 1
  have b1 := R2 1
  norm_num at a0 a1 b1
  rw [sym] at a0
  have haA2 : a * p11c_laplace (s + 1) 2 a =
      a * p11c_laplace (s + 1) 0 a - p11c_laplace s 1 a / s := by
    field_simp
    linarith
  have hA1 : (1 + a ^ 2) * p11c_laplace (s + 1) 1 a =
      (1 - 1 / s) * p11c_laplace s 1 a + 2 * a * p11c_laplace (s + 1) 0 a := by
    have : p11c_laplace s 1 a / s = (1 / s) * p11c_laplace s 1 a := by ring
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_div_iff hD]
    linear_combination (-(1 + a ^ 2)) * a0 + (2 * a) * hA1
  · rw [eq_div_iff hD]
    linear_combination (1 + a ^ 2) * hA1 - (2 * a) * a0
  · intro k hk
    have := R2 k
    rw [Int.cast_natCast] at this
    have hsa : s * a ≠ 0 := mul_ne_zero hs0 ha0
    field_simp
    linarith

/-! ### Rational reduction -/

/-- Evaluation of a rational polynomial at a real point. -/
abbrev p11cEv (a : ℝ) (p : Polynomial ℚ) : ℝ := Polynomial.eval₂ (algebraMap ℚ ℝ) a p

/-- `f` is a polynomial combination of `b_{1/2}^{(0)}`, `b_{1/2}^{(1)}` over a pole-free rational
function. -/
def p11cRep (f : ℝ → ℝ) : Prop :=
  ∃ p0 p1 q : Polynomial ℚ, ∀ a ∈ Ioo (0 : ℝ) 1,
    p11cEv a q ≠ 0 ∧
      f a = (p11cEv a p0 * p11c_laplace (1 / 2) 0 a + p11cEv a p1 * p11c_laplace (1 / 2) 1 a) /
        p11cEv a q

theorem p11cRep_comb {f g F : ℝ → ℝ} (hf : p11cRep f) (hg : p11cRep g)
    (U V W : Polynomial ℚ) (hW : ∀ a ∈ Ioo (0 : ℝ) 1, p11cEv a W ≠ 0)
    (h : ∀ a ∈ Ioo (0 : ℝ) 1, F a = (p11cEv a U * f a + p11cEv a V * g a) / p11cEv a W) :
    p11cRep F := by
  obtain ⟨P0, P1, Q, hP⟩ := hf
  obtain ⟨R0, R1, S, hR⟩ := hg
  refine ⟨U * P0 * S + V * R0 * Q, U * P1 * S + V * R1 * Q, Q * S * W, fun a ha => ?_⟩
  obtain ⟨hQ, hfa⟩ := hP a ha
  obtain ⟨hS, hga⟩ := hR a ha
  have hW' := hW a ha
  refine ⟨by
    simp only [p11cEv, Polynomial.eval₂_mul]
    exact mul_ne_zero (mul_ne_zero hQ hS) hW', ?_⟩
  rw [h a ha, hfa, hga]
  simp only [p11cEv, Polynomial.eval₂_mul, Polynomial.eval₂_add] at *
  field_simp
  ring

theorem p11cRep_zero : p11cRep (fun a => p11c_laplace (1 / 2) 0 a) :=
  ⟨1, 0, 1, fun a _ => by simp [p11cEv]⟩

theorem p11cRep_one : p11cRep (fun a => p11c_laplace (1 / 2) 1 a) :=
  ⟨0, 1, 1, fun a _ => by simp [p11cEv]⟩

theorem p11c_one_sub_sq_ne {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : 1 - a ^ 2 ≠ 0 := by
  nlinarith [ha.1, ha.2]

/-- Levels `0` and `1` at half-integer order `1/2 + j`. -/
theorem p11cRep_base (j : ℕ) :
    p11cRep (fun a => p11c_laplace (1 / 2 + (j : ℝ)) 0 a) ∧
      p11cRep (fun a => p11c_laplace (1 / 2 + (j : ℝ)) 1 a) := by
  induction j with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    exact ⟨p11cRep_zero, p11cRep_one⟩
  | succ j ih =>
    obtain ⟨h0, h1⟩ := ih
    have hs : (1 / 2 : ℝ) ≤ 1 / 2 + (j : ℝ) := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hup := fun a (ha : a ∈ Ioo (0 : ℝ) 1) => laplace_up (1 / 2 + (j : ℝ)) a hs ha
    have hW : ∀ a ∈ Ioo (0 : ℝ) 1, p11cEv a ((1 - Polynomial.X ^ 2) ^ 2) ≠ 0 := by
      intro a ha
      simp only [p11cEv, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_one,
        Polynomial.eval₂_X]
      exact pow_ne_zero _ (p11c_one_sub_sq_ne ha)
    have hc : (1 / 2 : ℝ) + ((j + 1 : ℕ) : ℝ) = 1 / 2 + (j : ℝ) + 1 := by push_cast; ring
    rw [hc]
    refine ⟨p11cRep_comb h0 h1 (1 + Polynomial.X ^ 2)
      (Polynomial.C (2 * (1 - 1 / (1 / 2 + (j : ℚ)))) * Polynomial.X) _ hW
      fun a ha => ?_, p11cRep_comb h1 h0
      ((1 + Polynomial.X ^ 2) * Polynomial.C (1 - 1 / (1 / 2 + (j : ℚ))))
      (Polynomial.C 2 * Polynomial.X) _ hW fun a ha => ?_⟩
    · rw [(hup a ha).1]
      simp [p11cEv]
      ring
    · rw [(hup a ha).2.1]
      simp [p11cEv]

theorem p11c_laplace_step {s a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℤ) (hk : s - 1 - k ≠ 0) :
    p11c_laplace s (k + 1) a =
      (((k : ℝ) + s - 1) * a * p11c_laplace s (k - 1) a -
        (k : ℝ) * (1 + a ^ 2) * p11c_laplace s k a) / ((s - 1 - k) * a) := by
  rw [eq_div_iff (mul_ne_zero hk ha.1.ne')]
  linear_combination p11c_laplace_red3 ha s k

theorem p11cRep_all (j : ℕ) (k : ℕ) :
    p11cRep (fun a => p11c_laplace (1 / 2 + (j : ℝ)) (k : ℤ) a) ∧
      p11cRep (fun a => p11c_laplace (1 / 2 + (j : ℝ)) ((k : ℤ) + 1) a) := by
  induction k with
  | zero => simpa using p11cRep_base j
  | succ k ih =>
    obtain ⟨hk0, hk1⟩ := ih
    refine ⟨by simpa using hk1, ?_⟩
    have hne : ((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ)) ≠ 0 := by
      intro h
      push_cast at h
      have h2 : ((2 * (j : ℤ) - 1 - 2 * ((k : ℤ) + 1) : ℤ) : ℚ) = 0 := by push_cast; linarith
      have := Int.cast_eq_zero.1 h2
      omega
    have hW : ∀ a ∈ Ioo (0 : ℝ) 1,
        p11cEv a (Polynomial.C ((1 / 2 + (j : ℚ)) - 1 - ((k + 1 : ℕ) : ℚ)) * Polynomial.X) ≠ 0 := by
      intro a ha
      simp only [p11cEv, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
      refine mul_ne_zero ?_ ha.1.ne'
      intro h
      apply hne
      have : (((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by
        push_cast at h ⊢; norm_num at h; linarith
      exact_mod_cast this
    refine p11cRep_comb (f := fun a => p11c_laplace (1 / 2 + (j : ℝ)) (k : ℤ) a)
      (g := fun a => p11c_laplace (1 / 2 + (j : ℝ)) ((k : ℤ) + 1) a) hk0 hk1
      (Polynomial.C (((k + 1 : ℕ) : ℚ) + (1 / 2 + (j : ℚ)) - 1) * Polynomial.X)
      (-(Polynomial.C ((k + 1 : ℕ) : ℚ)) * (1 + Polynomial.X ^ 2)) _ hW fun a ha => ?_
    have hk : (1 / 2 + (j : ℝ)) - 1 - (((k + 1 : ℕ) : ℤ) : ℝ) ≠ 0 := by
      intro h
      apply hne
      have : (((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by
        push_cast at h ⊢; linarith
      exact_mod_cast this
    have := p11c_laplace_step (s := 1 / 2 + (j : ℝ)) ha ((k + 1 : ℕ) : ℤ) hk
    have e1 : (((k + 1 : ℕ) : ℤ) + 1) = ((k : ℤ) + 1) + 1 := by push_cast; ring
    have e2 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
    rw [e2] at this
    have e3 : (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 := by push_cast; ring
    rw [e3] at this ⊢
    rw [show ((k : ℤ) + 1 + 1) = (k : ℤ) + 1 + 1 from rfl, this]
    simp only [p11cEv, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_neg, Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_pow]
    push_cast
    norm_num
    ring_nf

theorem laplace_rational_reduction (j k : ℕ) :
    ∃ p0 p1 q : Polynomial ℚ, ∀ a ∈ Ioo (0 : ℝ) 1,
      Polynomial.eval₂ (algebraMap ℚ ℝ) a q ≠ 0 ∧
      p11c_laplace (1 / 2 + (j : ℝ)) k a =
        (Polynomial.eval₂ (algebraMap ℚ ℝ) a p0 * p11c_laplace (1 / 2) 0 a +
         Polynomial.eval₂ (algebraMap ℚ ℝ) a p1 * p11c_laplace (1 / 2) 1 a) /
          Polynomial.eval₂ (algebraMap ℚ ℝ) a q :=
  (p11cRep_all j k).1

/-! ### Explicit denominator envelope -/

/-- `f` is a polynomial combination of `b_{1/2}^{(0)}`, `b_{1/2}^{(1)}` over
`a ^ m (1 - a ^ 2) ^ (2 j)`. -/
def p11cRepD (j m : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ p0 p1 : Polynomial ℚ, ∀ a ∈ Ioo (0 : ℝ) 1,
    f a = (p11cEv a p0 * p11c_laplace (1 / 2) 0 a + p11cEv a p1 * p11c_laplace (1 / 2) 1 a) /
      (a ^ m * (1 - a ^ 2) ^ (2 * j))

theorem p11cRepD_mono {j m : ℕ} (n : ℕ) {f : ℝ → ℝ} (h : p11cRepD j m f) :
    p11cRepD j (m + n) f := by
  obtain ⟨p0, p1, hp⟩ := h
  refine ⟨p0 * Polynomial.X ^ n, p1 * Polynomial.X ^ n, fun a ha => ?_⟩
  have h1 := p11c_one_sub_sq_ne ha
  have h2 := ha.1.ne'
  rw [hp a ha]
  simp only [p11cEv, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  field_simp
  ring

theorem p11cRepD_base (j : ℕ) :
    p11cRepD j 0 (fun a => p11c_laplace (1 / 2 + (j : ℝ)) 0 a) ∧
      p11cRepD j 0 (fun a => p11c_laplace (1 / 2 + (j : ℝ)) 1 a) := by
  induction j with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    exact ⟨⟨1, 0, fun a _ => by simp [p11cEv]⟩, ⟨0, 1, fun a _ => by simp [p11cEv]⟩⟩
  | succ j ih =>
    obtain ⟨⟨p0, p1, h0⟩, ⟨r0, r1, h1⟩⟩ := ih
    have hs : (1 / 2 : ℝ) ≤ 1 / 2 + (j : ℝ) := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hc : (1 / 2 : ℝ) + ((j + 1 : ℕ) : ℝ) = 1 / 2 + (j : ℝ) + 1 := by push_cast; ring
    have hpos : (1 / 2 : ℝ) + (j : ℝ) ≠ 0 := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      intro h; linarith
    rw [hc]
    refine ⟨⟨(1 + Polynomial.X ^ 2) * p0 +
        Polynomial.C (2 * (1 - 1 / (1 / 2 + (j : ℚ)))) * Polynomial.X * r0,
      (1 + Polynomial.X ^ 2) * p1 +
        Polynomial.C (2 * (1 - 1 / (1 / 2 + (j : ℚ)))) * Polynomial.X * r1, fun a ha => ?_⟩,
      ⟨(1 + Polynomial.X ^ 2) * Polynomial.C (1 - 1 / (1 / 2 + (j : ℚ))) * r0 +
        Polynomial.C 2 * Polynomial.X * p0,
      (1 + Polynomial.X ^ 2) * Polynomial.C (1 - 1 / (1 / 2 + (j : ℚ))) * r1 +
        Polynomial.C 2 * Polynomial.X * p1, fun a ha => ?_⟩⟩
    · have h3 := p11c_one_sub_sq_ne ha
      beta_reduce at h0 h1 ⊢
      rw [(laplace_up _ a hs ha).1, h0 a ha, h1 a ha]
      simp only [p11cEv, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
        Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_pow]
      simp only [eq_ratCast]
      push_cast
      field_simp
      ring
    · have h3 := p11c_one_sub_sq_ne ha
      beta_reduce at h0 h1 ⊢
      rw [(laplace_up _ a hs ha).2.1, h0 a ha, h1 a ha]
      simp only [p11cEv, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
        Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_pow]
      simp only [eq_ratCast]
      push_cast
      field_simp
      ring

theorem p11cRepD_all (j k : ℕ) :
    p11cRepD j k (fun a => p11c_laplace (1 / 2 + (j : ℝ)) (k : ℤ) a) ∧
      p11cRepD j (k + 1) (fun a => p11c_laplace (1 / 2 + (j : ℝ)) ((k : ℤ) + 1) a) := by
  induction k with
  | zero =>
    obtain ⟨h0, h1⟩ := p11cRepD_base j
    exact ⟨by simpa using h0, by simpa using p11cRepD_mono 1 h1⟩
  | succ k ih =>
    obtain ⟨⟨p0, p1, hk0⟩, ⟨r0, r1, hk1⟩⟩ := ih
    refine ⟨by
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by push_cast; ring]
      exact ⟨r0, r1, hk1⟩, ?_⟩
    have hne : ((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ)) ≠ 0 := by
      intro h
      push_cast at h
      have h2 : ((2 * (j : ℤ) - 1 - 2 * ((k : ℤ) + 1) : ℤ) : ℚ) = 0 := by push_cast; linarith
      have := Int.cast_eq_zero.1 h2
      omega
    have hk : (1 / 2 + (j : ℝ)) - 1 - (((k + 1 : ℕ) : ℤ) : ℝ) ≠ 0 := by
      intro h
      apply hne
      have : (((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by
        push_cast at h ⊢; linarith
      exact_mod_cast this
    have e3 : (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 := by push_cast; ring
    refine ⟨Polynomial.C (((k + 1 : ℕ) : ℚ) + (1 / 2 + (j : ℚ)) - 1) *
        Polynomial.C ((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ))⁻¹ *
        Polynomial.X ^ 2 * p0 - Polynomial.C ((k + 1 : ℕ) : ℚ) *
        Polynomial.C ((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ))⁻¹ *
        (1 + Polynomial.X ^ 2) * r0,
      Polynomial.C (((k + 1 : ℕ) : ℚ) + (1 / 2 + (j : ℚ)) - 1) *
        Polynomial.C ((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ))⁻¹ *
        Polynomial.X ^ 2 * p1 - Polynomial.C ((k + 1 : ℕ) : ℚ) *
        Polynomial.C ((j : ℚ) + 1 / 2 - 1 - ((k + 1 : ℕ) : ℚ))⁻¹ *
        (1 + Polynomial.X ^ 2) * r1, fun a ha => ?_⟩
    have h1 := p11c_one_sub_sq_ne ha
    have h2 := ha.1.ne'
    have := p11c_laplace_step (s := 1 / 2 + (j : ℝ)) ha ((k + 1 : ℕ) : ℤ) hk
    have e2 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
    rw [e2] at this
    rw [e3] at this ⊢
    beta_reduce at hk0 hk1 ⊢
    rw [this, hk0 a ha, hk1 a ha]
    simp only [p11cEv, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_pow]
    have hk' : (1 / 2 + (j : ℝ)) - 1 - ((k : ℝ) + 1) ≠ 0 := by
      intro h; apply hk; push_cast; linarith
    simp only [eq_ratCast]
    push_cast
    field_simp
    ring

/-- The explicit envelope `a ^ k (1 - a ^ 2) ^ (2 j)` for half-integer Laplace coefficients. -/
theorem laplace_reduction_denominator (j k : ℕ) :
    ∃ p0 p1 : Polynomial ℚ, ∀ a ∈ Ioo (0 : ℝ) 1,
      a ^ k * (1 - a ^ 2) ^ (2 * j) ≠ 0 ∧
      p11c_laplace (1 / 2 + (j : ℝ)) k a =
        (Polynomial.eval₂ (algebraMap ℚ ℝ) a p0 * p11c_laplace (1 / 2) 0 a +
         Polynomial.eval₂ (algebraMap ℚ ℝ) a p1 * p11c_laplace (1 / 2) 1 a) /
          (a ^ k * (1 - a ^ 2) ^ (2 * j)) := by
  obtain ⟨p0, p1, h⟩ := (p11cRepD_all j k).1
  exact ⟨p0, p1, fun a ha =>
    ⟨mul_ne_zero (pow_ne_zero _ ha.1.ne') (pow_ne_zero _ (p11c_one_sub_sq_ne ha)), h a ha⟩⟩

end KAM.Planetary
