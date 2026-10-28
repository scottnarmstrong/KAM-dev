/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Frame
public import KAM.Planetary.PlanarTorsion.Quartic
public import KAM.Planetary.PlanarTorsion.Characters

/-!
# Planar quartic torsion: the torsion matrix `beta` (P11C, package T13)

Blueprint P, Part 11b (`bpP:p11b:beta-def`, `bpP:p11b:beta-formula`, `stepP:p11b:bf-gram`,
`stepP:p11b:bf-avg`): `beta_def` is the explicit projector-only torsion formula (factors 8 on the
diagonal, 4 off it), `p11c_beta` its value on the physical data, `beta_formula` the statement that
it is the torus average of the rotated quartic, and `beta_properties` its analyticity on the axis
cone and its symmetry.

`beta_formula` follows the blueprint.  The Gram step (`bf-gram`) writes the rotated quartic as a
polynomial `p11cBetaGram` in `r₁ = |z₁|²`, `r₂ = |z₂|²` and `g = z₁ · z₂`; the averaging step
(`bf-avg`) uses `⟨g⟩ = 0` and `⟨g²⟩ = r₁ r₂ / 2` on the torus, computed from one-variable
integrals through the product-box lemma `p11c_boxIntegral_prod`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM KAM.Kepler

def beta_def (c : Fin 6 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let u := P 0 0; let v := P 1 1; let w := P 0 1; let D := u - v
  let A := c 0 * u ^ 2 + c 1 * v ^ 2 + (c 2 + c 3) * u * v + (c 4 * u + c 5 * v) * w
  let E := c 0 * v ^ 2 + c 1 * u ^ 2 + (c 2 + c 3) * u * v - (c 4 * v + c 5 * u) * w
  let B := 4 * (c 0 + c 1) * u * v + c 2 * D ^ 2 + c 3 * (D ^ 2 / 2 - 2 * u * v) +
    2 * (c 5 - c 4) * w * D
  !![8 * A, 4 * B; 4 * B, 8 * E]

def p11c_beta (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  beta_def (p11c_coeffs p a) (p11c_projector p a)

/-! ### Symmetry and analyticity -/

theorem beta_def_isSymm (c : Fin 6 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) :
    (beta_def c P).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [beta_def]

/-- The spectral projector is analytic on the axis cone. -/
theorem p11c_projector_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) (i j : Fin 2) :
    AnalyticAt ℝ (fun b => p11c_projector p b i j) a := by
  have hs0 := p11c_sigma0_analyticAt p hp ha
  have hQ := p11c_Q_analyticAt p hp ha
  have hs1 : AnalyticAt ℝ (fun b => p11c_sigma p b 1) a := by
    have h := (((hQ 0 0).add (hQ 1 1)).sub hs0)
    refine h.congr ?_
    filter_upwards [p11c_axes_isOpen.mem_nhds ha] with b hb
    simp only [Pi.add_apply, Pi.sub_apply]
    linarith [(p11c_sigma_sum_prod p hp hb).1]
  have hne : p11c_sigma p a 0 - p11c_sigma p a 1 ≠ 0 :=
    (sub_neg.2 (p11c_sigma_lt p hp ha)).ne
  have hinv := (hs0.sub hs1).inv hne
  have hdiag : ∀ k, AnalyticAt ℝ (fun b => p11c_Q p b k k - p11c_sigma p b 1) a :=
    fun k => (hQ k k).sub hs1
  fin_cases i <;> fin_cases j
  · exact hinv.mul (hdiag 0) |>.congr (Eventually.of_forall fun b => by
      simp [p11c_projector])
  · exact hinv.mul (hQ 0 1) |>.congr (Eventually.of_forall fun b => by
      simp [p11c_projector])
  · exact hinv.mul (hQ 1 0) |>.congr (Eventually.of_forall fun b => by
      simp [p11c_projector])
  · exact hinv.mul (hdiag 1) |>.congr (Eventually.of_forall fun b => by
      simp [p11c_projector])

theorem beta_properties (p : PlanarData) (hp : p.Valid) :
    (∀ i j, AnalyticOnNhd ℝ (fun a => p11c_beta p a i j) p11c_axes) ∧
      ∀ a, (p11c_beta p a).IsSymm := by
  refine ⟨fun i j a ha => ?_, fun a => beta_def_isSymm _ _⟩
  have hc : ∀ k, AnalyticAt ℝ (fun b => p11c_coeffs p b k) a := fun k =>
    analyticAt_pi_iff.1 ((quartic_explicit p hp).1 a ha) k
  have hP := p11c_projector_analyticAt p hp ha
  have hu := hP 0 0
  have hv := hP 1 1
  have hw := hP 0 1
  fin_cases i <;> fin_cases j <;> simp only [p11c_beta, beta_def] <;> simp <;> fun_prop

/-! ### The torus average of the rotated quartic -/

/-- Product box lemma: the integral over the box `[0, 2π]²` of `f₀(θ₀) f₁(θ₁)` factorises. -/
theorem p11c_boxIntegral_prod (f0 f1 : ℝ → ℝ) :
    ∫ θ : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)), f0 (θ 0) * f1 (θ 1) =
      (∫ t in (0 : ℝ)..2 * π, f0 t) * ∫ t in (0 : ℝ)..2 * π, f1 t := by
  have h : (volume : Measure (Fin 2 → ℝ)).restrict (Set.pi univ fun _ => Icc (0 : ℝ) (2 * π)) =
      Measure.pi fun _ => (volume : Measure ℝ).restrict (Icc (0 : ℝ) (2 * π)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  rw [h]
  have := integral_fintype_prod_eq_prod (fun j : Fin 2 => fun t : ℝ => ![f0, f1] j t)
    (μ := fun _ => (volume : Measure ℝ).restrict (Icc (0 : ℝ) (2 * π)))
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [this, intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc]

theorem p11c_boxIntegrableOn {f : (Fin 2 → ℝ) → ℝ} (hf : Continuous f) :
    IntegrableOn f (Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π))) :=
  hf.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)

private theorem int_a (x y : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, (cos t * x + sin t * y) = 0 := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

private theorem int_b (x y : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, (-sin t * x + cos t * y) = 0 := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

private theorem int_aa (x y : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, (cos t * x + sin t * y) ^ 2 = π * (x ^ 2 + y ^ 2) := by
  have : ∀ t : ℝ, (cos t * x + sin t * y) ^ 2 =
      x ^ 2 * cos t ^ 2 + (2 * x * y) * (sin t * cos t) + y ^ 2 * sin t ^ 2 := fun t => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [integral_cos_sq, integral_sin_sq, integral_sin_mul_cos₁]
  ring

private theorem int_bb (x y : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, (-sin t * x + cos t * y) ^ 2 = π * (x ^ 2 + y ^ 2) := by
  have : ∀ t : ℝ, (-sin t * x + cos t * y) ^ 2 =
      x ^ 2 * sin t ^ 2 - (2 * x * y) * (sin t * cos t) + y ^ 2 * cos t ^ 2 := fun t => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [integral_cos_sq, integral_sin_sq, integral_sin_mul_cos₁]
  ring

private theorem int_ab (x y : ℝ) :
    ∫ t in (0 : ℝ)..2 * π, (cos t * x + sin t * y) * (-sin t * x + cos t * y) = 0 := by
  have : ∀ t : ℝ, (cos t * x + sin t * y) * (-sin t * x + cos t * y) =
      (y ^ 2 - x ^ 2) * (sin t * cos t) + (x * y) * cos t ^ 2 + (-(x * y)) * sin t ^ 2 :=
    fun t => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp [integral_cos_sq, integral_sin_sq, integral_sin_mul_cos₁]

/-- The real torus average at `I`, written as a box integral. -/
theorem p11c_average_eq_boxIntegral (F : (Fin 2 → ℝ) → Phase 2 → ℝ) (I : Fin 2 → ℝ)
    (z : Phase 2) :
    p11c_average F I z = ((2 * π) ^ 2)⁻¹ *
      ∫ θ : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)), F I (p11c_rotation θ z) := by
  unfold p11c_average p11c_character
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, mul_zero,
    Complex.exp_zero, one_mul]
  rw [integral_complex_ofReal]
  have : (2 * π : ℂ) ^ (-2 : ℤ) = (((2 * π) ^ 2)⁻¹ : ℝ) := by
    push_cast
    rw [zpow_neg, zpow_two, sq]
  rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Gram polynomial of the rotated quartic in `r₁, r₂` and `g = z₁ · z₂` (`bf-gram`). -/
def p11cBetaGram (c : Fin 6 → ℝ) (γ s r0 r1 G : ℝ) : ℝ :=
  let A1 := γ ^ 2 * r0 + s ^ 2 * r1 - 2 * γ * s * G
  let A2 := s ^ 2 * r0 + γ ^ 2 * r1 + 2 * γ * s * G
  let B := γ * s * (r0 - r1) + (γ ^ 2 - s ^ 2) * G
  c 0 * A1 ^ 2 + c 1 * A2 ^ 2 + c 2 * A1 * A2 + c 3 * B ^ 2 + c 4 * A1 * B + c 5 * A2 * B

/-- `bf-gram`: the rotated quartic is the Gram polynomial. -/
theorem p11c_quartic_rotateSlow_gram (c : Fin 6 → ℝ) (γ s : ℝ) (w : Phase 2) :
    p11c_quartic c (p11c_rotateSlow !![γ, -s; s, γ] w) =
      p11cBetaGram c γ s (w.1 0 ^ 2 + w.2 0 ^ 2) (w.1 1 ^ 2 + w.2 1 ^ 2)
        (w.1 0 * w.1 1 + w.2 0 * w.2 1) := by
  simp only [p11c_quartic, p11c_pairDot, p11c_rotateSlow, p11cBetaGram, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- The Gram polynomial is a quadratic in `G`. -/
theorem p11cBetaGram_quad (c : Fin 6 → ℝ) (γ s r0 r1 G : ℝ) :
    p11cBetaGram c γ s r0 r1 G = p11cBetaGram c γ s r0 r1 0 +
      G * ((p11cBetaGram c γ s r0 r1 1 - p11cBetaGram c γ s r0 r1 (-1)) / 2) +
      G ^ 2 * ((p11cBetaGram c γ s r0 r1 1 + p11cBetaGram c γ s r0 r1 (-1)) / 2 -
        p11cBetaGram c γ s r0 r1 0) := by
  simp only [p11cBetaGram]
  ring

/-- The cross Gram variable `g` after rotating by `θ`. -/
def p11cGramRot (z : Phase 2) (θ : Fin 2 → ℝ) : ℝ :=
  (p11c_rotation θ z).1 0 * (p11c_rotation θ z).1 1 +
    (p11c_rotation θ z).2 0 * (p11c_rotation θ z).2 1

theorem p11c_rotation_sq (θ : Fin 2 → ℝ) (z : Phase 2) (j : Fin 2) :
    (p11c_rotation θ z).1 j ^ 2 + (p11c_rotation θ z).2 j ^ 2 = z.1 j ^ 2 + z.2 j ^ 2 := by
  simp only [p11c_rotation]
  linear_combination (z.1 j ^ 2 + z.2 j ^ 2) * sin_sq_add_cos_sq (θ j)

theorem p11cGramRot_continuous (z : Phase 2) : Continuous (p11cGramRot z) := by
  unfold p11cGramRot p11c_rotation
  fun_prop

/-- `bf-avg`: `⟨g⟩ = 0`. -/
theorem p11cGramRot_integral (z : Phase 2) :
    ∫ θ : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)), p11cGramRot z θ = 0 := by
  have h : ∀ θ : Fin 2 → ℝ, p11cGramRot z θ =
      (cos (θ 0) * z.1 0 + sin (θ 0) * z.2 0) * (cos (θ 1) * z.1 1 + sin (θ 1) * z.2 1) +
      (-sin (θ 0) * z.1 0 + cos (θ 0) * z.2 0) * (-sin (θ 1) * z.1 1 + cos (θ 1) * z.2 1) :=
    fun θ => rfl
  simp_rw [h]
  rw [integral_add (p11c_boxIntegrableOn (by fun_prop)) (p11c_boxIntegrableOn (by fun_prop)),
    p11c_boxIntegral_prod (fun t => cos t * z.1 0 + sin t * z.2 0)
      (fun t => cos t * z.1 1 + sin t * z.2 1),
    p11c_boxIntegral_prod (fun t => -sin t * z.1 0 + cos t * z.2 0)
      (fun t => -sin t * z.1 1 + cos t * z.2 1), int_a, int_b]
  simp

/-- `bf-avg`: `⟨g²⟩ = r₁ r₂ / 2`, as `2 π² r₁ r₂` before dividing by `(2π)²`. -/
theorem p11cGramRot_sq_integral (z : Phase 2) :
    ∫ θ : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)), p11cGramRot z θ ^ 2 =
      π ^ 2 * ((z.1 0 ^ 2 + z.2 0 ^ 2) * (z.1 1 ^ 2 + z.2 1 ^ 2)) * 2 := by
  have h : ∀ θ : Fin 2 → ℝ, p11cGramRot z θ ^ 2 =
      (cos (θ 0) * z.1 0 + sin (θ 0) * z.2 0) ^ 2 * (cos (θ 1) * z.1 1 + sin (θ 1) * z.2 1) ^ 2 +
      (2 * ((cos (θ 0) * z.1 0 + sin (θ 0) * z.2 0) * (-sin (θ 0) * z.1 0 + cos (θ 0) * z.2 0))) *
        ((cos (θ 1) * z.1 1 + sin (θ 1) * z.2 1) * (-sin (θ 1) * z.1 1 + cos (θ 1) * z.2 1)) +
      (-sin (θ 0) * z.1 0 + cos (θ 0) * z.2 0) ^ 2 *
        (-sin (θ 1) * z.1 1 + cos (θ 1) * z.2 1) ^ 2 := fun θ => by
    simp only [p11cGramRot, p11c_rotation]; ring
  simp_rw [h]
  rw [integral_add, integral_add,
    p11c_boxIntegral_prod (fun t => (cos t * z.1 0 + sin t * z.2 0) ^ 2)
      (fun t => (cos t * z.1 1 + sin t * z.2 1) ^ 2),
    p11c_boxIntegral_prod
      (fun t => 2 * ((cos t * z.1 0 + sin t * z.2 0) * (-sin t * z.1 0 + cos t * z.2 0)))
      (fun t => (cos t * z.1 1 + sin t * z.2 1) * (-sin t * z.1 1 + cos t * z.2 1)),
    p11c_boxIntegral_prod (fun t => (-sin t * z.1 0 + cos t * z.2 0) ^ 2)
      (fun t => (-sin t * z.1 1 + cos t * z.2 1) ^ 2),
    intervalIntegral.integral_const_mul, int_aa, int_aa, int_bb, int_bb, int_ab, int_ab]
  · ring
  all_goals exact p11c_boxIntegrableOn (by fun_prop)

theorem beta_formula (c : Fin 6 → ℝ) (g s : ℝ) (h : g ^ 2 + s ^ 2 = 1) (z : Phase 2) :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![g, -s; s, g]
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![g ^ 2, g * s; g * s, s ^ 2]
    p11c_average (fun _ w => p11c_quartic c (p11c_rotateSlow U w)) 0 z =
      (1 / 2 : ℝ) * ∑ i, ∑ j, beta_def c P i j * oscillatorAction z.2 z.1 i *
        oscillatorAction z.2 z.1 j := by
  intro U P
  rw [p11c_average_eq_boxIntegral]
  have hint : ∀ θ : Fin 2 → ℝ, p11c_quartic c (p11c_rotateSlow U (p11c_rotation θ z)) =
      p11cBetaGram c g s (z.1 0 ^ 2 + z.2 0 ^ 2) (z.1 1 ^ 2 + z.2 1 ^ 2) 0 +
      p11cGramRot z θ * ((p11cBetaGram c g s (z.1 0 ^ 2 + z.2 0 ^ 2) (z.1 1 ^ 2 + z.2 1 ^ 2) 1 -
        p11cBetaGram c g s (z.1 0 ^ 2 + z.2 0 ^ 2) (z.1 1 ^ 2 + z.2 1 ^ 2) (-1)) / 2) +
      p11cGramRot z θ ^ 2 * ((p11cBetaGram c g s (z.1 0 ^ 2 + z.2 0 ^ 2) (z.1 1 ^ 2 + z.2 1 ^ 2) 1
        + p11cBetaGram c g s (z.1 0 ^ 2 + z.2 0 ^ 2) (z.1 1 ^ 2 + z.2 1 ^ 2) (-1)) / 2 -
        p11cBetaGram c g s (z.1 0 ^ 2 + z.2 0 ^ 2) (z.1 1 ^ 2 + z.2 1 ^ 2) 0) := by
    intro θ
    rw [p11c_quartic_rotateSlow_gram, p11c_rotation_sq, p11c_rotation_sq,
      p11cBetaGram_quad]
    rfl
  simp_rw [hint]
  have hc := p11cGramRot_continuous z
  have hconst : ∀ K : ℝ, ∫ θ : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)), K =
      (2 * π) * K * (2 * π) := fun K => by
    have := p11c_boxIntegral_prod (fun _ => K) (fun _ => 1)
    simpa using this
  rw [integral_add, integral_add, integral_mul_const, integral_mul_const, p11cGramRot_integral,
    p11cGramRot_sq_integral, hconst]
  · simp only [beta_def, p11cBetaGram, oscillatorAction, Fin.sum_univ_two, P]
    simp
    field_simp
    ring
  all_goals exact p11c_boxIntegrableOn (by fun_prop)

end KAM.Planetary

end
