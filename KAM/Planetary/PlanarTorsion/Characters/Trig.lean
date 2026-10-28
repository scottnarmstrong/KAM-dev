/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Defs

/-!
# Planar quartic torsion: the one-plane trigonometric expansion

Blueprint P, Part 11b, step `stepP:p11b:ch-mon`.  For one oscillator plane the rotated monomial
`(cos θ x + sin θ y)^p (-sin θ x + cos θ y)^q` is a trigonometric polynomial of degree `p + q`;
its Fourier coefficients are the coefficients of an explicit polynomial in `E = e^{iθ}` whose own
coefficients are polynomials in `(x, y)` of total degree at most `p + q`.
-/

@[expose] public noncomputable section

open Set Real Polynomial
open scoped Polynomial

namespace KAM.Planetary.PlanarCharacters

/-- One-plane rotated monomial. -/
def charG (p q : ℕ) (x y θ : ℝ) : ℝ :=
  (cos θ * x + sin θ * y) ^ p * (-sin θ * x + cos θ * y) ^ q

/-- The coordinate `x + i y` as a polynomial. -/
def charW : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1

/-- The coordinate `x - i y` as a polynomial. -/
def charWb : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1

/-- `E · u` as a polynomial in `E`, over the coefficient ring `ℂ[x, y]`. -/
def charUP : (MvPolynomial (Fin 2) ℂ)[X] :=
  Polynomial.C (MvPolynomial.C (1 / 2 : ℂ) * charWb) * Polynomial.X ^ 2 +
    Polynomial.C (MvPolynomial.C (1 / 2 : ℂ) * charW)

/-- `E · v` as a polynomial in `E`, over the coefficient ring `ℂ[x, y]`. -/
def charVP : (MvPolynomial (Fin 2) ℂ)[X] :=
  Polynomial.C (MvPolynomial.C (Complex.I / 2) * charWb) * Polynomial.X ^ 2 -
    Polynomial.C (MvPolynomial.C (Complex.I / 2) * charW)

/-- The expansion polynomial of the rotated monomial `x^p y^q`. -/
def charQ (p q : ℕ) : (MvPolynomial (Fin 2) ℂ)[X] := charUP ^ p * charVP ^ q

/-- Its specialization at a real point. -/
def charQc (p q : ℕ) (x y : ℝ) : ℂ[X] :=
  (charQ p q).map (MvPolynomial.eval ![(x : ℂ), (y : ℂ)])

lemma charQc_def (p q : ℕ) (x y : ℝ) :
    charQc p q x y =
      ((Polynomial.C (((x : ℂ) - Complex.I * y) / 2) * Polynomial.X ^ 2 +
          Polynomial.C (((x : ℂ) + Complex.I * y) / 2)) ^ p *
        (Polynomial.C (Complex.I / 2 * ((x : ℂ) - Complex.I * y)) * Polynomial.X ^ 2 -
          Polynomial.C (Complex.I / 2 * ((x : ℂ) + Complex.I * y))) ^ q) := by
  have hw : MvPolynomial.eval ![(x : ℂ), (y : ℂ)] charW = (x : ℂ) + Complex.I * y := by
    simp [charW]
  have hwb : MvPolynomial.eval ![(x : ℂ), (y : ℂ)] charWb = (x : ℂ) - Complex.I * y := by
    simp [charWb]
  have hu : charUP.map (MvPolynomial.eval ![(x : ℂ), (y : ℂ)]) =
      Polynomial.C (((x : ℂ) - Complex.I * y) / 2) * Polynomial.X ^ 2 +
          Polynomial.C (((x : ℂ) + Complex.I * y) / 2) := by
    simp only [charUP, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_C, Polynomial.map_X, map_mul, MvPolynomial.eval_C, hw, hwb]
    simp only [← Polynomial.C_mul, div_eq_inv_mul, mul_one]
  have hv : charVP.map (MvPolynomial.eval ![(x : ℂ), (y : ℂ)]) =
      Polynomial.C (Complex.I / 2 * ((x : ℂ) - Complex.I * y)) * Polynomial.X ^ 2 -
          Polynomial.C (Complex.I / 2 * ((x : ℂ) + Complex.I * y)) := by
    simp only [charVP, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_C, Polynomial.map_X, map_mul, MvPolynomial.eval_C, hw, hwb]
  simp only [charQc, charQ, Polynomial.map_mul, Polynomial.map_pow, hu, hv]

lemma charQc_natDegree (p q : ℕ) (x y : ℝ) : (charQc p q x y).natDegree ≤ 2 * (p + q) := by
  rw [charQc_def]
  refine (natDegree_mul_le).trans ?_
  have h1 : (Polynomial.C (((x : ℂ) - Complex.I * y) / 2) * Polynomial.X ^ 2 +
      Polynomial.C (((x : ℂ) + Complex.I * y) / 2)).natDegree ≤ 2 := by compute_degree
  have h2 : (Polynomial.C (Complex.I / 2 * ((x : ℂ) - Complex.I * y)) * Polynomial.X ^ 2 -
      Polynomial.C (Complex.I / 2 * ((x : ℂ) + Complex.I * y))).natDegree ≤ 2 := by compute_degree
  have h3 := (natDegree_pow_le (p := _) (n := p)).trans (Nat.mul_le_mul_left p h1)
  have h4 := (natDegree_pow_le (p := _) (n := q)).trans (Nat.mul_le_mul_left q h2)
  omega

lemma charAlg1 (x y c s I : ℂ) (hc : c ^ 2 + s ^ 2 = 1) (hI : I ^ 2 = -1) :
    (x - I * y) / 2 * (c + s * I) ^ 2 + (x + I * y) / 2 = (c + s * I) * (c * x + s * y) := by
  linear_combination (-I * y / 2 - x / 2) * hc + (-I * s ^ 2 * y / 2 - c * s * y + s ^ 2 * x / 2) * hI

lemma charAlg2 (x y c s I : ℂ) (hc : c ^ 2 + s ^ 2 = 1) (hI : I ^ 2 = -1) :
    I / 2 * (x - I * y) * (c + s * I) ^ 2 - I / 2 * (x + I * y) =
      (c + s * I) * (-s * x + c * y) := by
  linear_combination (-I ^ 2 * y / 2 + I * x / 2 - y) * hc +
    (-I ^ 2 * s ^ 2 * y / 2 - I * c * s * y + I * s ^ 2 * x / 2 + c * s * x + s ^ 2 * y - y) * hI

/-- Evaluation at `E = e^{iθ}`: `E^d · G = Q(E)`. -/
lemma charQc_eval (p q : ℕ) (x y θ : ℝ) :
    (charQc p q x y).eval (Complex.exp (Complex.I * θ)) =
      Complex.exp (Complex.I * θ) ^ (p + q) * (charG p q x y θ : ℂ) := by
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hE : Complex.exp (Complex.I * θ) = (Real.cos θ : ℂ) + Real.sin θ * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I]; simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  have hu := charAlg1 x y (Real.cos θ) (Real.sin θ) Complex.I hc Complex.I_sq
  have hv := charAlg2 x y (Real.cos θ) (Real.sin θ) Complex.I hc Complex.I_sq
  rw [← hE] at hu hv
  rw [charQc_def]
  simp only [eval_mul, eval_pow, eval_add, eval_sub, eval_C, eval_X]
  rw [hu, hv, charG, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
  push_cast
  rw [pow_add, mul_pow, mul_pow]; ring

/-- Trigonometric expansion of the rotated monomial. -/
lemma charG_expand (p q : ℕ) (x y θ : ℝ) :
    (charG p q x y θ : ℂ) = ∑ n ∈ Finset.range (2 * (p + q) + 1),
      (charQc p q x y).coeff n * Complex.exp (Complex.I * (((n : ℤ) - ((p + q : ℕ) : ℤ) : ℤ) : ℂ) * θ) := by
  have h := charQc_eval p q x y θ
  rw [eval_eq_sum_range' (n := 2 * (p + q) + 1)
    (Nat.lt_succ_of_le (charQc_natDegree p q x y))] at h
  have hE : Complex.exp (Complex.I * θ) ^ (p + q) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have h2 : (charG p q x y θ : ℂ) = Complex.exp (-(Complex.I * θ)) ^ (p + q) *
      ∑ i ∈ Finset.range (2 * (p + q) + 1), (charQc p q x y).coeff i * Complex.exp (Complex.I * θ) ^ i := by
    rw [h, ← mul_assoc, ← mul_pow, ← Complex.exp_add]; simp
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- Orthogonality of characters on `[0, 2π]`, nonzero mode. -/
lemma charInt_ne (m : ℤ) (hm : m ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.exp (Complex.I * (m : ℂ) * θ) = 0 := by
  have hc : Complex.I * (m : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hm)
  have := integral_exp_mul_complex (a := (0 : ℝ)) (b := 2 * π) hc
  simp only [mul_assoc] at this ⊢
  rw [this]
  have h1 : Complex.exp (Complex.I * ((m : ℂ) * ((2 * π : ℝ) : ℂ))) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I m
    rw [← this]; congr 1; push_cast; ring
  rw [h1]; simp

/-- Orthogonality of characters on `[0, 2π]`, zero mode. -/
lemma charInt_zero :
    ∫ θ in (0 : ℝ)..2 * π, Complex.exp (Complex.I * ((0 : ℤ) : ℂ) * θ) = 2 * π := by
  simp

/-- Fourier coefficient of the one-plane rotated monomial. -/
def charFc (p q : ℕ) (x y : ℝ) (k : ℤ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
    Complex.exp (-Complex.I * ((k : ℂ) * θ)) * (charG p q x y θ : ℂ)

lemma charFc_eq (p q : ℕ) (x y : ℝ) (k : ℤ) :
    charFc p q x y k = ∑ n ∈ Finset.range (2 * (p + q) + 1),
      if (n : ℤ) = k + ((p + q : ℕ) : ℤ) then (charQc p q x y).coeff n else 0 := by
  unfold charFc
  have hint : ∀ θ : ℝ, Complex.exp (-Complex.I * ((k : ℂ) * θ)) * (charG p q x y θ : ℂ) =
      ∑ n ∈ Finset.range (2 * (p + q) + 1), (charQc p q x y).coeff n *
        Complex.exp (Complex.I * ((((n : ℤ) - ((p + q : ℕ) : ℤ) - k : ℤ)) : ℂ) * θ) := by
    intro θ
    rw [charG_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  simp_rw [hint]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul]
    have h2 : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    by_cases hn : (n : ℤ) = k + ((p + q : ℕ) : ℤ)
    · have h3 : (n : ℤ) - ((p + q : ℕ) : ℤ) - k = 0 := by omega
      rw [h3, charInt_zero]; simp only [hn, ite_true]; field_simp
    · have h3 : (n : ℤ) - ((p + q : ℕ) : ℤ) - k ≠ 0 := by omega
      rw [charInt_ne _ h3, mul_zero, mul_zero]
      exact (ite_eq_right_iff.2 fun h => (hn h).elim).symm
  · intro n _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)

end KAM.Planetary.PlanarCharacters

end
