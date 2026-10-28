/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Trig

/-!
# Planar quartic torsion: one-plane character identities

Blueprint P, Part 11b, steps `stepP:p11b:ch-mon` and `stepP:p11b:ch-bra`.  For the one-plane
Fourier coefficient `charFc`: finite mode support, reconstruction at `θ = 0`, rotation covariance
and homogeneity.
-/

@[expose] public noncomputable section

open Set Real Polynomial
open scoped Polynomial

namespace KAM.Planetary.PlanarCharacters

lemma charFc_eq_zero_of_lt (p q : ℕ) (x y : ℝ) (k : ℤ) (hk : ((p + q : ℕ) : ℤ) < |k|) :
    charFc p q x y k = 0 := by
  rw [charFc_eq]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn' := Finset.mem_range.1 hn
  rw [if_neg]
  intro h
  rcases abs_cases k with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

lemma charG_zero (p q : ℕ) (x y : ℝ) : charG p q x y 0 = x ^ p * y ^ q := by
  simp [charG]

/-- Reconstruction: the Fourier coefficients of one plane add up to the value at `θ = 0`. -/
lemma charFc_sum (p q D : ℕ) (hD : p + q ≤ D) (x y : ℝ) :
    ∑ k ∈ Finset.Icc (-(D : ℤ)) D, charFc p q x y k = ((x ^ p * y ^ q : ℝ) : ℂ) := by
  have h0 := charQc_eval p q x y 0
  rw [eval_eq_sum_range' (n := 2 * (p + q) + 1)
    (Nat.lt_succ_of_le (charQc_natDegree p q x y))] at h0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_pow, mul_one, one_mul,
    charG_zero] at h0
  rw [← h0]
  simp_rw [charFc_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.1 hn
  have : ∀ k : ℤ, ((n : ℤ) = k + ((p + q : ℕ) : ℤ)) ↔ k = (n : ℤ) - ((p + q : ℕ) : ℤ) := by
    intro k; omega
  simp_rw [this]
  rw [Finset.sum_ite_eq' (Finset.Icc (-(D : ℤ)) D)]
  rw [if_pos (by rw [Finset.mem_Icc]; omega)]

lemma charG_rot (p q : ℕ) (x y φ θ : ℝ) :
    charG p q (cos φ * x + sin φ * y) (-sin φ * x + cos φ * y) θ = charG p q x y (θ + φ) := by
  unfold charG
  rw [Real.cos_add, Real.sin_add]
  congr 2 <;> ring

lemma charG_smul (p q : ℕ) (t x y θ : ℝ) :
    charG p q (t * x) (t * y) θ = t ^ (p + q) * charG p q x y θ := by
  unfold charG
  have h1 : cos θ * (t * x) + sin θ * (t * y) = t * (cos θ * x + sin θ * y) := by ring
  have h2 : -sin θ * (t * x) + cos θ * (t * y) = t * (-sin θ * x + cos θ * y) := by ring
  rw [h1, h2, mul_pow, mul_pow, pow_add]; ring

lemma charG_period (p q : ℕ) (x y θ : ℝ) :
    charG p q x y (θ + 2 * π) = charG p q x y θ := by
  simp [charG, Real.cos_add_two_pi, Real.sin_add_two_pi]

lemma charFc_smul (p q : ℕ) (t x y : ℝ) (k : ℤ) :
    charFc p q (t * x) (t * y) k = (t : ℂ) ^ (p + q) * charFc p q x y k := by
  unfold charFc
  have : ∀ θ : ℝ, Complex.exp (-Complex.I * ((k : ℂ) * θ)) * ((charG p q (t * x) (t * y) θ : ℝ) : ℂ) =
      (t : ℂ) ^ (p + q) * (Complex.exp (-Complex.I * ((k : ℂ) * θ)) * (charG p q x y θ : ℂ)) := by
    intro θ; rw [charG_smul]; push_cast; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]; ring

/-- Rotation covariance of the one-plane coefficient. -/
lemma charFc_rot (p q : ℕ) (x y φ : ℝ) (k : ℤ) :
    charFc p q (cos φ * x + sin φ * y) (-sin φ * x + cos φ * y) k =
      Complex.exp (Complex.I * (k * φ)) * charFc p q x y k := by
  unfold charFc
  simp_rw [charG_rot]
  set f : ℝ → ℂ := fun u => Complex.exp (-Complex.I * ((k : ℂ) * u)) * (charG p q x y u : ℂ) with hf
  have hper : Function.Periodic f (2 * π) := by
    intro u
    simp only [hf]
    rw [charG_period]
    congr 1
    have h := Complex.exp_int_mul_two_pi_mul_I (-k)
    have : Complex.exp (-Complex.I * ((k : ℂ) * ((u + 2 * π : ℝ) : ℂ))) =
        Complex.exp (-Complex.I * ((k : ℂ) * u)) * Complex.exp (((-k : ℤ) : ℂ) * (2 * π * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this, h, mul_one]
  have h1 : ∀ θ : ℝ, Complex.exp (-Complex.I * ((k : ℂ) * θ)) * (charG p q x y (θ + φ) : ℂ) =
      Complex.exp (Complex.I * (k * φ)) * f (θ + φ) := by
    intro θ
    simp only [hf]
    rw [← mul_assoc (Complex.exp (Complex.I * ((k : ℂ) * φ))), ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right f φ,
    zero_add, add_comm (2 * π) φ, hper.intervalIntegral_add_eq φ 0, zero_add]
  ring

open MeasureTheory

lemma charBox_integral (g : Fin 2 → ℝ → ℂ) :
    ∫ θ : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)), ∏ j, g j (θ j) =
      ∏ j, ∫ t in (0 : ℝ)..2 * π, g j t := by
  have h : (volume : Measure (Fin 2 → ℝ)).restrict (Set.pi univ fun _ => Icc (0 : ℝ) (2 * π)) =
      Measure.pi fun _ => (volume : Measure ℝ).restrict (Icc (0 : ℝ) (2 * π)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  rw [h, integral_fintype_prod_eq_prod (fun j (t : ℝ) => g j t)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc]

lemma charBox (a : Fin 4 → ℕ) (k : Fin 2 → ℤ) (z : Phase 2) :
    (2 * π : ℂ) ^ (-2 : ℤ) * ∫ theta : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)),
        Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) *
          ((p11c_monomial a (p11c_rotation theta z) : ℝ) : ℂ) =
      charFc (a 0) (a 1) (z.1 0) (z.2 0) (k 0) * charFc (a 2) (a 3) (z.1 1) (z.2 1) (k 1) := by
  let g : Fin 2 → ℝ → ℂ := ![
    fun t => Complex.exp (-Complex.I * ((k 0 : ℂ) * t)) * (charG (a 0) (a 1) (z.1 0) (z.2 0) t : ℂ),
    fun t => Complex.exp (-Complex.I * ((k 1 : ℂ) * t)) * (charG (a 2) (a 3) (z.1 1) (z.2 1) t : ℂ)]
  have hint : ∀ theta : Fin 2 → ℝ, Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) *
      ((p11c_monomial a (p11c_rotation theta z) : ℝ) : ℂ) = ∏ j, g j (theta j) := by
    intro theta
    simp only [Fin.prod_univ_two, Fin.sum_univ_two, g, Matrix.cons_val_zero, Matrix.cons_val_one,
      p11c_monomial, p11c_rotation, charG]
    push_cast
    have key : ∀ A B : ℂ, Complex.exp (-Complex.I * (A + B)) =
        Complex.exp (-Complex.I * A) * Complex.exp (-Complex.I * B) := by
      intro A B; rw [mul_add, Complex.exp_add]
    rw [key]; ring
  simp_rw [hint]
  rw [charBox_integral g]
  simp only [Fin.prod_univ_two, g, Matrix.cons_val_zero, Matrix.cons_val_one, charFc]
  rw [zpow_neg, zpow_two, mul_inv]
  ring

lemma charMono_continuous (a : Fin 4 → ℕ) (z : Phase 2) :
    Continuous fun theta : Fin 2 → ℝ => p11c_monomial a (p11c_rotation theta z) := by
  unfold p11c_monomial p11c_rotation
  fun_prop

/-- The finite exponent index set of `QuarticFamily.eval`. -/
def charIdx : Finset (Fin 4 → Fin 5) :=
  (Finset.univ : Finset (Fin 4 → Fin 5)).filter (fun a => ∑ i, (a i).val = 4)

/-- The character of a quartic family as a finite sum of products of one-plane coefficients. -/
lemma character_eq_sum {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (k : Fin 2 → ℤ)
    (I : Fin 2 → ℝ) (z : Phase 2) :
    p11c_character F.eval k I z = ∑ a ∈ charIdx,
      (F.coeff (fun i => (a i).val) I : ℂ) *
        (charFc ((a 0).val) ((a 1).val) (z.1 0) (z.2 0) (k 0) *
          charFc ((a 2).val) ((a 3).val) (z.1 1) (z.2 1) (k 1)) := by
  unfold p11c_character QuarticFamily.eval charIdx
  have hcont : ∀ a : Fin 4 → Fin 5, Continuous fun theta : Fin 2 → ℝ =>
      Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) *
        (((F.coeff (fun i => (a i).val) I * p11c_monomial (fun i => (a i).val)
          (p11c_rotation theta z) : ℝ)) : ℂ) := by
    intro a
    have := charMono_continuous (fun i => (a i).val) z
    fun_prop
  have hK : IsCompact (Set.pi univ fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsum : ∀ theta : Fin 2 → ℝ, Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) *
      ((∑ a ∈ (Finset.univ : Finset (Fin 4 → Fin 5)).filter (fun a => ∑ i, (a i).val = 4),
        F.coeff (fun i => (a i).val) I * p11c_monomial (fun i => (a i).val)
          (p11c_rotation theta z) : ℝ) : ℂ) =
      ∑ a ∈ (Finset.univ : Finset (Fin 4 → Fin 5)).filter (fun a => ∑ i, (a i).val = 4),
        Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) *
        (((F.coeff (fun i => (a i).val) I * p11c_monomial (fun i => (a i).val)
          (p11c_rotation theta z) : ℝ)) : ℂ) := by
    intro theta; rw [Complex.ofReal_sum, Finset.mul_sum]
  simp_rw [hsum]
  rw [integral_finset_sum _ fun a _ => (hcont a).continuousOn.integrableOn_compact hK,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : ∀ theta : Fin 2 → ℝ, Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) *
      (((F.coeff (fun i => (a i).val) I * p11c_monomial (fun i => (a i).val)
          (p11c_rotation theta z) : ℝ)) : ℂ) =
      (F.coeff (fun i => (a i).val) I : ℂ) * (Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) *
        ((p11c_monomial (fun i => (a i).val) (p11c_rotation theta z) : ℝ) : ℂ)) := by
    intro theta; push_cast; ring
  simp_rw [h1]
  rw [integral_const_mul, ← mul_assoc, mul_comm _ (F.coeff _ I : ℂ), mul_assoc]
  congr 1
  exact charBox (fun i => (a i).val) k z

end KAM.Planetary.PlanarCharacters

end
