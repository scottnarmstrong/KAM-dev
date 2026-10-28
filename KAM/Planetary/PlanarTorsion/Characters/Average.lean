/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Basic

/-!
# Planar quartic torsion: the zero mode of one plane

Blueprint P, Part 11b (`bpP:p11b:char`): the zero Fourier mode of the rotated one-plane monomial is
invariant under rotations and homogeneous, hence a constant multiple of a power of `x² + y²`
(and zero in odd degree).
-/

@[expose] public noncomputable section

open Set Real
open scoped Polynomial

namespace KAM.Planetary.PlanarCharacters

/-- The unit-axis zero mode of the one-plane coefficient. -/
def charK (p q : ℕ) : ℂ := charFc p q 1 0 0

lemma charFc_zero_radial (p q : ℕ) (x y : ℝ) :
    charFc p q x y 0 = ((‖(⟨x, y⟩ : ℂ)‖ ^ (p + q) : ℝ) : ℂ) * charK p q := by
  set w : ℂ := ⟨x, y⟩ with hw
  set r := ‖w‖ with hr
  have hx : cos (-Complex.arg w) * r + sin (-Complex.arg w) * 0 = x := by
    have := Complex.norm_mul_cos_arg w
    simp only [Real.cos_neg, Real.sin_neg, mul_zero, add_zero]
    rw [mul_comm]; exact this
  have hy : -sin (-Complex.arg w) * r + cos (-Complex.arg w) * 0 = y := by
    have := Complex.norm_mul_sin_arg w
    simp only [Real.cos_neg, Real.sin_neg, mul_zero, add_zero, neg_neg]
    rw [mul_comm]; exact this
  have h1 := charFc_rot p q r 0 (-Complex.arg w) 0
  rw [hx, hy] at h1
  rw [h1]
  have h2 := charFc_smul p q r 1 0 0
  rw [mul_one, mul_zero] at h2
  rw [h2]
  simp [charK]

lemma charK_odd (p q : ℕ) (h : ¬ Even (p + q)) : charK p q = 0 := by
  have h1 := charFc_rot p q 1 0 π 0
  have h2 := charFc_smul p q (-1) 1 0 0
  simp only [Real.cos_pi, Real.sin_pi, mul_one, mul_zero, add_zero, neg_zero, zero_mul,
    one_mul, Int.cast_zero, Complex.ofReal_neg, Complex.ofReal_one, mul_zero,
    Complex.exp_zero] at h1 h2
  have h3 : charK p q = (-1 : ℂ) ^ (p + q) * charK p q := by
    unfold charK; rw [← h2]; exact h1.symm
  rw [Nat.not_even_iff_odd.1 h |>.neg_one_pow] at h3
  have : charK p q = - charK p q := by linear_combination h3
  linear_combination this / 2

lemma charFc_zero_odd (p q : ℕ) (h : ¬ Even (p + q)) (x y : ℝ) : charFc p q x y 0 = 0 := by
  rw [charFc_zero_radial, charK_odd p q h, mul_zero]

lemma charFc_zero_even (p q m : ℕ) (h : p + q = 2 * m) (x y : ℝ) :
    charFc p q x y 0 = (((x ^ 2 + y ^ 2) ^ m : ℝ) : ℂ) * charK p q := by
  rw [charFc_zero_radial, h]
  congr 2
  rw [pow_mul, Complex.sq_norm, Complex.normSq_mk]
  ring

end KAM.Planetary.PlanarCharacters

namespace KAM.Planetary

open KAM.Planetary.PlanarCharacters

/-- Weight of the exponent vector `a` in the average. -/
def charLam (a : Fin 4 → Fin 5) : ℝ :=
  if Even ((a 0).val + (a 1).val) then
    (charK (a 0).val (a 1).val * charK (a 2).val (a 3).val).re
  else 0

lemma charAvg_term {a : Fin 4 → Fin 5} (ha : a ∈ charIdx) (x0 y0 x1 y1 : ℝ) :
    (charFc (a 0).val (a 1).val x0 y0 0 * charFc (a 2).val (a 3).val x1 y1 0).re =
      (if (a 0).val + (a 1).val = 4 then 4 * charLam a * ((y0 ^ 2 + x0 ^ 2) / 2) ^ 2 else 0) +
      (if (a 0).val + (a 1).val = 2 then
        4 * charLam a * (((y0 ^ 2 + x0 ^ 2) / 2) * ((y1 ^ 2 + x1 ^ 2) / 2)) else 0) +
      (if (a 0).val + (a 1).val = 0 then 4 * charLam a * ((y1 ^ 2 + x1 ^ 2) / 2) ^ 2 else 0) := by
  have h4 := charIdx_sum ha
  by_cases hev : Even ((a 0).val + (a 1).val)
  · obtain ⟨m0, hm0⟩ := hev
    have hm1 : (a 2).val + (a 3).val = 2 * (2 - m0) := by omega
    have hle : m0 ≤ 2 := by omega
    rw [charFc_zero_even _ _ m0 (by omega), charFc_zero_even _ _ (2 - m0) hm1]
    have hlam : charLam a = (charK (a 0).val (a 1).val * charK (a 2).val (a 3).val).re := by
      rw [charLam, if_pos ⟨m0, hm0⟩]
    have hprod : ∀ r0 r1 : ℝ, ((r0 : ℂ) * charK (a 0).val (a 1).val *
        ((r1 : ℂ) * charK (a 2).val (a 3).val)).re = r0 * r1 * charLam a := by
      intro r0 r1
      rw [hlam, show (r0 : ℂ) * charK (a 0).val (a 1).val * ((r1 : ℂ) * charK (a 2).val (a 3).val) =
        ((r0 * r1 : ℝ) : ℂ) * (charK (a 0).val (a 1).val * charK (a 2).val (a 3).val) by
          push_cast; ring, Complex.re_ofReal_mul]
    rw [hprod]
    have e0 : (a 0).val + (a 1).val = 2 * m0 := by omega
    interval_cases m0
    · simp [e0]; ring
    · simp [e0]; ring
    · simp [e0]; ring
  · have h1 : (a 0).val + (a 1).val ≠ 4 := fun h => hev (by rw [h]; decide)
    have h2 : (a 0).val + (a 1).val ≠ 2 := fun h => hev (by rw [h]; decide)
    have h3 : (a 0).val + (a 1).val ≠ 0 := fun h => hev (by rw [h]; decide)
    rw [charFc_zero_odd _ _ hev, if_neg h1, if_neg h2, if_neg h3]
    simp

end KAM.Planetary

end
