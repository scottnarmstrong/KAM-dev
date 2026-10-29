/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# Elementary real inequalities for the rescaled deviation bounds (P11A-P8b2)

Pure inequalities among powers of `ε`, with no reference to the KAM data: the rescaling by
`ε ^ |β|` turns each Cauchy bound of step `pr-in` into a bound `≤ ε · (…)`.
-/

@[expose] public noncomputable section
namespace KAM.Planetary

section Num

theorem p11_num_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a : ℕ) : x ^ a ≤ 1 :=
  pow_le_one₀ hx0 hx1

/-- Rescaled `g₂` term: `ε^j · P Q c ε³ L / ((s/4)^a (ε/4)^b) ≤ P Q 4^b c ε² L` for `a + b = j + 1`. -/
theorem p11_num_g {e s P Q cc L5 : ℝ} (he : 0 < e) (hs : 5 * e ≤ s) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hc : 0 ≤ cc) (hL : 0 ≤ L5) (a b j : ℕ) (hj : a + b = j + 1) :
    e ^ j * (P * Q * (cc * e ^ 3 * L5) / ((s / 4) ^ a * (e / 4) ^ b)) ≤
      P * Q * 4 ^ b * (cc * e ^ 2 * L5) := by
  have hs0 : 0 < s := by linarith
  have hej : e ^ (a + b) = e * e ^ j := by rw [hj, pow_succ, mul_comm]
  have h1 : e ^ (a + b) * (P * Q * (cc * e ^ 3 * L5) / ((s / 4) ^ a * (e / 4) ^ b)) =
      e * (P * Q * 4 ^ b * (cc * e ^ 2 * L5)) * (4 * e / s) ^ a := by
    simp only [div_pow, mul_pow]
    have : (0 : ℝ) < s ^ a := by positivity
    field_simp
    ring
  have hx : (4 * e / s) ^ a ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one hs0).2 (by linarith))
  have h2 : 0 ≤ P * Q * 4 ^ b * (cc * e ^ 2 * L5) := by positivity
  have h3 : e * (e ^ j * (P * Q * (cc * e ^ 3 * L5) / ((s / 4) ^ a * (e / 4) ^ b))) ≤
      e * (P * Q * 4 ^ b * (cc * e ^ 2 * L5)) := by
    rw [← mul_assoc, ← hej, h1]
    nlinarith [mul_nonneg he.le h2]
  exact le_of_mul_le_mul_left h3 he

/-- Rescaled `Z` term: `ε^j · ε P Q M / ((s/2)^a ε^b) ≤ ε P Q M` for `a + b = j`. -/
theorem p11_num_z {e s P Q M : ℝ} (he : 0 < e) (hs : 5 * e ≤ s) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hM : 0 ≤ M) (a b j : ℕ) (hj : a + b = j) :
    e ^ j * (e * (P * Q * M / ((s / 2) ^ a * e ^ b))) ≤ e * (P * Q * M) := by
  have hs0 : 0 < s := by linarith
  have h1 : e ^ j * (e * (P * Q * M / ((s / 2) ^ a * e ^ b))) =
      e * (P * Q * M) * (2 * e / s) ^ a := by
    rw [← hj]
    simp only [div_pow, mul_pow]
    have : (0 : ℝ) < s ^ a := by positivity
    field_simp
    ring
  rw [h1]
  have hx : (2 * e / s) ^ a ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one hs0).2 (by linarith))
  have : 0 ≤ e * (P * Q * M) := by positivity
  nlinarith

/-- Rescaled `Ĝ₀` term (pure `J`, order `a = j + 1`): `ε^j · ε P R / (s/4)^a ≤ P R (4ε/s)`. -/
theorem p11_num_a {e s P R : ℝ} (he : 0 < e) (hs : 0 < s) (hP : 0 ≤ P) (hR : 0 ≤ R)
    (hsmall : 4 * e / s ≤ 1) (a j : ℕ) (hj : a = j + 1) :
    e ^ j * (e * (P * R / (s / 4) ^ a)) ≤ P * R * (4 * e / s) := by
  have h1 : e ^ j * (e * (P * R / (s / 4) ^ a)) = P * R * (4 * e / s) ^ a := by
    rw [hj]
    simp only [div_pow, mul_pow]
    have : (0 : ℝ) < s ^ (j + 1) := by positivity
    field_simp
    ring
  rw [h1]
  have hx : (4 * e / s) ^ a ≤ 4 * e / s :=
    pow_le_of_le_one (by positivity) hsmall (by omega)
  have : 0 ≤ P * R := by positivity
  nlinarith

end Num

end KAM.Planetary

end
