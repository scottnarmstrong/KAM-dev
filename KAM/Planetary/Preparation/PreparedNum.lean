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

/-- Collecting the `Z` term. -/
theorem p11_num_z_final {e c k2 F PQ η lx : ℝ} (he : 0 < e) (hc : 0 ≤ c) (hη0 : 0 ≤ η)
    (hlx : 1 ≤ lx) (hPQ0 : 0 ≤ PQ) (hPQ : PQ ≤ F) (hη : η ≤ k2 * e * lx) :
    e * (PQ * (c * (e + η))) ≤ F * (c * (1 + k2) * e ^ 2 * lx) := by
  have hk2 : 0 ≤ k2 := by
    by_contra hk
    push Not at hk
    have : k2 * e * lx < 0 := by
      have : 0 < e * lx := by positivity
      nlinarith
    linarith
  have h1 : e + η ≤ (1 + k2) * e * lx := by nlinarith
  have h2 : 0 ≤ (1 + k2) * e * lx := by positivity
  have h3 : c * (e + η) ≤ c * ((1 + k2) * e * lx) := mul_le_mul_of_nonneg_left h1 hc
  have h4 : PQ * (c * (e + η)) ≤ F * (c * ((1 + k2) * e * lx)) := by
    have : 0 ≤ c * (e + η) := by positivity
    have : 0 ≤ c * ((1 + k2) * e * lx) := by positivity
    exact mul_le_mul hPQ h3 (by positivity) (hPQ0.trans hPQ)
  calc e * (PQ * (c * (e + η))) ≤ e * (F * (c * ((1 + k2) * e * lx))) :=
        mul_le_mul_of_nonneg_left h4 he.le
    _ = F * (c * (1 + k2) * e ^ 2 * lx) := by ring

/-- Final collection, pure `J` case. -/
theorem p11_num_collect_pure {e c K F a l1 l5 lQ T3 X : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hc : 0 ≤ c) (hF : 0 ≤ F) (hl1 : 0 ≤ l1) (hl5 : 0 ≤ l5) (h1 : l1 ≤ lQ)
    (h5 : l5 ≤ lQ) (haK : a ≤ K) (hFK : F ≤ K) (hX : X ≤ T3 + a * (e * l1) + F * (c * e ^ 2 * l5)) :
    X ≤ T3 + K * (1 + c) * e * lQ := by
  have hK : 0 ≤ K := hF.trans hFK
  have h2 : e ^ 2 ≤ e := by nlinarith
  have t1 : a * (e * l1) ≤ K * e * lQ := by
    have : 0 ≤ e := he.le
    calc a * (e * l1) ≤ K * (e * lQ) := mul_le_mul haK (mul_le_mul_of_nonneg_left h1 he.le)
          (by positivity) hK
      _ = K * e * lQ := by ring
  have t2 : F * (c * e ^ 2 * l5) ≤ K * c * e * lQ := by
    have h3 : c * e ^ 2 * l5 ≤ c * e * lQ := by
      have : 0 ≤ c := hc
      calc c * e ^ 2 * l5 ≤ c * e * l5 := by gcongr
        _ ≤ c * e * lQ := by gcongr
    calc F * (c * e ^ 2 * l5) ≤ K * (c * e * lQ) :=
          mul_le_mul hFK h3 (by positivity) hK
      _ = K * c * e * lQ := by ring
  calc X ≤ T3 + a * (e * l1) + F * (c * e ^ 2 * l5) := hX
    _ ≤ T3 + K * e * lQ + K * c * e * lQ := by linarith
    _ = T3 + K * (1 + c) * e * lQ := by ring

/-- Final collection, `ρ̃`-index case. -/
theorem p11_num_collect_rho {e c K F k2 M l2 l5 lQ T3 X m : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hc : 0 ≤ c) (hF : 0 ≤ F) (hk2 : 0 ≤ k2) (hM : 0 ≤ M) (hl2 : 0 ≤ l2) (hl5 : 0 ≤ l5)
    (h2 : l2 ≤ lQ) (h5 : l5 ≤ lQ) (hK : F * (1 + k2) + F * M ≤ K)
    (hX : X ≤ m + F * (c * (1 + k2) * e ^ 2 * l2) + F * M * (c * e ^ 2 * l5))
    (hm : m ≤ T3) : X ≤ T3 + K * (1 + c) * e * lQ := by
  have hK0 : 0 ≤ K := by
    have : 0 ≤ F * (1 + k2) + F * M := by positivity
    linarith
  have he2 : e ^ 2 ≤ e := by nlinarith
  have hlQ0 : 0 ≤ lQ := hl2.trans h2
  have t1 : F * (c * (1 + k2) * e ^ 2 * l2) ≤ F * (1 + k2) * c * e * lQ := by
    have h3 : c * (1 + k2) * e ^ 2 * l2 ≤ (1 + k2) * c * e * lQ := by
      calc c * (1 + k2) * e ^ 2 * l2 ≤ c * (1 + k2) * e * l2 := by gcongr
        _ ≤ c * (1 + k2) * e * lQ := by gcongr
        _ = (1 + k2) * c * e * lQ := by ring
    calc F * (c * (1 + k2) * e ^ 2 * l2) ≤ F * ((1 + k2) * c * e * lQ) :=
          mul_le_mul_of_nonneg_left h3 hF
      _ = F * (1 + k2) * c * e * lQ := by ring
  have t2 : F * M * (c * e ^ 2 * l5) ≤ F * M * c * e * lQ := by
    have h3 : c * e ^ 2 * l5 ≤ c * e * lQ := by
      calc c * e ^ 2 * l5 ≤ c * e * l5 := by gcongr
        _ ≤ c * e * lQ := by gcongr
    calc F * M * (c * e ^ 2 * l5) ≤ F * M * (c * e * lQ) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = F * M * c * e * lQ := by ring
  have t3 : (F * (1 + k2) + F * M) * c * e * lQ ≤ K * c * e * lQ := by gcongr
  calc X ≤ m + F * (c * (1 + k2) * e ^ 2 * l2) + F * M * (c * e ^ 2 * l5) := hX
    _ ≤ T3 + (F * (1 + k2) + F * M) * c * e * lQ := by nlinarith
    _ ≤ T3 + K * c * e * lQ := by linarith
    _ ≤ T3 + K * (1 + c) * e * lQ := by
        have hlQ0 : 0 ≤ lQ := hl2.trans h2
        have hh : 0 ≤ K * e * lQ := by positivity
        have : K * (1 + c) * e * lQ = K * e * lQ + K * c * e * lQ := by ring
        linarith

end Num

end KAM.Planetary

end
