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

/-- Rescaled `g₂` term: `ε^j · P Q c ε³ L / ((s/4)^a (ε/4)^b) ≤ P Q 4^b c ε² L`
for `a + b = j + 1`. -/
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

theorem p11_num_powl {Λ l a : ℝ} (hΛ : 1 ≤ Λ) (hl : 1 ≤ l) (ha : 0 ≤ a) (s mu : ℕ)
    (hs : s ≤ mu) :
    (Λ * l ^ a) ^ s ≤ Λ ^ mu * l ^ (a * (mu : ℝ)) := by
  have hl0 : 0 < l := by linarith
  rw [mul_pow, ← Real.rpow_natCast (l ^ a) s, ← Real.rpow_mul hl0.le]
  have h1 : Λ ^ s ≤ Λ ^ mu := pow_le_pow_right₀ hΛ hs
  have h2 : l ^ (a * (s : ℝ)) ≤ l ^ (a * (mu : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hl (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) ha)
  have h3 : 0 ≤ l ^ (a * (s : ℝ)) := Real.rpow_nonneg hl0.le _
  exact mul_le_mul h1 h2 h3 (by positivity)

/-- `ℓ^x ℓ^y ≤ ℓ^z` for `x + y ≤ z`. -/
theorem p11_num_rpow_mul_le {l x y z : ℝ} (hl : 1 ≤ l) (h : x + y ≤ z) :
    l ^ x * l ^ y ≤ l ^ z := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hl h

theorem p11_num_inv_pow {s0 : ℝ} (_hs0 : 0 < s0) (d : ℝ) (s : ℕ) :
    1 / (s0 / d) ^ s = (d / s0) ^ s := by
  rw [one_div, ← inv_pow, inv_div]

/-- Block 1 of step pr-c. -/
theorem p11_num_cl1 {e c l F Rc Λ τ P R s1 s2 : ℝ} {s M : ℕ} (he : 0 < e) (he1 : e ≤ 1)
    (hl : 1 ≤ l) (hc : 0 ≤ c) (hΛ : 1 ≤ Λ) (hτ : 0 ≤ τ) (hP : 0 ≤ P) (hPF : P ≤ F)
    (hR0 : 0 ≤ R) (hR : R ≤ Rc * l ^ (2 * τ + 1)) (hs1 : 0 < s1) (hs2 : 0 < s2)
    (h41 : 4 / s1 ≤ Λ * l ^ (τ + 1)) (h42 : 4 / s2 ≤ Λ * l ^ (τ + 1)) (hs : s ≤ M) :
    e * (P * R / (s1 / 4) ^ s) + P * (c * e ^ 3 * l ^ (5 * τ + 2)) / (s2 / 4) ^ s ≤
      F * Λ ^ M * (Rc + c) * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) := by
  have hl0 : 0 < l := by linarith
  have hF : 0 ≤ F := hP.trans hPF
  have hRc : 0 ≤ Rc := by
    by_contra h
    push Not at h
    have : Rc * l ^ (2 * τ + 1) < 0 := mul_neg_of_neg_of_pos h (Real.rpow_pos_of_pos hl0 _)
    linarith
  have hp1 := p11_num_powl hΛ hl (by linarith : 0 ≤ τ + 1) s M hs
  have hbase : (4 / s1) ^ s ≤ Λ ^ M * l ^ ((τ + 1) * (M : ℝ)) :=
    (pow_le_pow_left₀ (by positivity) h41 s).trans hp1
  have hbase2 : (4 / s2) ^ s ≤ Λ ^ M * l ^ ((τ + 1) * (M : ℝ)) :=
    (pow_le_pow_left₀ (by positivity) h42 s).trans hp1
  have hLM : 0 ≤ l ^ ((τ + 1) * (M : ℝ)) := Real.rpow_nonneg hl0.le _
  have hΛM : 0 ≤ Λ ^ M := by positivity
  have e1 : P * R / (s1 / 4) ^ s = P * R * (4 / s1) ^ s := by
    rw [div_eq_mul_one_div, p11_num_inv_pow hs1]
  have e2 : P * (c * e ^ 3 * l ^ (5 * τ + 2)) / (s2 / 4) ^ s =
      P * (c * e ^ 3 * l ^ (5 * τ + 2)) * (4 / s2) ^ s := by
    rw [div_eq_mul_one_div, p11_num_inv_pow hs2]
  rw [e1, e2]
  have hm1 : l ^ (2 * τ + 1) * l ^ ((τ + 1) * (M : ℝ)) ≤ l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ)) :=
    p11_num_rpow_mul_le hl (by linarith)
  have hm2 : l ^ (5 * τ + 2) * l ^ ((τ + 1) * (M : ℝ)) ≤ l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ)) :=
    p11_num_rpow_mul_le hl (le_refl _)
  have hL5 : 0 ≤ l ^ (5 * τ + 2) := Real.rpow_nonneg hl0.le _
  have t1 : e * (P * R * (4 / s1) ^ s) ≤
      F * Λ ^ M * Rc * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) := by
    have h1 : P * R * (4 / s1) ^ s ≤ F * (Rc * l ^ (2 * τ + 1)) *
        (Λ ^ M * l ^ ((τ + 1) * (M : ℝ))) :=
      mul_le_mul (mul_le_mul hPF hR hR0 hF) hbase (by positivity) (by positivity)
    have h2 : F * (Rc * l ^ (2 * τ + 1)) * (Λ ^ M * l ^ ((τ + 1) * (M : ℝ))) =
        F * Λ ^ M * Rc * (l ^ (2 * τ + 1) * l ^ ((τ + 1) * (M : ℝ))) := by ring
    have h3 : F * Λ ^ M * Rc * (l ^ (2 * τ + 1) * l ^ ((τ + 1) * (M : ℝ))) ≤
        F * Λ ^ M * Rc * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hm1 (by positivity)
    calc e * (P * R * (4 / s1) ^ s) ≤ e * (F * Λ ^ M * Rc * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) :=
          mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans h3)) he.le
      _ = _ := by ring
  have t2 : P * (c * e ^ 3 * l ^ (5 * τ + 2)) * (4 / s2) ^ s ≤
      F * Λ ^ M * c * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) := by
    have he3 : e ^ 3 ≤ e := by
      have : e ^ 3 = e * e ^ 2 := by ring
      rw [this]; nlinarith [pow_le_one₀ he.le he1 (n := 2)]
    have h1 : P * (c * e ^ 3 * l ^ (5 * τ + 2)) ≤ F * (c * e * l ^ (5 * τ + 2)) :=
      mul_le_mul hPF (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he3 hc) hL5)
        (by positivity) hF
    have h2 : P * (c * e ^ 3 * l ^ (5 * τ + 2)) * (4 / s2) ^ s ≤
        F * (c * e * l ^ (5 * τ + 2)) * (Λ ^ M * l ^ ((τ + 1) * (M : ℝ))) :=
      mul_le_mul h1 hbase2 (by positivity) (by positivity)
    have h3 : F * (c * e * l ^ (5 * τ + 2)) * (Λ ^ M * l ^ ((τ + 1) * (M : ℝ))) =
        F * Λ ^ M * c * e * (l ^ (5 * τ + 2) * l ^ ((τ + 1) * (M : ℝ))) := by ring
    have h4 : F * Λ ^ M * c * e * (l ^ (5 * τ + 2) * l ^ ((τ + 1) * (M : ℝ))) ≤
        F * Λ ^ M * c * e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hm2 (by positivity)
    calc _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := h4
      _ = _ := by ring
  calc _ ≤ F * Λ ^ M * Rc * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) +
        F * Λ ^ M * c * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) := add_le_add t1 t2
    _ = _ := by ring

/-- Block 2 of step pr-c. -/
theorem p11_num_cl2 {e c l F k2 Λ τ P η s2 : ℝ} {j M : ℕ} (he : 0 < e) (he1 : e ≤ 1)
    (hl : 1 ≤ l) (hc : 0 ≤ c) (hΛ : 1 ≤ Λ) (hτ : 0 ≤ τ) (hP : 0 ≤ P) (hPF : P ≤ F)
    (hη0 : 0 ≤ η) (hη : η ≤ k2 * e * l ^ (2 * τ + 1)) (hs2 : 0 < s2)
    (h42 : 4 / s2 ≤ Λ * l ^ (τ + 1)) (hj : j ≤ M) :
    P * (c * (e + η)) / (s2 / 2) ^ j +
        P * (c * e ^ 3 * l ^ (5 * τ + 2)) / ((s2 / 4) ^ j * (e / 4) ^ 1) / e ≤
      F * Λ ^ M * (c * (1 + k2) + 4 * c) * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) := by
  have hl0 : 0 < l := by linarith
  have hF : 0 ≤ F := hP.trans hPF
  have hk2 : 0 ≤ k2 := by
    by_contra h
    push Not at h
    have : k2 * e * l ^ (2 * τ + 1) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h he) (Real.rpow_pos_of_pos hl0 _)
    linarith
  have hp1 := p11_num_powl hΛ hl (by linarith : 0 ≤ τ + 1) j M hj
  have hbase2 : (4 / s2) ^ j ≤ Λ ^ M * l ^ ((τ + 1) * (M : ℝ)) :=
    (pow_le_pow_left₀ (by positivity) h42 j).trans hp1
  have hbase1 : (2 / s2) ^ j ≤ Λ ^ M * l ^ ((τ + 1) * (M : ℝ)) :=
    (pow_le_pow_left₀ (by positivity) (by
      have : 2 / s2 ≤ 4 / s2 := div_le_div_of_nonneg_right (by norm_num) hs2.le
      exact this) j).trans hbase2
  have hL5 : 0 ≤ l ^ (5 * τ + 2) := Real.rpow_nonneg hl0.le _
  have hLx : 1 ≤ l ^ (2 * τ + 1) := Real.one_le_rpow hl (by linarith)
  have hm1 : l ^ (2 * τ + 1) * l ^ ((τ + 1) * (M : ℝ)) ≤ l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ)) :=
    p11_num_rpow_mul_le hl (by linarith)
  have hm2 : l ^ (5 * τ + 2) * l ^ ((τ + 1) * (M : ℝ)) ≤ l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ)) :=
    p11_num_rpow_mul_le hl (le_refl _)
  have e1 : P * (c * (e + η)) / (s2 / 2) ^ j = P * (c * (e + η)) * (2 / s2) ^ j := by
    rw [div_eq_mul_one_div, p11_num_inv_pow hs2]
  have e2 : P * (c * e ^ 3 * l ^ (5 * τ + 2)) / ((s2 / 4) ^ j * (e / 4) ^ 1) / e =
      4 * (P * (c * e * l ^ (5 * τ + 2)) * (4 / s2) ^ j) := by
    have hs2j : 0 < s2 ^ j := by positivity
    simp only [div_pow, pow_one]
    field_simp
  rw [e1, e2]
  have hΛM : 0 ≤ Λ ^ M := by positivity
  have hLM : 0 ≤ l ^ ((τ + 1) * (M : ℝ)) := Real.rpow_nonneg hl0.le _
  have hee : e + η ≤ (1 + k2) * e * l ^ (2 * τ + 1) := by
    have : e ≤ e * l ^ (2 * τ + 1) := by nlinarith
    nlinarith
  have t1 : P * (c * (e + η)) * (2 / s2) ^ j ≤
      F * Λ ^ M * (c * (1 + k2)) * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) := by
    have h1 : P * (c * (e + η)) ≤ F * (c * ((1 + k2) * e * l ^ (2 * τ + 1))) :=
      mul_le_mul hPF (mul_le_mul_of_nonneg_left hee hc) (by positivity) hF
    have h2 : P * (c * (e + η)) * (2 / s2) ^ j ≤
        F * (c * ((1 + k2) * e * l ^ (2 * τ + 1))) * (Λ ^ M * l ^ ((τ + 1) * (M : ℝ))) :=
      mul_le_mul h1 hbase1 (by positivity) (by positivity)
    have h3 : F * (c * ((1 + k2) * e * l ^ (2 * τ + 1))) * (Λ ^ M * l ^ ((τ + 1) * (M : ℝ))) =
        F * Λ ^ M * (c * (1 + k2)) * e * (l ^ (2 * τ + 1) * l ^ ((τ + 1) * (M : ℝ))) := by ring
    have h4 : F * Λ ^ M * (c * (1 + k2)) * e * (l ^ (2 * τ + 1) * l ^ ((τ + 1) * (M : ℝ))) ≤
        F * Λ ^ M * (c * (1 + k2)) * e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hm1 (by positivity)
    calc _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := h4
      _ = _ := by ring
  have t2 : 4 * (P * (c * e * l ^ (5 * τ + 2)) * (4 / s2) ^ j) ≤
      F * Λ ^ M * (4 * c) * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) := by
    have h1 : P * (c * e * l ^ (5 * τ + 2)) ≤ F * (c * e * l ^ (5 * τ + 2)) :=
      mul_le_mul_of_nonneg_right hPF (by positivity)
    have h2 : P * (c * e * l ^ (5 * τ + 2)) * (4 / s2) ^ j ≤
        F * (c * e * l ^ (5 * τ + 2)) * (Λ ^ M * l ^ ((τ + 1) * (M : ℝ))) :=
      mul_le_mul h1 hbase2 (by positivity) (by positivity)
    have h3 : 4 * (F * (c * e * l ^ (5 * τ + 2)) * (Λ ^ M * l ^ ((τ + 1) * (M : ℝ)))) =
        F * Λ ^ M * (4 * c) * e * (l ^ (5 * τ + 2) * l ^ ((τ + 1) * (M : ℝ))) := by ring
    have h4 : F * Λ ^ M * (4 * c) * e * (l ^ (5 * τ + 2) * l ^ ((τ + 1) * (M : ℝ))) ≤
        F * Λ ^ M * (4 * c) * e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hm2 (by positivity)
    calc _ ≤ 4 * (F * (c * e * l ^ (5 * τ + 2)) * (Λ ^ M * l ^ ((τ + 1) * (M : ℝ)))) := by
          linarith
      _ = _ := h3
      _ ≤ _ := h4
      _ = _ := by ring
  calc _ ≤ F * Λ ^ M * (c * (1 + k2)) * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) +
        F * Λ ^ M * (4 * c) * (e * l ^ (5 * τ + 2 + (τ + 1) * (M : ℝ))) := add_le_add t1 t2
    _ = _ := by ring

end Num

end KAM.Planetary

end
