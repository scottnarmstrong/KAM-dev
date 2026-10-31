/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Coords
public import KAM.Wave.Measure.Lambda

/-!
# W7: unperturbed separation and asymptotics (blueprint `bpW:w7:unpert-bounds`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

For `‖ξ‖ ≤ 1/2`: `|s| ≤ 1`, `|ω⁰| ≤ λ₂ + 3/10` (i); normal separation
`|⟨l, Ω⁰⟩| ≥ 3 β_* ⟨l⟩` on `Λ` (ii); the `κ = 2` asymptotics (iii); and the Lipschitz bound of
`⟨l, Ω⁰⟩` in the frequency coordinate (iv).
-/

@[expose] public noncomputable section

open Real Finsupp

namespace KAM.Wave

/-- `β_* = 1 / (2 √(9 + m))` (blueprint `bpW:w7:constdef` (C2)). -/
def measBetaStar (m : ℝ) : ℝ := 1 / (2 * Real.sqrt (9 + m))

/-- `a_κ = m/2 + 1` (blueprint `bpW:w7:constdef` (C2)). -/
def measAKappa (m : ℝ) : ℝ := m / 2 + 1

theorem measBetaStar_pos {m : ℝ} (hm : 0 < m) : 0 < measBetaStar m := by
  unfold measBetaStar
  have : 0 < Real.sqrt (9 + m) := Real.sqrt_pos.2 (by linarith)
  positivity

theorem measBetaStar_le {m : ℝ} (hm : 0 < m) : 3 * measBetaStar m ≤ 1 / 2 := by
  unfold measBetaStar
  have h : 3 ≤ Real.sqrt (9 + m) := by
    rw [show (3 : ℝ) = Real.sqrt 9 by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem measAKappa_pos {m : ℝ} (hm : 0 < m) : 0 < measAKappa m := by
  unfold measAKappa; linarith

section

variable (m : ℝ) (hm : 0 < m)

/-- `|s| ≤ 1` for `‖ξ‖ ≤ 1/2` (blueprint `bpW:w7:unpert-bounds` (i)). -/
theorem abs_measS_le {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2) : |measS m hm ξ| ≤ 1 := by
  obtain ⟨g0, g01, g1⟩ := measLam_facts m hm
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  have hpi := Real.pi_gt_three
  have a0 : |ξ 0| ≤ 1 / 2 := by have := norm_le_pi_norm ξ 0; simp at this; linarith
  have a1 : |ξ 1| ≤ 1 / 2 := by have := norm_le_pi_norm ξ 1; simp at this; linarith
  rw [measS_eq]
  have b0 : |ξ 0 / lamTan m hm 0| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0]; nlinarith [abs_nonneg (ξ 0)]
  have b1 : |ξ 1 / lamTan m hm 1| ≤ 1 / 4 := by
    rw [abs_div, abs_of_pos hl1, div_le_iff₀ hl1]; nlinarith [abs_nonneg (ξ 1)]
  rw [abs_mul, abs_of_pos (by positivity : 0 < 21 / (8 * π))]
  have : |ξ 0 / lamTan m hm 0 + ξ 1 / lamTan m hm 1| ≤ 3 / 4 :=
    (abs_add_le _ _).trans (by linarith)
  calc 21 / (8 * π) * _ ≤ 21 / (8 * π) * (3 / 4) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith

/-- `|ω⁰(ξ)|_∞ ≤ λ₂ + 3/10` (blueprint `bpW:w7:unpert-bounds` (i)). -/
theorem norm_omegaTan_le {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2) :
    ‖omegaTan m hm ξ‖ ≤ lamTan m hm 1 + 3 / 10 := by
  obtain ⟨g0, g01, g1⟩ := measLam_facts m hm
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  have hNA := measNA_lt m hm
  have h := norm_omegaTan_sub_le m hm ξ 0
  have e0 : omegaTan m hm 0 = fun i => lamTan m hm i := by
    funext i; simp [omegaTan]
  rw [e0, sub_zero] at h
  have hn : ‖omegaTan m hm ξ - fun i => lamTan m hm i‖ ≤ 3 / 10 := by
    refine h.trans ?_
    have := measNA_pos m hm
    nlinarith
  rw [pi_norm_le_iff_of_nonneg (by linarith)]
  intro i
  have hi : |(omegaTan m hm ξ - fun i => lamTan m hm i) i| ≤ 3 / 10 := by
    have := norm_le_pi_norm (omegaTan m hm ξ - fun i => lamTan m hm i) i
    simp only [Real.norm_eq_abs] at this ⊢
    linarith
  simp only [Pi.sub_apply] at hi
  rw [Real.norm_eq_abs]
  have hli : lamTan m hm i ≤ lamTan m hm 1 := by fin_cases i <;> simp only [Fin.zero_eta,
                                                   Fin.isValue, Fin.mk_one] <;> linarith
  have := abs_le.1 hi
  rw [abs_le]
  constructor <;> linarith [lamTan_pos m hm i]

/-! ### Normal frequencies -/

theorem lamN_le_mul (ν : ℕ) : lamN m hm ν ≤ normLab ν * (Real.sqrt (9 + m) / 3) := by
  have h3 := normLab_ge ν
  have hsq := lamN_sq m hm ν
  have hpos : 0 ≤ lamN m hm ν := Real.sqrt_nonneg _
  have hs : 0 ≤ Real.sqrt (9 + m) := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 9 + m by linarith)
  apply le_of_sq_le_sq _ (by positivity)
  have : lamN m hm ν ^ 2 = normLab ν ^ 2 + m := by rw [hsq]; unfold normLab; ring
  rw [this, mul_pow, div_pow, hs2]
  have h9 : 9 ≤ normLab ν ^ 2 := by nlinarith
  nlinarith [mul_nonneg hm.le (sub_nonneg.2 h9)]

theorem lt_lamN (ν : ℕ) : normLab ν < lamN m hm ν := by
  have h3 := normLab_ge ν
  have hsq := lamN_sq m hm ν
  have hpos : 0 ≤ lamN m hm ν := Real.sqrt_nonneg _
  have : lamN m hm ν ^ 2 = normLab ν ^ 2 + m := by rw [hsq]; unfold normLab; ring
  nlinarith

theorem lamN_sq' (ν : ℕ) : lamN m hm ν ^ 2 = normLab ν ^ 2 + m := by
  rw [lamN_sq]; unfold normLab; ring

theorem lamN_sub_eq {i j : ℕ} :
    lamN m hm i - lamN m hm j =
      (normLab i - normLab j) * (normLab i + normLab j) / (lamN m hm i + lamN m hm j) := by
  have hi := lt_lamN m hm i
  have hj := lt_lamN m hm j
  have h3 := normLab_ge i
  have h3j := normLab_ge j
  rw [eq_div_iff (by linarith)]
  have := lamN_sq' m hm i
  have := lamN_sq' m hm j
  nlinarith

theorem lamN_sub_le {i j : ℕ} (hji : j < i) : lamN m hm i - lamN m hm j ≤ normLab i - normLab j :=
    by
  have hi := lt_lamN m hm i
  have hj := lt_lamN m hm j
  have hd : normLab j < normLab i := by
    unfold normLab
    have : (j : ℝ) < i := by exact_mod_cast hji
    linarith
  have := normLab_ge j
  rw [lamN_sub_eq, div_le_iff₀ (by linarith)]
  nlinarith

theorem lamN_sub_ge {i j : ℕ} (hji : j < i) :
    (normLab i - normLab j) * (3 / Real.sqrt (9 + m)) ≤ lamN m hm i - lamN m hm j := by
  have hi := lamN_le_mul m hm i
  have hj := lamN_le_mul m hm j
  have hs : 0 < Real.sqrt (9 + m) := Real.sqrt_pos.2 (by linarith)
  have hli := lt_lamN m hm i
  have hlj := lt_lamN m hm j
  have h3 := normLab_ge i
  have h3j := normLab_ge j
  have hd : normLab j < normLab i := by
    unfold normLab
    have : (j : ℝ) < i := by exact_mod_cast hji
    linarith
  rw [lamN_sub_eq, le_div_iff₀ (by linarith)]
  have hsum : lamN m hm i + lamN m hm j ≤ (normLab i + normLab j) * (Real.sqrt (9 + m) / 3) := by
    nlinarith
  have : (normLab i - normLab j) * (3 / Real.sqrt (9 + m)) * (lamN m hm i + lamN m hm j) ≤
      (normLab i - normLab j) * (3 / Real.sqrt (9 + m)) *
        ((normLab i + normLab j) * (Real.sqrt (9 + m) / 3)) :=
    mul_le_mul_of_nonneg_left hsum (by
      have : 0 ≤ normLab i - normLab j := by linarith
      positivity)
  refine this.trans (le_of_eq ?_)
  field_simp

/-- Lower bound for the unperturbed normal frequency: `Ω⁰_ν ≥ (8/9) j`. -/
theorem omegaNor_ge {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2) (ν : ℕ) :
    8 / 9 * normLab ν ≤ omegaNor m hm ξ ν := by
  rw [omegaNor_eq]
  have hs := abs_measS_le m hm hξ
  have h3 := normLab_ge ν
  have hl := lt_lamN m hm ν
  have hpos : 0 < lamN m hm ν := by linarith
  have : |4 / (7 * lamN m hm ν) * measS m hm ξ| ≤ 4 / 21 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 4 / (7 * lamN m hm ν) * |measS m hm ξ| ≤ 4 / (7 * lamN m hm ν) * 1 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 4 / 21 := by
          rw [mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have := (abs_le.1 this).1
  linarith

theorem omegaNor_sub_ge {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2) {i j : ℕ} (hji : j < i) :
    3 * measBetaStar m * (normLab i - normLab j) ≤ omegaNor m hm ξ i - omegaNor m hm ξ j := by
  have hs := abs_measS_le m hm hξ
  have hli := lt_lamN m hm i
  have hlj := lt_lamN m hm j
  have h3i := normLab_ge i
  have h3j := normLab_ge j
  have hd : normLab j + 1 ≤ normLab i := by
    unfold normLab
    have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
    linarith
  have hi4 : 4 ≤ normLab i := by linarith
  have hpi : 0 < lamN m hm i := by linarith
  have hpj : 0 < lamN m hm j := by linarith
  have hprod : 12 ≤ lamN m hm i * lamN m hm j := by nlinarith
  have key : omegaNor m hm ξ i - omegaNor m hm ξ j =
      (lamN m hm i - lamN m hm j) *
        (1 - 4 * measS m hm ξ / (7 * (lamN m hm i * lamN m hm j))) := by
    have hi0 : lamN m hm i ≠ 0 := hpi.ne'
    have hj0 : lamN m hm j ≠ 0 := hpj.ne'
    rw [omegaNor_eq, omegaNor_eq]
    field_simp
    ring
  have hfac : 1 - 4 * measS m hm ξ / (7 * (lamN m hm i * lamN m hm j)) ≥ 1 / 2 := by
    have : |4 * measS m hm ξ / (7 * (lamN m hm i * lamN m hm j))| ≤ 1 / 21 := by
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_pos (by positivity : 0 < 7 * (lamN m hm i * lamN m hm j))]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg (measS m hm ξ)]
    have := (abs_le.1 this).2
    linarith
  have hsq : 0 < Real.sqrt (9 + m) := Real.sqrt_pos.2 (by linarith)
  have hg := lamN_sub_ge m hm hji
  have hge0 : 0 ≤ lamN m hm i - lamN m hm j := by
    have := lamN_sub_ge m hm hji
    have : 0 ≤ (normLab i - normLab j) * (3 / Real.sqrt (9 + m)) := by
      have : 0 ≤ normLab i - normLab j := by linarith
      positivity
    linarith
  rw [key]
  calc 3 * measBetaStar m * (normLab i - normLab j)
      = (normLab i - normLab j) * (3 / Real.sqrt (9 + m)) * (1 / 2) := by
        unfold measBetaStar; field_simp
    _ ≤ (lamN m hm i - lamN m hm j) * (1 / 2) := by gcongr
    _ ≤ _ := by gcongr

/-- The `κ = 2` asymptotics (blueprint `bpW:w7:unpert-bounds` (iii)). -/
theorem omegaNor_sub_approx {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2) {i j : ℕ} (hji : j < i) :
    |omegaNor m hm ξ i - omegaNor m hm ξ j - (normLab i - normLab j)| ≤
      measAKappa m * (normLab i - normLab j) / normLab j ^ 2 := by
  have hs := abs_measS_le m hm hξ
  have hli := lt_lamN m hm i
  have hlj := lt_lamN m hm j
  have h3i := normLab_ge i
  have h3j := normLab_ge j
  have hd : normLab j + 1 ≤ normLab i := by
    unfold normLab
    have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
    linarith
  have hpi : 0 < lamN m hm i := by linarith
  have hpj : 0 < lamN m hm j := by linarith
  set n := normLab i - normLab j with hn
  have hn0 : 0 < n := by linarith
  have hDsub := lamN_sub_le m hm hji
  have hDsub0 : 0 ≤ lamN m hm i - lamN m hm j := by
    have := lamN_sub_ge m hm hji
    have hsq : 0 < Real.sqrt (9 + m) := Real.sqrt_pos.2 (by linarith)
    have : 0 ≤ (normLab i - normLab j) * (3 / Real.sqrt (9 + m)) := by positivity
    linarith
  -- decomposition
  have e1 : omegaNor m hm ξ i - omegaNor m hm ξ j - n =
      (m / (lamN m hm i + normLab i) - m / (lamN m hm j + normLab j))
        + (-(4 * measS m hm ξ / 7)) * ((lamN m hm i - lamN m hm j) /
          (lamN m hm i * lamN m hm j)) := by
    have hi' : lamN m hm i - normLab i = m / (lamN m hm i + normLab i) := by
      rw [eq_div_iff (by linarith)]; nlinarith [lamN_sq' m hm i]
    have hj' : lamN m hm j - normLab j = m / (lamN m hm j + normLab j) := by
      rw [eq_div_iff (by linarith)]; nlinarith [lamN_sq' m hm j]
    have hi0 : lamN m hm i ≠ 0 := hpi.ne'
    have hj0 : lamN m hm j ≠ 0 := hpj.ne'
    rw [omegaNor_eq, omegaNor_eq, hn]
    rw [← hi', ← hj']
    field_simp
    ring
  rw [e1]
  have t1 : |m / (lamN m hm i + normLab i) - m / (lamN m hm j + normLab j)| ≤
      m * n / (2 * normLab j ^ 2) := by
    have hA : 0 < lamN m hm i + normLab i := by linarith
    have hB : 0 < lamN m hm j + normLab j := by linarith
    have : m / (lamN m hm i + normLab i) - m / (lamN m hm j + normLab j) =
        -(m * ((lamN m hm i + normLab i) - (lamN m hm j + normLab j)) /
          ((lamN m hm i + normLab i) * (lamN m hm j + normLab j))) := by
      field_simp; ring
    rw [this, abs_neg, abs_of_nonneg (by
      have : 0 ≤ (lamN m hm i + normLab i) - (lamN m hm j + normLab j) := by linarith
      positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (lamN m hm i + normLab i) - (lamN m hm j + normLab j) ≤ 2 * n := by
      rw [hn]; linarith
    have h2 : 4 * normLab i * normLab j ≤ (lamN m hm i + normLab i) * (lamN m hm j + normLab j) :=
        by
      nlinarith
    have h4 : normLab j ≤ normLab i := by linarith
    -- m * D * (2 j²) ≤ m n * (A B)
    have hmpos : 0 < m := hm
    calc m * ((lamN m hm i + normLab i) - (lamN m hm j + normLab j)) * (2 * normLab j ^ 2)
        ≤ m * (2 * n) * (2 * normLab j ^ 2) := by gcongr
      _ = m * n * (4 * normLab j * normLab j) := by ring
      _ ≤ m * n * (4 * normLab i * normLab j) := by gcongr
      _ ≤ m * n * ((lamN m hm i + normLab i) * (lamN m hm j + normLab j)) := by gcongr
  have t2 : |(-(4 * measS m hm ξ / 7)) * ((lamN m hm i - lamN m hm j) /
      (lamN m hm i * lamN m hm j))| ≤ n / normLab j ^ 2 := by
    rw [abs_mul, abs_neg, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 7),
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_nonneg (div_nonneg hDsub0 (by positivity))]
    have h1 : (lamN m hm i - lamN m hm j) / (lamN m hm i * lamN m hm j) ≤ n / normLab j ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : normLab j ^ 2 ≤ lamN m hm i * lamN m hm j := by nlinarith
      calc (lamN m hm i - lamN m hm j) * normLab j ^ 2
          ≤ n * normLab j ^ 2 := by gcongr
        _ ≤ n * (lamN m hm i * lamN m hm j) := by gcongr
    have h2 : 4 * |measS m hm ξ| / 7 ≤ 1 := by linarith
    calc 4 * |measS m hm ξ| / 7 * ((lamN m hm i - lamN m hm j) / (lamN m hm i * lamN m hm j))
        ≤ 1 * (n / normLab j ^ 2) := by
          apply mul_le_mul h2 h1 (div_nonneg hDsub0 (by positivity)) (by norm_num)
      _ = n / normLab j ^ 2 := one_mul _
  calc _ ≤ |(m / (lamN m hm i + normLab i) - m / (lamN m hm j + normLab j))| +
        |(-(4 * measS m hm ξ / 7)) * ((lamN m hm i - lamN m hm j) /
          (lamN m hm i * lamN m hm j))| := abs_add_le _ _
    _ ≤ m * n / (2 * normLab j ^ 2) + n / normLab j ^ 2 := by
        linarith
    _ = measAKappa m * n / normLab j ^ 2 := by
        unfold measAKappa
        have : normLab j ≠ 0 := (normLab_pos j).ne'
        field_simp

/-- Lipschitz bound of `⟨l, Ω⁰⟩` in the frequency coordinate (blueprint `bpW:w7:unpert-bounds`
(iv)). -/
theorem abs_linF_omegaNor_sub_le (l : ℕ →₀ ℤ) (ξ ξ' : Fin 2 → ℝ) :
    |linF l (omegaNor m hm ξ) - linF l (omegaNor m hm ξ')| ≤
      4 / 7 * (lamTan m hm 0 + lamTan m hm 1) * absWt l (-1) *
        ‖omegaTan m hm ξ - omegaTan m hm ξ'‖ := by
  have hfun : ∀ ζ : Fin 2 → ℝ, omegaNor m hm ζ =
      fun ν => lamN m hm ν + (4 / 7 * measS m hm ζ) * (1 / lamN m hm ν) := by
    intro ζ; funext ν
    have : lamN m hm ν ≠ 0 := by linarith [lt_lamN m hm ν, normLab_ge ν]
    rw [omegaNor_eq]; field_simp
  rw [hfun ξ, hfun ξ', linF_add_mul, linF_add_mul]
  have e : linF l (lamN m hm) + 4 / 7 * measS m hm ξ * linF l (fun ν => 1 / lamN m hm ν) -
      (linF l (lamN m hm) + 4 / 7 * measS m hm ξ' * linF l (fun ν => 1 / lamN m hm ν)) =
      4 / 7 * (measS m hm ξ - measS m hm ξ') * linF l (fun ν => 1 / lamN m hm ν) := by ring
  rw [e]
  have hlin : |linF l (fun ν => 1 / lamN m hm ν)| ≤ absWt l (-1) := by
    unfold linF absWt Finsupp.sum
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hl := lt_lamN m hm ν
    have h3 := normLab_ge ν
    rw [Real.rpow_neg_one, abs_of_pos (by apply one_div_pos.2; linarith)]
    show 1 / lamN m hm ν ≤ _
    rw [one_div]
    exact inv_anti₀ (by linarith) hl.le
  have hs := abs_measS_sub_le m hm ξ ξ'
  have hw := absWt_nonneg l (-1)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 7)]
  have hnn := norm_nonneg (omegaTan m hm ξ - omegaTan m hm ξ')
  have hl0 := lamTan_pos m hm 0
  have hl1 := lamTan_pos m hm 1
  calc 4 / 7 * |measS m hm ξ - measS m hm ξ'| * |linF l fun ν => 1 / lamN m hm ν|
      ≤ 4 / 7 * ((lamTan m hm 0 + lamTan m hm 1) *
          ‖omegaTan m hm ξ - omegaTan m hm ξ'‖) * absWt l (-1) := by
        gcongr
    _ = _ := by ring

/-- Normal separation (blueprint `bpW:w7:unpert-bounds` (ii)). -/
theorem three_betaStar_japL_le {ξ : Fin 2 → ℝ} (hξ : ‖ξ‖ ≤ 1 / 2) {l : ℕ →₀ ℤ}
    (hl : IsLam l) : 3 * measBetaStar m * japL l ≤ |linF l (omegaNor m hm ξ)| := by
  have hb := measBetaStar_le hm
  have hb0 := measBetaStar_pos hm
  have lo := omegaNor_ge m hm hξ
  rcases lam_cases l hl with ⟨a, σ, hσ, rfl⟩ | ⟨a, b, σ, hab, hσ, rfl⟩ | hmn
  · rw [japL_single a hσ, linF_single, abs_mul]
    have h3 := normLab_ge a
    have := lo a
    have : |(σ : ℝ)| ≥ 1 := by rcases hσ with rfl | rfl | rfl | rfl <;> norm_num
    rw [abs_of_pos (by linarith [normLab_pos a] : 0 < omegaNor m hm ξ a)]
    have t0 : 0 ≤ |(σ : ℝ)| * normLab a := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (lo a) (abs_nonneg (σ : ℝ)),
      mul_le_mul_of_nonneg_right hb t0]
  · rw [japL_pair hab.ne hσ, linF_pair hab.ne]
    have := lo a
    have := lo b
    have h3 := normLab_ge a
    have h4 := normLab_ge b
    rw [← mul_add, abs_mul, abs_of_pos (by linarith : 0 < omegaNor m hm ξ a + omegaNor m hm ξ b)]
    have : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [this, one_mul]
    nlinarith
  · obtain ⟨i, j, σ, hji, hσ, rfl⟩ := hmn
    rw [japL_minus hji hσ, linF_minus hji, abs_mul]
    have hd : (i : ℝ) - j = normLab i - normLab j := by unfold normLab; ring
    have := omegaNor_sub_ge m hm hξ hji
    have h1 : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [h1, one_mul, abs_of_nonneg (by
      have : 0 ≤ 3 * measBetaStar m * (normLab i - normLab j) := by
        have : 0 ≤ normLab i - normLab j := by
          unfold normLab
          have : (j : ℝ) < i := by exact_mod_cast hji
          linarith
        positivity
      linarith), hd]
    exact this

end

end KAM.Wave

end
