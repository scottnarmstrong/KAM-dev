/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.FiniteMulti

/-!
# Rectangular averaging: the quadratic first-step bound (P11A-P4, `stepP:p11:aa-quad`)

The numerical inequalities of the finite averaging iteration with the first remainder bound
`ε₁ = E₁` an arbitrary number in `[0, 3E/(4κ)]` (the source takes `E₁ = 2 y₀ E`, `y₀ = E/Q`, which is
quadratic in `E`). The remainder bounds are `ε₀ = E`, `εᵢ = E₁ 4^{1-i}`; every estimate is the
corresponding one of `FiniteMulti` for the larger sequence `(3E/(4κ)) 4^{1-i}`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Planetary

/-- First step, case A with the quadratic bound: the remainder is at most `2 (E/Q) E`. -/
theorem p11_step_first_quad {Q E κ q : ℝ} (hQ : 0 < Q) (hE : 0 ≤ E) (hκ : 6 ≤ κ)
    (hy : E / Q ≤ 3 / (8 * κ)) (hq0 : 0 ≤ q) (hq : q ≤ E / Q) :
    (1 - 2 * (1 * E / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (0 + E) + q) * E ≤ 2 * (E / Q) * E := by
  set y := E / Q with hyd
  have hEy : E = y * Q := by rw [hyd]; field_simp
  have hy0 : 0 ≤ y := div_nonneg hE hQ.le
  have hy16 : y ≤ 1 / 16 := by
    refine hy.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h1 : (1 - 2 * (1 * E / Q))⁻¹ ≤ 8 / 7 := by
    rw [one_mul, ← hyd]
    refine (inv_one_sub_le hy16 (by norm_num)).trans ?_
    norm_num
  have h2 : 2 * 1 / (Real.exp 1 * Q) * (0 + E) = 2 * y / Real.exp 1 := by
    rw [hEy, zero_add]; field_simp
  have he := exp_one_gt_27
  have h3 : 2 * y / Real.exp 1 ≤ 3 / 4 * y := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h5 : (1 - 2 * (1 * E / Q))⁻¹ * (2 * 1 / (Real.exp 1 * Q) * (0 + E) + q) ≤
      8 / 7 * (7 / 4 * y) := by
    rw [h2]
    exact mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  exact mul_le_mul_of_nonneg_right (h5.trans (by linarith)) hE

/-- The remainder bounds `ε₀ = E`, `εᵢ = E₁ 4^{1-i}` of Case A with free first bound `E₁`. -/
def p11Eps (E E₁ : ℝ) (i : ℕ) : ℝ := if i = 0 then E else E₁ * (1 / 4) ^ (i - 1)

theorem p11Eps_zero (E E₁ : ℝ) : p11Eps E E₁ 0 = E := by simp [p11Eps]

theorem p11Eps_succ (E E₁ : ℝ) (l : ℕ) : p11Eps E E₁ (l + 1) = E₁ * (1 / 4) ^ l := by
  simp [p11Eps]

theorem p11Eps_nonneg {E E₁ : ℝ} (hE : 0 ≤ E) (hE₁ : 0 ≤ E₁) (i : ℕ) : 0 ≤ p11Eps E E₁ i := by
  rcases i with _ | l
  · rw [p11Eps_zero]; exact hE
  · rw [p11Eps_succ]; positivity

theorem p11Eps_le {E E₁ κ : ℝ} (h : E₁ ≤ 3 * E / (4 * κ)) (i : ℕ) :
    p11Eps E E₁ i ≤ multiEps E κ i := by
  rcases i with _ | l
  · rw [p11Eps_zero, multiEps_zero]
  · rw [p11Eps_succ, multiEps_succ]
    exact mul_le_mul_of_nonneg_right h (by positivity)

theorem p11_multi_star {r S s N κ E E₁ : ℝ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < N) (hκ : 0 < κ)
    (hE : 0 ≤ E) (hE₁ : 0 ≤ E₁) (hE₁κ : E₁ ≤ 3 * E / (4 * κ)) (l : ℕ) :
    let c := multiSched r S s N
    0 ≤ ∑ j : Fin (l + 1), (1 / 2) * (c.ρ (l + 1) / (c.R j - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S j - c.S (l + 1) + c.σ (l + 1))) * p11Eps E E₁ j ∧
    ∑ j : Fin (l + 1), (1 / 2) * (c.ρ (l + 1) / (c.R j - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S j - c.S (l + 1) + c.σ (l + 1))) * p11Eps E E₁ j ≤
      E / (3 * κ) + 5 * E / (8 * N) := by
  intro c
  have hρ : 0 < r / (8 * N) := by positivity
  have hσ : 0 < s / (4 * N) := by positivity
  rw [Fin.sum_univ_eq_sum_range (fun j => (1 / 2) * (c.ρ (l + 1) / (c.R j - c.R (l + 1) +
    c.ρ (l + 1)) + c.σ (l + 1) / (c.S j - c.S (l + 1) + c.σ (l + 1))) * p11Eps E E₁ j) (l + 1),
    Finset.sum_range_succ']
  have htail : ∀ j ∈ Finset.range l,
      0 ≤ (1 / 2) * (c.ρ (l + 1) / (c.R (j + 1) - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S (j + 1) - c.S (l + 1) + c.σ (l + 1))) * p11Eps E E₁ (j + 1) ∧
      (1 / 2) * (c.ρ (l + 1) / (c.R (j + 1) - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S (j + 1) - c.S (l + 1) + c.σ (l + 1))) * p11Eps E E₁ (j + 1) ≤
      (1 / 3) * (E₁ * (1 / 4) ^ j) := by
    intro j hj
    have hjl : (j : ℝ) + 1 ≤ l := by exact_mod_cast Finset.mem_range.1 hj
    have hx : 3 * c.ρ (l + 1) ≤ c.R (j + 1) - c.R (l + 1) + c.ρ (l + 1) := by
      rw [multi_ρ_succ, multi_R_closed, multi_R_closed]
      nlinarith
    have hy : 3 * c.σ (l + 1) ≤ c.S (j + 1) - c.S (l + 1) + c.σ (l + 1) := by
      rw [multi_σ_succ, multi_S_closed, multi_S_closed]
      nlinarith
    obtain ⟨w0, w1⟩ := multi_weight_tail (by rw [multi_ρ_succ]; exact hρ)
      (by rw [multi_σ_succ]; exact hσ) hx hy
    have e0 : 0 ≤ p11Eps E E₁ (j + 1) := p11Eps_nonneg hE hE₁ _
    rw [p11Eps_succ] at e0 ⊢
    exact ⟨mul_nonneg w0 e0, mul_le_mul_of_nonneg_right w1 e0⟩
  have hhead : 0 ≤ (1 / 2) * (c.ρ (l + 1) / (c.R 0 - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S 0 - c.S (l + 1) + c.σ (l + 1))) * p11Eps E E₁ 0 ∧
      (1 / 2) * (c.ρ (l + 1) / (c.R 0 - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S 0 - c.S (l + 1) + c.σ (l + 1))) * p11Eps E E₁ 0 ≤
      5 * E / (8 * N) := by
    have hx : r / 4 ≤ c.R 0 - c.R (l + 1) + c.ρ (l + 1) := by
      rw [multi_ρ_succ, multi_R_closed, multi_R_zero]
      have : 0 ≤ 2 * (l : ℝ) * (r / (8 * N)) := by positivity
      linarith
    have hy : s / 3 ≤ c.S 0 - c.S (l + 1) + c.σ (l + 1) := by
      rw [multi_σ_succ, multi_S_closed, multi_S_zero]
      have : 0 ≤ 2 * (l : ℝ) * (s / (4 * N)) := by positivity
      linarith
    have hρc : 0 < c.ρ (l + 1) := (multi_ρ_succ r S s N l).symm ▸ hρ
    have hσc : 0 < c.σ (l + 1) := (multi_σ_succ r S s N l).symm ▸ hσ
    obtain ⟨w0, w1⟩ := multi_weight_head hρc hσc (by positivity : 0 < r / 4)
      (by positivity : 0 < s / 3) hx hy
    rw [p11Eps_zero]
    refine ⟨mul_nonneg w0 hE, (mul_le_mul_of_nonneg_right w1 hE).trans (le_of_eq ?_)⟩
    rw [multi_ρ_succ, multi_σ_succ]
    field_simp
    ring
  refine ⟨add_nonneg (Finset.sum_nonneg fun j hj => (htail j hj).1) hhead.1, ?_⟩
  have hsum : ∑ j ∈ Finset.range l, (1 / 2) * (c.ρ (l + 1) / (c.R (j + 1) - c.R (l + 1) +
      c.ρ (l + 1)) + c.σ (l + 1) / (c.S (j + 1) - c.S (l + 1) + c.σ (l + 1))) *
        p11Eps E E₁ (j + 1) ≤ ∑ j ∈ Finset.range l, (1 / 3) * (E₁ * (1 / 4) ^ j) :=
    Finset.sum_le_sum fun j hj => (htail j hj).2
  have hg : ∑ j ∈ Finset.range l, (1 / 3) * (E₁ * (1 / 4) ^ j) ≤ (1 / 3) * E₁ * (4 / 3) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have := geom_quarter l
    have h0 : 0 ≤ (1 / 3) * E₁ := by positivity
    nlinarith
  have h4 : (1 / 3) * E₁ * (4 / 3) ≤ E / (3 * κ) := by
    have : (1 / 3) * (3 * E / (4 * κ)) * (4 / 3) = E / (3 * κ) := by field_simp
    rw [← this]
    have h0 : 0 ≤ (4 / 3 : ℝ) := by norm_num
    nlinarith
  linarith [hhead.2]

/-- `∑_{i<n} εᵢ₊₁ ≤ (4/3) E₁`. -/
theorem p11_multi_tail_sum {E E₁ : ℝ} (hE₁ : 0 ≤ E₁) (n : ℕ) :
    ∑ i ∈ Finset.range n, p11Eps E E₁ (i + 1) ≤ 4 / 3 * E₁ := by
  have : ∑ i ∈ Finset.range n, p11Eps E E₁ (i + 1) =
      E₁ * ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => p11Eps_succ E E₁ i
  rw [this]
  have := geom_quarter n
  nlinarith

section Displacement

variable {a s κ E E₁ : ℝ} {n : ℕ}

/-- The action-displacement sums of `multi_disp_σ` for the smaller sequence. -/
theorem p11_multi_disp_σ (ha : 0 < a) (hs : 0 < s) (hE : 0 ≤ E) (hE₁ : 0 ≤ E₁)
    (hE₁κ : E₁ ≤ 3 * E / (4 * κ)) (hn : 1 ≤ n) (hnκ : 8 * (n : ℝ) ≤ κ) (r S : ℝ)
    (hκ : 0 < κ) :
    a * s * ∑ i ∈ Finset.range (n + 1),
      1 * p11Eps E E₁ i / (exp 1 * a * (multiSched r S s n).σ i) ≤ 3 * E := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity))
    (multi_disp_σ ha hs hκ hE hn hnκ r S)
  have hσ : 0 < (multiSched r S s n).σ i := by
    rcases i with _ | l
    · rw [multi_σ_zero]; positivity
    · rw [multi_σ_succ]; positivity
  have hle := p11Eps_le hE₁κ i
  rw [one_mul, one_mul]
  exact div_le_div_of_nonneg_right hle (by positivity)

/-- The angle-displacement sum of `multi_disp_ρ` for the smaller sequence. -/
theorem p11_multi_disp_ρ {r : ℝ} (ha : 0 < a) (hr : 0 < r) (hE : 0 ≤ E) (hE₁ : 0 ≤ E₁)
    (hE₁κ : E₁ ≤ 3 * E / (4 * κ)) (hn : 1 ≤ n) (hnκ : 8 * (n : ℝ) ≤ κ) (S : ℝ)
    (hκ : 0 < κ) :
    a * r * ∑ i ∈ Finset.range (n + 1),
      1 * p11Eps E E₁ i / (a * (multiSched r S s n).ρ i) ≤ 9 * E := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity))
    (multi_disp_ρ (s := s) ha hr hκ hE hn hnκ S)
  have hρ : 0 < (multiSched r S s n).ρ i := by
    rcases i with _ | l
    · rw [multi_ρ_zero]; positivity
    · rw [multi_ρ_succ]; positivity
  have hle := p11Eps_le hE₁κ i
  rw [one_mul, one_mul]
  exact div_le_div_of_nonneg_right hle (by positivity)

end Displacement

end KAM.Planetary

end
