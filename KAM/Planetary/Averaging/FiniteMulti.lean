/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Averaging.FiniteSetup

/-!
# P Part 2: the loss budget of the finite averaging iteration, `N` steps
(`stepP:p2:nfb-N`, `stepP:p2:nfb-ind`)

The schedule of Case A: a first step with losses `(r/8, s/6)` followed by `N` steps with losses
`(r/(8N), s/(4N))`, with the remainder bounds `ε₀ = E`, `εᵢ = (3E/(4κ)) 4^{1-i}`. This module proves
the closed forms of the radii, the weights of the star norm and the admissibility of every stage.
Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`, package P23-12.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

/-- The Case A schedule: `ρ₀ = r/8`, `σ₀ = s/6`, then `ρ = r/(8N)`, `σ = s/(4N)`. -/
def multiSched (r S s N : ℝ) : Sched :=
  ⟨r, S, fun i => if i = 0 then r / 8 else r / (8 * N),
    fun i => if i = 0 then s / 6 else s / (4 * N)⟩

section Closed

variable (r S s N : ℝ)

theorem multi_ρ_zero : (multiSched r S s N).ρ 0 = r / 8 := by simp [multiSched]

theorem multi_σ_zero : (multiSched r S s N).σ 0 = s / 6 := by simp [multiSched]

theorem multi_ρ_succ (l : ℕ) : (multiSched r S s N).ρ (l + 1) = r / (8 * N) := by
  simp [multiSched]

theorem multi_σ_succ (l : ℕ) : (multiSched r S s N).σ (l + 1) = s / (4 * N) := by
  simp [multiSched]

theorem multi_R_zero : (multiSched r S s N).R 0 = r := rfl

theorem multi_S_zero : (multiSched r S s N).S 0 = S := rfl

theorem multi_R_closed (l : ℕ) :
    (multiSched r S s N).R (l + 1) = 3 * r / 4 - 2 * l * (r / (8 * N)) := by
  induction l with
  | zero =>
    rw [Sched.R_succ, multi_R_zero, multi_ρ_zero]; push_cast; ring
  | succ l ih =>
    rw [Sched.R_succ, ih, multi_ρ_succ]; push_cast; ring

theorem multi_S_closed (l : ℕ) :
    (multiSched r S s N).S (l + 1) = S - s / 3 - 2 * l * (s / (4 * N)) := by
  induction l with
  | zero =>
    rw [Sched.S_succ, multi_S_zero, multi_σ_zero]; push_cast; ring
  | succ l ih =>
    rw [Sched.S_succ, ih, multi_σ_succ]; push_cast; ring

/-- The remainder bounds of Case A: `ε₀ = E`, `εᵢ = (3E/(4κ)) 4^{1-i}` for `i ≥ 1`. -/
def multiEps (E κ : ℝ) (i : ℕ) : ℝ := if i = 0 then E else 3 * E / (4 * κ) * (1 / 4) ^ (i - 1)

theorem multiEps_zero (E κ : ℝ) : multiEps E κ 0 = E := by simp [multiEps]

theorem multiEps_succ (E κ : ℝ) (l : ℕ) :
    multiEps E κ (l + 1) = 3 * E / (4 * κ) * (1 / 4) ^ l := by simp [multiEps]

theorem multiEps_nonneg {E κ : ℝ} (hE : 0 ≤ E) (hκ : 0 < κ) (i : ℕ) : 0 ≤ multiEps E κ i := by
  rcases i with _ | l
  · rw [multiEps_zero]; exact hE
  · rw [multiEps_succ]; positivity

theorem multi_weight_tail {ρ σ x y : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hx : 3 * ρ ≤ x)
    (hy : 3 * σ ≤ y) : 0 ≤ (1 / 2) * (ρ / x + σ / y) ∧ (1 / 2) * (ρ / x + σ / y) ≤ 1 / 3 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : ρ / x ≤ 1 / 3 := by rw [div_le_iff₀ hx0]; linarith
  have h2 : σ / y ≤ 1 / 3 := by rw [div_le_iff₀ hy0]; linarith
  have h1' : 0 ≤ ρ / x := by positivity
  have h2' : 0 ≤ σ / y := by positivity
  constructor <;> linarith

theorem multi_weight_head {ρ σ x y A B : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hA : 0 < A) (hB : 0 < B)
    (hx : A ≤ x) (hy : B ≤ y) :
    0 ≤ (1 / 2) * (ρ / x + σ / y) ∧ (1 / 2) * (ρ / x + σ / y) ≤ (1 / 2) * (ρ / A + σ / B) := by
  have hx0 : 0 < x := lt_of_lt_of_le hA hx
  have hy0 : 0 < y := lt_of_lt_of_le hB hy
  have h1 : ρ / x ≤ ρ / A := div_le_div_of_nonneg_left hρ.le hA hx
  have h2 : σ / y ≤ σ / B := div_le_div_of_nonneg_left hσ.le hB hy
  have h1' : 0 ≤ ρ / x := by positivity
  have h2' : 0 ≤ σ / y := by positivity
  constructor <;> linarith

/-- The star norm of stage `l + 1` is at most `E/(3κ) + 5E/(8N)`. -/
theorem multi_star {r S s N κ E : ℝ} (hr : 0 < r) (hs : 0 < s) (hN : 0 < N) (hκ : 0 < κ)
    (hE : 0 ≤ E) (l : ℕ) :
    let c := multiSched r S s N
    0 ≤ ∑ j : Fin (l + 1), (1 / 2) * (c.ρ (l + 1) / (c.R j - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S j - c.S (l + 1) + c.σ (l + 1))) * multiEps E κ j ∧
    ∑ j : Fin (l + 1), (1 / 2) * (c.ρ (l + 1) / (c.R j - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S j - c.S (l + 1) + c.σ (l + 1))) * multiEps E κ j ≤
      E / (3 * κ) + 5 * E / (8 * N) := by
  intro c
  have hρ : 0 < r / (8 * N) := by positivity
  have hσ : 0 < s / (4 * N) := by positivity
  rw [Fin.sum_univ_eq_sum_range (fun j => (1 / 2) * (c.ρ (l + 1) / (c.R j - c.R (l + 1) +
    c.ρ (l + 1)) + c.σ (l + 1) / (c.S j - c.S (l + 1) + c.σ (l + 1))) * multiEps E κ j) (l + 1),
    Finset.sum_range_succ']
  -- the terms `j + 1 ≤ l`
  have htail : ∀ j ∈ Finset.range l,
      0 ≤ (1 / 2) * (c.ρ (l + 1) / (c.R (j + 1) - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S (j + 1) - c.S (l + 1) + c.σ (l + 1))) * multiEps E κ (j + 1) ∧
      (1 / 2) * (c.ρ (l + 1) / (c.R (j + 1) - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S (j + 1) - c.S (l + 1) + c.σ (l + 1))) * multiEps E κ (j + 1) ≤
      (1 / 3) * (3 * E / (4 * κ) * (1 / 4) ^ j) := by
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
    have e0 : 0 ≤ multiEps E κ (j + 1) := multiEps_nonneg hE hκ _
    rw [multiEps_succ] at e0 ⊢
    exact ⟨mul_nonneg w0 e0, mul_le_mul_of_nonneg_right w1 e0⟩
  -- the term `j = 0`
  have hhead : 0 ≤ (1 / 2) * (c.ρ (l + 1) / (c.R 0 - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S 0 - c.S (l + 1) + c.σ (l + 1))) * multiEps E κ 0 ∧
      (1 / 2) * (c.ρ (l + 1) / (c.R 0 - c.R (l + 1) + c.ρ (l + 1)) +
        c.σ (l + 1) / (c.S 0 - c.S (l + 1) + c.σ (l + 1))) * multiEps E κ 0 ≤
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
    rw [multiEps_zero]
    refine ⟨mul_nonneg w0 hE, (mul_le_mul_of_nonneg_right w1 hE).trans (le_of_eq ?_)⟩
    rw [multi_ρ_succ, multi_σ_succ]
    field_simp
    ring
  refine ⟨add_nonneg (Finset.sum_nonneg fun j hj => (htail j hj).1) hhead.1, ?_⟩
  have hsum : ∑ j ∈ Finset.range l, (1 / 2) * (c.ρ (l + 1) / (c.R (j + 1) - c.R (l + 1) +
      c.ρ (l + 1)) + c.σ (l + 1) / (c.S (j + 1) - c.S (l + 1) + c.σ (l + 1))) *
        multiEps E κ (j + 1) ≤ ∑ j ∈ Finset.range l, (1 / 3) * (3 * E / (4 * κ) * (1 / 4) ^ j) :=
    Finset.sum_le_sum fun j hj => (htail j hj).2
  have hg : ∑ j ∈ Finset.range l, (1 / 3) * (3 * E / (4 * κ) * (1 / 4) ^ j) ≤
      (1 / 3) * (3 * E / (4 * κ)) * (4 / 3) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have := geom_quarter l
    have h0 : 0 ≤ (1 / 3) * (3 * E / (4 * κ)) := by positivity
    nlinarith
  have : (1 / 3) * (3 * E / (4 * κ)) * (4 / 3) = E / (3 * κ) := by field_simp
  linarith [hhead.2]

end Closed

section Estimates

variable {r s α₂ κ E N : ℝ}

/-- `E ≤ P/(1024 N)` where `P = 2π α₂ r s`. -/
theorem multi_E_N (hN : 1 ≤ N) (hNκ : 8 * N < κ)
    (hEP : E ≤ 2 * π * α₂ * r * s / (128 * κ)) (hP : 0 ≤ 2 * π * α₂ * r * s) :
    E ≤ 2 * π * α₂ * r * s / (1024 * N) := by
  refine hEP.trans ?_
  have hN0 : 0 < N := by linarith
  exact div_le_div_of_nonneg_left hP (by positivity) (by linarith)

/-- Every remainder bound of the later stages is below `Q/256`. -/
theorem multi_eps_Q (hr : 0 < r) (hs : 0 < s) (hα : 0 < α₂) (hκ : 0 < κ) (hE : 0 ≤ E)
    (hN : 1 ≤ N) (hNκ : 8 * N < κ) (hEP : E ≤ 2 * π * α₂ * r * s / (128 * κ)) (l : ℕ) :
    multiEps E κ (l + 1) ≤ 2 * π * α₂ * (r / (8 * N)) * (s / (4 * N)) / 256 := by
  have hN0 : 0 < N := by linarith
  have hπ := Real.pi_pos
  have hP : 0 ≤ 2 * π * α₂ * r * s := by positivity
  have hEN := multi_E_N hN hNκ hEP hP
  rw [multiEps_succ]
  have h1 : (1 / 4 : ℝ) ^ l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h0 : 0 ≤ 3 * E / (4 * κ) := by positivity
  have h2 : 3 * E / (4 * κ) * (1 / 4) ^ l ≤ 3 * E / (4 * κ) := by nlinarith
  have h3 : 3 * E / (4 * κ) ≤ 3 * E / (32 * N) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have h4 : 3 * E / (32 * N) ≤ 3 * (2 * π * α₂ * r * s / (1024 * N)) / (32 * N) := by
    gcongr
  have h5 : 3 * (2 * π * α₂ * r * s / (1024 * N)) / (32 * N) ≤
      2 * π * α₂ * (r / (8 * N)) * (s / (4 * N)) / 256 := by
    have : 2 * π * α₂ * (r / (8 * N)) * (s / (4 * N)) / 256 =
        2 * π * α₂ * r * s / (8192 * N ^ 2) := by field_simp; ring
    rw [this]
    have : 3 * (2 * π * α₂ * r * s / (1024 * N)) / (32 * N) =
        3 * (2 * π * α₂ * r * s) / (32768 * N ^ 2) := by field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hP (sq_nonneg N)]
  linarith

/-- The star norm of every later stage is below `Q/16`. -/
theorem multi_star_Q (hr : 0 < r) (hs : 0 < s) (hα : 0 < α₂) (_hκ : 0 < κ) (hE : 0 ≤ E)
    (hN : 1 ≤ N) (hNκ : 8 * N < κ) (hEP : E ≤ 2 * π * α₂ * r * s / (128 * κ)) :
    E / (3 * κ) + 5 * E / (8 * N) ≤ 2 * π * α₂ * (r / (8 * N)) * (s / (4 * N)) / 16 := by
  have hN0 : 0 < N := by linarith
  have hπ := Real.pi_pos
  have hP : 0 ≤ 2 * π * α₂ * r * s := by positivity
  have hEN := multi_E_N hN hNκ hEP hP
  have h1 : E / (3 * κ) ≤ E / (24 * N) :=
    div_le_div_of_nonneg_left hE (by positivity) (by linarith)
  have h2 : E / (24 * N) + 5 * E / (8 * N) = (2 / 3) * E / N := by field_simp; ring
  have h3 : (2 / 3) * E / N ≤ (2 / 3) * (2 * π * α₂ * r * s / (1024 * N)) / N := by gcongr
  have h4 : (2 / 3) * (2 * π * α₂ * r * s / (1024 * N)) / N ≤
      2 * π * α₂ * (r / (8 * N)) * (s / (4 * N)) / 16 := by
    have : 2 * π * α₂ * (r / (8 * N)) * (s / (4 * N)) / 16 =
        2 * π * α₂ * r * s / (512 * N ^ 2) := by field_simp; ring
    rw [this]
    have : (2 / 3) * (2 * π * α₂ * r * s / (1024 * N)) / N =
        (2 / 3) * (2 * π * α₂ * r * s) / (1024 * N ^ 2) := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hP (sq_nonneg N)]
  linarith

end Estimates

section Displacement

variable {a s κ E : ℝ} {n : ℕ}

/-- `∑_{i<n} ε_{i+1} ≤ E/κ`, and `n ε₁ ≤ 3E/32`. -/
theorem multi_tail_sum (hκ : 0 < κ) (hE : 0 ≤ E) :
    ∑ i ∈ Finset.range n, multiEps E κ (i + 1) ≤ 4 / 3 * (3 * E / (4 * κ)) := by
  have h0 : 0 ≤ 3 * E / (4 * κ) := by positivity
  have : ∑ i ∈ Finset.range n, multiEps E κ (i + 1) =
      3 * E / (4 * κ) * ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => multiEps_succ E κ i
  rw [this]
  have := geom_quarter n
  nlinarith

theorem multi_n_eps (hκ : 0 < κ) (hE : 0 ≤ E) (hnκ : 8 * (n : ℝ) ≤ κ) :
    (n : ℝ) * (3 * E / (4 * κ)) ≤ 3 * E / 32 := by
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The two action-displacement sums: `a s ∑ ε_i/(e a σ_i) ≤ 3E`. -/
theorem multi_disp_σ (ha : 0 < a) (hs : 0 < s) (hκ : 0 < κ) (hE : 0 ≤ E) (hn : 1 ≤ n)
    (hnκ : 8 * (n : ℝ) ≤ κ) (r S : ℝ) :
    a * s * ∑ i ∈ Finset.range (n + 1),
      1 * multiEps E κ i / (exp 1 * a * (multiSched r S s n).σ i) ≤ 3 * E := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.sum_range_succ']
  simp only [multi_σ_zero, multi_σ_succ, multiEps_zero]
  have hT := multi_tail_sum (n := n) hκ hE
  have hnc := multi_n_eps (n := n) hκ hE hnκ
  have hsum : ∑ i ∈ Finset.range n, 1 * multiEps E κ (i + 1) / (exp 1 * a * (s / (4 * n))) =
      (∑ i ∈ Finset.range n, multiEps E κ (i + 1)) / (exp 1 * a * (s / (4 * n))) := by
    rw [Finset.sum_div]; simp
  rw [hsum]
  set T := ∑ i ∈ Finset.range n, multiEps E κ (i + 1)
  have key : a * s * (T / (exp 1 * a * (s / (4 * n))) + 1 * E / (exp 1 * a * (s / 6))) =
      (4 * n * T + 6 * E) / exp 1 := by field_simp
  rw [key]
  have he := exp_one_gt_27
  rw [div_le_iff₀ (by linarith)]
  have : 4 * (n : ℝ) * T ≤ 4 * n * (4 / 3 * (3 * E / (4 * κ))) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  nlinarith

/-- The angle-displacement sum: `a r ∑ ε_i/(a ρ_i) ≤ 9E`. -/
theorem multi_disp_ρ {r : ℝ} (ha : 0 < a) (hr : 0 < r) (hκ : 0 < κ) (hE : 0 ≤ E) (hn : 1 ≤ n)
    (hnκ : 8 * (n : ℝ) ≤ κ) (S : ℝ) :
    a * r * ∑ i ∈ Finset.range (n + 1),
      1 * multiEps E κ i / (a * (multiSched r S s n).ρ i) ≤ 9 * E := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Finset.sum_range_succ']
  simp only [multi_ρ_zero, multi_ρ_succ, multiEps_zero]
  have hT := multi_tail_sum (n := n) hκ hE
  have hnc := multi_n_eps (n := n) hκ hE hnκ
  have hsum : ∑ i ∈ Finset.range n, 1 * multiEps E κ (i + 1) / (a * (r / (8 * n))) =
      (∑ i ∈ Finset.range n, multiEps E κ (i + 1)) / (a * (r / (8 * n))) := by
    rw [Finset.sum_div]; simp
  rw [hsum]
  set T := ∑ i ∈ Finset.range n, multiEps E κ (i + 1)
  have key : a * r * (T / (a * (r / (8 * n))) + 1 * E / (a * (r / 8))) = 8 * n * T + 8 * E := by
    field_simp
  rw [key]
  have : 8 * (n : ℝ) * T ≤ 8 * n * (4 / 3 * (3 * E / (4 * κ))) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  nlinarith

end Displacement

end KAM.Planetary

end
