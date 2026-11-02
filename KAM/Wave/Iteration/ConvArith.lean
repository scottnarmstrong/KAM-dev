/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.IterArith
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# W6: the arithmetic of the convergence proof (blueprint `bpW:w6:convergence`)

Blueprint label `bpW:w6:convergence` (milestone W6): the parts of steps
`c-freq`, `c-op`, `c-cauchy` that concern only the sequences of `bpW:w6:sequences`, under the
smallness `ε₀ ≤ γ₀ α₀ σ₀^t`.

* step `c-freq`: `∑ 6π ε_ν ≤ 8π ε₀`, `∑ 6π ε_ν/λ_ν ≤ 64π ε₀/λ₀`, `∑ 3ε_ν ≤ 4ε₀`,
  `∑ 3ε_ν/λ_ν ≤ 16 ε₀/λ₀` (finite partial sums, all `n`);
* step `c-cauchy`: `∑_{ν<n} 4 c_F q_ν σ_ν ≤ 5 c_F q₀ σ₀ = e_Φ = 5 c_F ε₀/(α₀ σ₀^{t-1})`, and the
  tails `∑_{n ≤ ν < N} 4 c_F q_ν σ_ν ≤ e_Φ 8^{-n}`;
* step `c-op`: `∏_{μ=1}^{n} (1 + 2^{-μ-1}) ≤ e^{1/2} < 2`.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

theorem sum_inv_pow_Ico_le {r : ℝ} (hr : 1 < r) (n N : ℕ) :
    ∑ ν ∈ Finset.Ico n N, 1 / r ^ ν ≤ r / (r - 1) / r ^ n := by
  have hr0 : 0 < r := by linarith
  have h1 : 0 ≤ 1 / r := by positivity
  have h2 : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
  have h := geom_sum_Ico_le_of_lt_one (m := n) (n := N) h1 h2
  simp only [one_div_pow] at h
  refine h.trans (le_of_eq ?_)
  have : r - 1 ≠ 0 := by linarith
  field_simp

/-- `∏_{μ<n} (1 + 2^{-μ-2}) ≤ e^{1/2} < 2` (blueprint `bpW:w6:convergence`, step `c-op`:
`∏_{μ ≥ 1} (1 + 2^{-μ-1})`). -/
theorem w6prod_le_two (n : ℕ) : ∏ μ ∈ Finset.range n, (1 + 1 / (2 : ℝ) ^ (μ + 2)) ≤ 2 := by
  have hexp : ∏ μ ∈ Finset.range n, (1 + 1 / (2 : ℝ) ^ (μ + 2)) ≤
      Real.exp (∑ μ ∈ Finset.range n, 1 / (2 : ℝ) ^ (μ + 2)) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun μ _ => by positivity) fun μ _ => by
      have := Real.add_one_le_exp (1 / (2 : ℝ) ^ (μ + 2)); linarith
  have hsum : ∑ μ ∈ Finset.range n, 1 / (2 : ℝ) ^ (μ + 2) ≤ 1 / 2 := by
    have h := sum_inv_pow_Ico_le (r := 2) (by norm_num) 2 (n + 2)
    have e : ∑ μ ∈ Finset.range n, 1 / (2 : ℝ) ^ (μ + 2) =
        ∑ ν ∈ Finset.Ico 2 (n + 2), 1 / (2 : ℝ) ^ ν := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1) fun μ _ => by rw [add_comm 2 μ]
    rw [e]; refine h.trans (le_of_eq ?_); norm_num
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    have he : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith
    have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  exact hexp.trans ((Real.exp_le_exp.2 hsum).trans h2)

namespace W6SeqData

variable {d : W6SeqData} (hd : d.SeqValid) (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
include hd hsmall

/-- `∑_{ν<n} ε_ν ≤ 4ε₀/3`. -/
theorem sum_eps_le (n : ℕ) : ∑ ν ∈ Finset.range n, d.eps ν ≤ 4 / 3 * d.eps0 := by
  have h := sum_three_eps_le hd hsmall n
  rw [← Finset.mul_sum] at h
  linarith

/-- Step `c-freq`: `∑_{ν<n} 6π ε_ν ≤ 8π ε₀` and `∑_{ν<n} 3 ε_ν ≤ 4 ε₀`. -/
theorem freq_sum_le (n : ℕ) :
    ∑ ν ∈ Finset.range n, 6 * π * d.eps ν ≤ 8 * π * d.eps0 ∧
      ∑ ν ∈ Finset.range n, 3 * d.eps ν ≤ 4 * d.eps0 := by
  refine ⟨?_, sum_three_eps_le hd hsmall n⟩
  rw [← Finset.mul_sum]
  have := sum_eps_le hd hsmall n
  have := Real.pi_pos
  nlinarith

/-- `∑_{ν<n} ε_ν/λ_ν ≤ (4/λ₀)(4ε₀/3)`. -/
theorem sum_eps_div_lam_le (n : ℕ) :
    ∑ ν ∈ Finset.range n, d.eps ν / d.lam ν ≤ 4 / d.lam 0 * (4 / 3 * d.eps0) := by
  have hl0 := lam_pos hd 0
  calc ∑ ν ∈ Finset.range n, d.eps ν / d.lam ν ≤ ∑ ν ∈ Finset.range n, 4 / d.lam 0 * d.eps ν := by
        refine Finset.sum_le_sum fun ν _ => ?_
        have hl := lam_pos hd ν
        have hge := lam_ge hd ν
        have he := (epsNu_pos hd ν).le
        rw [div_le_iff₀ hl]
        calc d.eps ν = 4 / d.lam 0 * d.eps ν * (d.lam 0 / 4) := by field_simp
          _ ≤ 4 / d.lam 0 * d.eps ν * d.lam ν := by gcongr
    _ = 4 / d.lam 0 * ∑ ν ∈ Finset.range n, d.eps ν := by rw [Finset.mul_sum]
    _ ≤ 4 / d.lam 0 * (4 / 3 * d.eps0) := by gcongr; exact sum_eps_le hd hsmall n

/-- Step `c-freq`, Lipschitz parts: `∑_{ν<n} 6π ε_ν/λ_ν ≤ 64π ε₀/λ₀` and
`∑_{ν<n} 3 ε_ν/λ_ν ≤ 16 ε₀/λ₀`. -/
theorem freq_lip_sum_le (n : ℕ) :
    ∑ ν ∈ Finset.range n, 6 * π * d.eps ν / d.lam ν ≤ 64 * π * d.eps0 / d.lam 0 ∧
      ∑ ν ∈ Finset.range n, 3 * d.eps ν / d.lam ν ≤ 16 * d.eps0 / d.lam 0 := by
  have h := sum_eps_div_lam_le hd hsmall n
  have hl0 := lam_pos hd 0
  have he := hd.eps0_pos
  have hπ := Real.pi_pos
  have e1 : ∑ ν ∈ Finset.range n, 6 * π * d.eps ν / d.lam ν =
      6 * π * ∑ ν ∈ Finset.range n, d.eps ν / d.lam ν := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ν _ => by ring
  have e2 : ∑ ν ∈ Finset.range n, 3 * d.eps ν / d.lam ν =
      3 * ∑ ν ∈ Finset.range n, d.eps ν / d.lam ν := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ν _ => by ring
  rw [e1, e2]
  have e3 : 4 / d.lam 0 * (4 / 3 * d.eps0) = 16 / 3 * (d.eps0 / d.lam 0) := by ring
  rw [e3] at h
  have hq : 0 ≤ d.eps0 / d.lam 0 := by positivity
  constructor
  · rw [show 64 * π * d.eps0 / d.lam 0 = 64 * π * (d.eps0 / d.lam 0) by ring]
    nlinarith
  · rw [show 16 * d.eps0 / d.lam 0 = 16 * (d.eps0 / d.lam 0) by ring]
    nlinarith

/-- `q_ν σ_ν ≤ q₀ σ₀ 8^{-ν}`. -/
theorem q_sigma_le (ν : ℕ) : d.qNu ν * d.sigma ν ≤ d.qNu 0 * d.sigma 0 / 8 ^ ν := by
  have h : ∀ ν, d.qNu ν ≤ d.qNu 0 / 4 ^ ν := by
    intro ν
    induction ν with
    | zero => simp
    | succ n ih =>
      calc d.qNu (n + 1) ≤ d.qNu n / 4 := q_succ_le hd hsmall n
        _ ≤ d.qNu 0 / 4 ^ n / 4 := by gcongr
        _ = d.qNu 0 / 4 ^ (n + 1) := by rw [pow_succ]; ring
  have hs : d.sigma ν = d.sigma 0 / 2 ^ ν := by simp [sigma]
  rw [hs]
  have hσ := (sigmaNu_pos hd 0).le
  have hq0 := (qNu_pos hd 0).le
  calc d.qNu ν * (d.sigma 0 / 2 ^ ν) ≤ d.qNu 0 / 4 ^ ν * (d.sigma 0 / 2 ^ ν) := by
        gcongr; exact h ν
    _ = d.qNu 0 * d.sigma 0 / 8 ^ ν := by
        rw [show (8 : ℝ) ^ ν = 4 ^ ν * 2 ^ ν by rw [← mul_pow]; norm_num]; field_simp

/-- `e_Φ = 5 c_F ε₀/(α₀ σ₀^{t-1})` (blueprint `bpW:w6:convergence` (iii)). -/
def ePhi (d : W6SeqData) : ℝ := 5 * stepMF w6CF w6T d.al0 (d.sigma 0) d.eps0

omit hsmall in
theorem ePhi_eq : d.ePhi = 5 * w6CF * d.qNu 0 * d.sigma 0 := by
  have h := stepMF_eq hd 0
  rw [alpha_zero] at h
  unfold ePhi; rw [show d.eps0 = d.eps 0 from rfl, h]; ring

/-- Step `c-cauchy`, tails: `∑_{n ≤ ν < N} 4 c_F q_ν σ_ν ≤ e_Φ 8^{-n}`. -/
theorem cauchy_tail_le (n N : ℕ) :
    ∑ ν ∈ Finset.Ico n N, 4 * w6CF * d.qNu ν * d.sigma ν ≤ d.ePhi / 8 ^ n := by
  rw [ePhi_eq hd]
  have hc := w6CF_pos
  have hqs : 0 ≤ d.qNu 0 * d.sigma 0 := (mul_pos (qNu_pos hd 0) (sigmaNu_pos hd 0)).le
  calc ∑ ν ∈ Finset.Ico n N, 4 * w6CF * d.qNu ν * d.sigma ν
      ≤ ∑ ν ∈ Finset.Ico n N, 4 * w6CF * (d.qNu 0 * d.sigma 0) * (1 / 8 ^ ν) := by
        refine Finset.sum_le_sum fun ν _ => ?_
        have := q_sigma_le hd hsmall ν
        calc 4 * w6CF * d.qNu ν * d.sigma ν = 4 * w6CF * (d.qNu ν * d.sigma ν) := by ring
          _ ≤ 4 * w6CF * (d.qNu 0 * d.sigma 0 / 8 ^ ν) := by gcongr
          _ = 4 * w6CF * (d.qNu 0 * d.sigma 0) * (1 / 8 ^ ν) := by ring
    _ = 4 * w6CF * (d.qNu 0 * d.sigma 0) * ∑ ν ∈ Finset.Ico n N, 1 / (8 : ℝ) ^ ν := by
        rw [Finset.mul_sum]
    _ ≤ 4 * w6CF * (d.qNu 0 * d.sigma 0) * (8 / (8 - 1) / 8 ^ n) := by
        gcongr; exact sum_inv_pow_Ico_le (by norm_num) n N
    _ ≤ 5 * w6CF * d.qNu 0 * d.sigma 0 / 8 ^ n := by
        have hp : (0 : ℝ) < 8 ^ n := by positivity
        rw [show 4 * w6CF * (d.qNu 0 * d.sigma 0) * (8 / (8 - 1) / 8 ^ n) =
          32 / 7 * (w6CF * (d.qNu 0 * d.sigma 0)) / 8 ^ n by ring,
          show 5 * w6CF * d.qNu 0 * d.sigma 0 / 8 ^ n =
            5 * (w6CF * (d.qNu 0 * d.sigma 0)) / 8 ^ n by
            ring]
        gcongr; norm_num

/-- Step `c-cauchy`: `∑_{ν<n} 4 c_F q_ν σ_ν ≤ e_Φ`. -/
theorem cauchy_sum_le (n : ℕ) :
    ∑ ν ∈ Finset.range n, 4 * w6CF * d.qNu ν * d.sigma ν ≤ d.ePhi := by
  have h := cauchy_tail_le hd hsmall 0 n
  rw [Finset.range_eq_Ico]; simpa using h

omit hsmall in
/-- `2 · 2 M_{F,ν} = 4 c_F q_ν σ_ν` (step `c-cauchy`). -/
theorem two_two_MF_eq (ν : ℕ) :
    2 * (2 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν)) =
      4 * w6CF * d.qNu ν * d.sigma ν := by
  rw [stepMF_eq hd ν]; ring

end W6SeqData

end KAM.Wave
