/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# W6: the arithmetic of the iterative lemma (blueprint `bpW:w6:iter-lemma`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint label `bpW:w6:iter-lemma` (milestone W6): the parts that concern the
sequences of Definition `bpW:w6:sequences` only.

Under the smallness `ε₀ ≤ γ₀ α₀ σ₀^t`, with `q_ν = ε_ν/(α_ν σ_ν^t)`:
* the statement `q_ν ≤ γ₀ 2^{-ν}` and `q_{ν+1} ≤ q_ν/4` of the lemma (`w6Iter_q_bounds`);
* step `il-small`: `η_ν ≤ 1/8` and `ε_ν ≤ α_ν σ_ν^t η_ν²/c₀`, which is W5's smallness
  `bpW:w5:small` (`W6SeqData.eps_le_small`);
* step `il-err`: `ε_{ν+1} ≤ ε_ν/4` (used by `bpW:w6:k0`) and `λ_{ν+1} ≤ λ_ν`;
* step `il-lip`: `(6π+3) ε_ν/λ_ν ≤ 2^{-ν-2} M_ν` and `M_ν (1 + 2^{-ν-2}) ≤ M_{ν+1}`;
* step `il-div`: `(1+K)(1+K^τ) ≤ 4 K^{τ+1}` for `K ≥ 1` and `6π · 4 K_ν^{τ+1} ε_ν ≤ α_ν - α_{ν+1}`;
* step `il-tr`: `16 M_{F,ν}/σ_ν ≤ 2^{-ν-2}`, `M_{F,ν} = c_F ε_ν/(α_ν σ_ν^{t-1}) = c_F q_ν σ_ν`.

The application of W5's step theorem `bpW:w5:step` (the rest of the lemma) is not part of this
file.
-/

@[expose] public noncomputable section

open Real

namespace KAM.Wave

namespace W6SeqData

variable {d : W6SeqData} (hd : d.SeqValid)
include hd

theorem sigma_rpow_pos (ν : ℕ) : 0 < d.sigma ν ^ w6T := Real.rpow_pos_of_pos (sigmaNu_pos hd ν) _

theorem alpha_sigma_pos (ν : ℕ) : 0 < d.alpha ν * d.sigma ν ^ w6T :=
  mul_pos (alpha_pos hd ν) (sigma_rpow_pos hd ν)

/-- `ε_ν = q_ν α_ν σ_ν^t`. -/
theorem eps_eq_q (ν : ℕ) : d.eps ν = d.qNu ν * (d.alpha ν * d.sigma ν ^ w6T) := by
  unfold qNu; rw [div_mul_cancel₀ _ (alpha_sigma_pos hd ν).ne']

/-- `σ_{ν+1}^t = σ_ν^t / 2^{52}`. -/
theorem sigma_succ_rpow (ν : ℕ) : d.sigma (ν + 1) ^ w6T = d.sigma ν ^ w6T / 2 ^ (52 : ℕ) := by
  rw [sigma_succ, Real.div_rpow (sigmaNu_pos hd ν).le (by norm_num), w6T_eq,
    show (52 : ℝ) = ((52 : ℕ) : ℝ) by norm_num, Real.rpow_natCast (2 : ℝ)]

theorem alpha_le_two_alpha_succ (ν : ℕ) : d.alpha ν ≤ 2 * d.alpha (ν + 1) := by
  unfold alpha
  have := hd.al0_pos
  rw [pow_succ]
  have h : (0 : ℝ) < 2 ^ ν := by positivity
  rw [show 1 / ((2 : ℝ) ^ ν * 2) = 1 / 2 ^ ν / 2 by field_simp]
  have : 0 ≤ 1 / (2 : ℝ) ^ ν := by positivity
  nlinarith

/-- `q_{ν+1} = 2^{52} · 2C₂ q_ν η_ν α_ν/α_{ν+1}`. -/
theorem q_succ_eq (ν : ℕ) :
    d.qNu (ν + 1) =
      2 ^ (52 : ℕ) * (2 * w6C2 * d.qNu ν * d.etaNu ν) * (d.alpha ν / d.alpha (ν + 1)) := by
  have hq : d.qNu (ν + 1) = d.eps (ν + 1) / (d.alpha (ν + 1) * d.sigma (ν + 1) ^ w6T) := rfl
  rw [hq, eps_succ, eps_eq_q hd ν, sigma_succ_rpow hd ν]
  have h1 := alpha_pos hd ν
  have h2 := alpha_pos hd (ν + 1)
  have h3 := sigma_rpow_pos hd ν
  field_simp

theorem q_nonneg_of_eps (ν : ℕ) (he : 0 ≤ d.eps ν) : 0 ≤ d.qNu ν :=
  div_nonneg he (alpha_sigma_pos hd ν).le

/-- One step: if `0 ≤ q_ν ≤ γ₀` then `q_{ν+1} ≤ q_ν/4` (step `il-err`). -/
theorem q_succ_le_of (ν : ℕ) (h0 : 0 ≤ d.qNu ν) (hγ : d.qNu ν ≤ w6Gamma0) :
    d.qNu (ν + 1) ≤ d.qNu ν / 4 := by
  rw [q_succ_eq hd ν]
  have hη : d.etaNu ν ≤ w6GammaBase⁻¹ := by
    rw [eta_eq_q, ← w6Gamma0_rpow_third]
    exact Real.rpow_le_rpow h0 hγ (by norm_num)
  have hη0 : 0 ≤ d.etaNu ν := Real.rpow_nonneg h0 _
  have ha : d.alpha ν / d.alpha (ν + 1) ≤ 2 := by
    rw [div_le_iff₀ (alpha_pos hd (ν + 1))]; exact alpha_le_two_alpha_succ hd ν
  have ha0 : 0 ≤ d.alpha ν / d.alpha (ν + 1) := (div_pos (alpha_pos hd ν) (alpha_pos hd _)).le
  have hC := w6C2_pos
  have hX := w6GammaBase_pos
  have hXge := w6GammaBase_ge
  have hc0 := w6C0_pos
  -- `2^{52} · 2 C₂ · X⁻¹ · 2 ≤ 1/4`
  have hkey : (2 : ℝ) ^ (52 : ℕ) * (2 * w6C2) * w6GammaBase⁻¹ * 2 ≤ 1 / 4 := by
    rw [mul_assoc _ w6GammaBase⁻¹, mul_comm w6GammaBase⁻¹, ← mul_assoc, ← div_eq_mul_inv,
      div_le_iff₀ hX]
    have : (2 : ℝ) ^ (56 : ℕ) = 2 ^ (52 : ℕ) * 16 := by norm_num
    nlinarith
  calc 2 ^ (52 : ℕ) * (2 * w6C2 * d.qNu ν * d.etaNu ν) * (d.alpha ν / d.alpha (ν + 1))
      ≤ 2 ^ (52 : ℕ) * (2 * w6C2 * d.qNu ν * w6GammaBase⁻¹) * 2 := by gcongr
    _ = ((2 : ℝ) ^ (52 : ℕ) * (2 * w6C2) * w6GammaBase⁻¹ * 2) * d.qNu ν := by ring
    _ ≤ 1 / 4 * d.qNu ν := mul_le_mul_of_nonneg_right hkey h0
    _ = d.qNu ν / 4 := by ring

theorem eta_pos_of (ν : ℕ) (he : 0 < d.eps ν) : 0 < d.etaNu ν := by
  rw [eta_eq_q]; exact Real.rpow_pos_of_pos (div_pos he (alpha_sigma_pos hd ν)) _

/-- `ε_ν > 0`. -/
theorem epsNu_pos (ν : ℕ) : 0 < d.eps ν := by
  induction ν with
  | zero => exact hd.eps0_pos
  | succ n ih =>
    rw [eps_succ]; have := eta_pos_of hd n ih; have := w6C2_pos; positivity

theorem qNu_pos (ν : ℕ) : 0 < d.qNu ν := div_pos (epsNu_pos hd ν) (alpha_sigma_pos hd ν)

theorem eta_pos (ν : ℕ) : 0 < d.etaNu ν := eta_pos_of hd ν (epsNu_pos hd ν)

/-- `α_{ν+1} ≤ α_ν`. -/
theorem alpha_succ_le (ν : ℕ) : d.alpha (ν + 1) ≤ d.alpha ν := by
  unfold alpha
  have := hd.al0_pos
  have h : 1 / (2 : ℝ) ^ (ν + 1) ≤ 1 / 2 ^ ν :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_succ ν))
  have : 0 ≤ d.al0 / 2 := by positivity
  nlinarith

theorem alpha_sigma_succ_le (ν : ℕ) :
    d.alpha (ν + 1) * d.sigma (ν + 1) ^ w6T ≤ d.alpha ν * d.sigma ν ^ w6T := by
  have ha := alpha_succ_le hd ν
  have hs : d.sigma (ν + 1) ^ w6T ≤ d.sigma ν ^ w6T := by
    rw [sigma_succ_rpow hd ν]
    exact div_le_self (sigma_rpow_pos hd ν).le (one_le_pow₀ (by norm_num))
  exact mul_le_mul ha hs (sigma_rpow_pos hd _).le (alpha_pos hd ν).le

section small

variable (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T)
include hsmall

theorem q_zero_le : d.qNu 0 ≤ w6Gamma0 := by
  unfold qNu
  rw [alpha_zero, div_le_iff₀ (by rw [← alpha_zero]; exact alpha_sigma_pos hd 0)]
  have : d.eps 0 = d.eps0 := rfl
  rw [this]; linarith

/-- `q_ν ≤ γ₀ 4^{-ν}`. -/
theorem q_le_four_pow (ν : ℕ) : d.qNu ν ≤ w6Gamma0 / 4 ^ ν := by
  induction ν with
  | zero => simpa using q_zero_le hd hsmall
  | succ n ih =>
    have hγ : d.qNu n ≤ w6Gamma0 :=
      ih.trans (div_le_self w6Gamma0_pos.le (one_le_pow₀ (by norm_num)))
    calc d.qNu (n + 1) ≤ d.qNu n / 4 := q_succ_le_of hd n (qNu_pos hd n).le hγ
      _ ≤ w6Gamma0 / 4 ^ n / 4 := by gcongr
      _ = w6Gamma0 / 4 ^ (n + 1) := by rw [pow_succ]; ring

theorem q_le_gamma0 (ν : ℕ) : d.qNu ν ≤ w6Gamma0 :=
  (q_le_four_pow hd hsmall ν).trans (div_le_self w6Gamma0_pos.le (one_le_pow₀ (by norm_num)))

/-- `q_ν ≤ γ₀ 2^{-ν}`. -/
theorem q_le_two_pow (ν : ℕ) : d.qNu ν ≤ w6Gamma0 / 2 ^ ν := by
  refine (q_le_four_pow hd hsmall ν).trans ?_
  apply div_le_div_of_nonneg_left w6Gamma0_pos.le (by positivity)
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) ν

/-- `q_{ν+1} ≤ q_ν/4`. -/
theorem q_succ_le (ν : ℕ) : d.qNu (ν + 1) ≤ d.qNu ν / 4 :=
  q_succ_le_of hd ν (qNu_pos hd ν).le (q_le_gamma0 hd hsmall ν)

/-- **Iterative lemma, the bounds on `q_ν`** (blueprint `bpW:w6:iter-lemma`): under
`ε₀ ≤ γ₀ α₀ σ₀^t`, `q_ν ≤ γ₀ 2^{-ν}` and `q_{ν+1} ≤ q_ν/4` for every `ν`. -/
theorem w6Iter_q_bounds (ν : ℕ) :
    d.qNu ν ≤ w6Gamma0 / 2 ^ ν ∧ d.qNu (ν + 1) ≤ d.qNu ν / 4 :=
  ⟨q_le_two_pow hd hsmall ν, q_succ_le hd hsmall ν⟩

/-- `η_ν ≤ γ₀^{1/3} ≤ 1/8` (step `il-small`). -/
theorem eta_le (ν : ℕ) : d.etaNu ν ≤ 1 / 8 := by
  have h : d.etaNu ν ≤ w6GammaBase⁻¹ := by
    rw [eta_eq_q, ← w6Gamma0_rpow_third]
    exact Real.rpow_le_rpow (qNu_pos hd ν).le (q_le_gamma0 hd hsmall ν) (by norm_num)
  refine h.trans ?_
  rw [inv_le_comm₀ w6GammaBase_pos (by norm_num)]
  have := w6GammaBase_ge_big
  have : (8 : ℝ) ≤ 2 ^ (56 : ℕ) * 896 := by norm_num
  norm_num at *; linarith

/-- **W5's smallness at stage `ν`** (step `il-small`): `ε_ν ≤ α_ν σ_ν^t η_ν²/c₀`
(`bpW:w5:small`). -/
theorem eps_le_small (ν : ℕ) :
    d.eps ν ≤ d.alpha ν * d.sigma ν ^ w6T * d.etaNu ν ^ 2 / w6C0 := by
  have hq := qNu_pos hd ν
  have hX := w6GammaBase_pos
  have hc0 := w6C0_pos
  -- `η = q^{1/3} ≤ X⁻¹ ≤ c₀⁻¹`, and `q = η³`
  have hη3 : d.etaNu ν ^ 3 = d.qNu ν := by
    rw [eta_eq_q, ← Real.rpow_natCast, ← Real.rpow_mul hq.le]; norm_num
  have hη : d.etaNu ν ≤ w6C0⁻¹ := by
    have h : d.etaNu ν ≤ w6GammaBase⁻¹ := by
      rw [eta_eq_q, ← w6Gamma0_rpow_third]
      exact Real.rpow_le_rpow hq.le (q_le_gamma0 hd hsmall ν) (by norm_num)
    refine h.trans (inv_anti₀ hc0 ?_)
    have := w6C2_pos
    rw [w6GammaBase, w6two_rpow_T4]
    have : 0 ≤ (2 : ℝ) ^ (56 : ℕ) * w6C2 := by positivity
    linarith
  have hη0 := eta_pos hd ν
  have hb := alpha_sigma_pos hd ν
  rw [eps_eq_q hd ν, ← hη3]
  rw [le_div_iff₀ hc0]
  have : d.etaNu ν * w6C0 ≤ 1 := by
    calc d.etaNu ν * w6C0 ≤ w6C0⁻¹ * w6C0 := by gcongr
      _ = 1 := inv_mul_cancel₀ hc0.ne'
  have h2 : 0 ≤ d.etaNu ν ^ 2 * (d.alpha ν * d.sigma ν ^ w6T) := by positivity
  calc d.etaNu ν ^ 3 * (d.alpha ν * d.sigma ν ^ w6T) * w6C0
      = (d.etaNu ν * w6C0) * (d.etaNu ν ^ 2 * (d.alpha ν * d.sigma ν ^ w6T)) := by ring
    _ ≤ 1 * (d.etaNu ν ^ 2 * (d.alpha ν * d.sigma ν ^ w6T)) := by gcongr
    _ = d.alpha ν * d.sigma ν ^ w6T * d.etaNu ν ^ 2 := by ring

/-- `ε_{ν+1} ≤ ε_ν/4` (blueprint `bpW:w6:k0`, proof). -/
theorem eps_succ_le (ν : ℕ) : d.eps (ν + 1) ≤ d.eps ν / 4 := by
  rw [eps_eq_q hd (ν + 1), eps_eq_q hd ν]
  have h1 := q_succ_le hd hsmall ν
  have h2 := alpha_sigma_succ_le hd ν
  have h3 := (qNu_pos hd (ν + 1)).le
  have h4 := (alpha_sigma_pos hd (ν + 1)).le
  calc d.qNu (ν + 1) * (d.alpha (ν + 1) * d.sigma (ν + 1) ^ w6T)
      ≤ d.qNu ν / 4 * (d.alpha ν * d.sigma ν ^ w6T) := mul_le_mul h1 h2 h4 (by
        have := (qNu_pos hd ν).le; positivity)
    _ = d.qNu ν * (d.alpha ν * d.sigma ν ^ w6T) / 4 := by ring

theorem eps_le_four_pow (ν : ℕ) : d.eps ν ≤ d.eps0 / 4 ^ ν := by
  induction ν with
  | zero => simp [eps]
  | succ n ih =>
    calc d.eps (n + 1) ≤ d.eps n / 4 := eps_succ_le hd hsmall n
      _ ≤ d.eps0 / 4 ^ n / 4 := by gcongr
      _ = d.eps0 / 4 ^ (n + 1) := by rw [pow_succ]; ring

/-- `∑_{μ<ν} 3 ε_μ ≤ 4 ε₀` (blueprint `bpW:w6:k0`, proof). -/
theorem sum_three_eps_le (ν : ℕ) : ∑ μ ∈ Finset.range ν, 3 * d.eps μ ≤ 4 * d.eps0 := by
  have h : ∀ n, ∑ μ ∈ Finset.range n, 3 * d.eps μ ≤ 4 * d.eps0 * (1 - 1 / 4 ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := eps_le_four_pow hd hsmall n
      have hp : (0 : ℝ) < 4 ^ n := by positivity
      calc ∑ μ ∈ Finset.range n, 3 * d.eps μ + 3 * d.eps n
          ≤ 4 * d.eps0 * (1 - 1 / 4 ^ n) + 3 * (d.eps0 / 4 ^ n) := by linarith
        _ = 4 * d.eps0 * (1 - 1 / 4 ^ (n + 1)) := by rw [pow_succ]; field_simp; ring
  refine (h ν).trans ?_
  have := hd.eps0_pos
  have : 0 ≤ 1 / (4 : ℝ) ^ ν := by positivity
  nlinarith

/-- **Lipschitz growth** (step `il-lip`): `(6π+3) ε_ν/λ_ν ≤ 2^{-ν-2} M_ν`. -/
theorem lip_growth_le (ν : ℕ) : (6 * π + 3) * d.eps ν / d.lam ν ≤ d.Mnu ν / 2 ^ (ν + 2) := by
  have hM := M_pos hd ν
  have ha := alpha_pos hd ν
  have hσ := sigma_rpow_le_one hd ν
  have hσ0 := (sigma_rpow_pos hd ν).le
  have hq := q_le_two_pow hd hsmall ν
  have hq0 := (qNu_pos hd ν).le
  have hγ := w6Gamma0_le_small
  have hπ := Real.pi_le_four
  have hp : (0 : ℝ) < 2 ^ ν := by positivity
  have he : (6 * π + 3) * d.eps ν / d.lam ν =
      (6 * π + 3) * d.qNu ν * d.sigma ν ^ w6T * d.Mnu ν := by
    rw [eps_eq_q hd ν, lam]; field_simp
  rw [he]
  have h1 : (6 * π + 3) * d.qNu ν * d.sigma ν ^ w6T ≤ 27 * (w6Gamma0 / 2 ^ ν) := by
    have : (6 * π + 3) ≤ 27 := by linarith
    have hg : 0 ≤ 27 * (w6Gamma0 / 2 ^ ν) := by have := w6Gamma0_pos; positivity
    have hpi0 : 0 ≤ 6 * π + 3 := by have := Real.pi_pos; linarith
    calc (6 * π + 3) * d.qNu ν * d.sigma ν ^ w6T ≤ 27 * (w6Gamma0 / 2 ^ ν) * 1 :=
          mul_le_mul (mul_le_mul this hq hq0 (by norm_num)) hσ hσ0 hg
      _ = 27 * (w6Gamma0 / 2 ^ ν) := mul_one _
  have h2 : 27 * (w6Gamma0 / 2 ^ ν) ≤ 1 / 2 ^ (ν + 2) := by
    rw [pow_add]
    have : 108 * w6Gamma0 ≤ 1 := by
      have : (108 : ℝ) * ((2 : ℝ) ^ (56 : ℕ) * 896)⁻¹ ≤ 1 := by norm_num
      nlinarith [w6Gamma0_pos]
    rw [mul_div_assoc', div_le_div_iff₀ hp (by positivity)]
    nlinarith
  calc (6 * π + 3) * d.qNu ν * d.sigma ν ^ w6T * d.Mnu ν ≤ 1 / 2 ^ (ν + 2) * d.Mnu ν :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hM.le
    _ = d.Mnu ν / 2 ^ (ν + 2) := by ring

end small

/-- `M_ν (1 + 2^{-ν-2}) ≤ M_{ν+1}` (step `il-lip`). -/
theorem M_growth_le (ν : ℕ) : d.Mnu ν * (1 + 1 / 2 ^ (ν + 2)) ≤ d.Mnu (ν + 1) := by
  unfold Mnu
  have := hd.M0_pos
  have hp : (0 : ℝ) < 2 ^ ν := by positivity
  rw [show (2 : ℝ) ^ (ν + 2) = 2 ^ ν * 4 by rw [pow_add]; norm_num,
    show (2 : ℝ) ^ (ν + 1) = 2 ^ ν * 2 by rw [pow_succ]]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ this.le
  have e : (2 - 1 / (2 : ℝ) ^ ν) * (1 + 1 / (2 ^ ν * 4)) =
      2 - 1 / (2 ^ ν * 2) - 1 / (2 ^ ν) ^ 2 / 4 := by field_simp; ring
  rw [e]
  have : 0 ≤ 1 / ((2 : ℝ) ^ ν) ^ 2 / 4 := by positivity
  linarith

/-- `λ_{ν+1} ≤ λ_ν` (step `il-err`). -/
theorem lam_succ_le (ν : ℕ) : d.lam (ν + 1) ≤ d.lam ν := by
  unfold lam
  have ha := alpha_succ_le hd ν
  have hM : d.Mnu ν ≤ d.Mnu (ν + 1) := by
    have h := M_growth_le hd ν
    have := M_pos hd ν
    have : 0 ≤ d.Mnu ν * (1 / 2 ^ (ν + 2)) := by positivity
    nlinarith
  exact div_le_div₀ (alpha_pos hd ν).le ha (M_pos hd ν) hM

omit hd in
/-- `α_ν - α_{ν+1} = α₀ 2^{-ν-2}`. -/
theorem alpha_sub_succ (ν : ℕ) : d.alpha ν - d.alpha (ν + 1) = d.al0 / 2 ^ (ν + 2) := by
  unfold alpha; rw [pow_succ, pow_add]; field_simp; ring

omit hd in
/-- `(1+K)(1+K^τ) ≤ 4 K^{τ+1}` for `K ≥ 1` (step `il-div`). -/
theorem one_add_mul_one_add_rpow_le {K : ℝ} (hK : 1 ≤ K) :
    (1 + K) * (1 + K ^ w6Tau) ≤ 4 * K ^ (w6Tau + 1) := by
  have hK0 : 0 < K := by linarith
  have h1 : 1 ≤ K ^ w6Tau := Real.one_le_rpow hK (by rw [w6Tau_eq]; norm_num)
  rw [Real.rpow_add hK0, Real.rpow_one]
  nlinarith

/-- `K_ν^{τ+1} = 2^{25 ν}/(96 π γ₀ σ₀^t)`. -/
theorem K_rpow_eq (ν : ℕ) :
    d.K ν ^ (w6Tau + 1) = (2 ^ ν) ^ (25 : ℕ) / (96 * π * w6Gamma0 * d.sigma 0 ^ w6T) := by
  have hb := K0_base_pos hd
  unfold K K0
  rw [Real.mul_rpow (Real.rpow_nonneg hb.le _) (by positivity), ← Real.rpow_mul hb.le]
  rw [w6Tau_eq, show -(1 / ((24 : ℝ) + 1)) * (24 + 1) = -1 by norm_num, Real.rpow_neg_one,
    show (24 : ℝ) + 1 = ((25 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- `σ_ν^t = σ₀^t/(2^ν)^{52}`. -/
theorem sigma_rpow_eq (ν : ℕ) : d.sigma ν ^ w6T = d.sigma 0 ^ w6T / (2 ^ ν) ^ (52 : ℕ) := by
  have h0 : d.sigma ν = d.sigma 0 / 2 ^ ν := by simp [sigma]
  rw [h0, Real.div_rpow (sigmaNu_pos hd 0).le (by positivity), w6T_eq,
    show (52 : ℝ) = ((52 : ℕ) : ℝ) by norm_num, Real.rpow_natCast (2 ^ ν : ℝ)]

/-- **Divisors** (step `il-div`): `6π · 4 K_ν^{τ+1} ε_ν ≤ α_ν - α_{ν+1}`. -/
theorem div_arith (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T) (ν : ℕ) :
    6 * π * (4 * d.K ν ^ (w6Tau + 1)) * d.eps ν ≤ d.alpha ν - d.alpha (ν + 1) := by
  rw [alpha_sub_succ, K_rpow_eq hd, eps_eq_q hd ν, sigma_rpow_eq hd ν]
  have hb := K0_base_pos hd
  have hq := q_le_two_pow hd hsmall ν
  have hq0 := (qNu_pos hd ν).le
  have ha := alphaNu_le hd ν
  have ha0 := (alpha_pos hd ν).le
  have hγ := w6Gamma0_pos
  have hσ := sigma_rpow_pos hd 0
  have hpi := Real.pi_pos
  set x : ℝ := 2 ^ ν with hx
  have hx1 : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx0 : 0 < x := by linarith
  -- bound `ε_ν ≤ (γ₀/x) α₀ σ₀^t/x^{52}`
  have hε : d.qNu ν * (d.alpha ν * (d.sigma 0 ^ w6T / x ^ (52 : ℕ))) ≤
      w6Gamma0 / x * (d.al0 * (d.sigma 0 ^ w6T / x ^ (52 : ℕ))) := by gcongr
  have e2 : (2 : ℝ) ^ (ν + 2) = 4 * x := by rw [hx, pow_add]; ring
  rw [e2]
  calc 6 * π * (4 * (x ^ (25 : ℕ) / (96 * π * w6Gamma0 * d.sigma 0 ^ w6T))) *
        (d.qNu ν * (d.alpha ν * (d.sigma 0 ^ w6T / x ^ (52 : ℕ))))
      ≤ 6 * π * (4 * (x ^ (25 : ℕ) / (96 * π * w6Gamma0 * d.sigma 0 ^ w6T))) *
        (w6Gamma0 / x * (d.al0 * (d.sigma 0 ^ w6T / x ^ (52 : ℕ)))) := by gcongr
    _ = d.al0 / (4 * x) * (1 / x ^ (27 : ℕ)) := by field_simp; ring
    _ ≤ d.al0 / (4 * x) * 1 := by
        gcongr
        · have := hd.al0_pos; positivity
        · rw [div_le_one (by positivity)]; exact one_le_pow₀ hx1
    _ = d.al0 / (4 * x) := mul_one _

/-- `M_{F,ν} = c_F ε_ν/(α_ν σ_ν^{t-1}) = c_F q_ν σ_ν` (blueprint `bpW:w6:iter-lemma`). -/
theorem stepMF_eq (ν : ℕ) :
    stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) = w6CF * d.qNu ν * d.sigma ν := by
  have hσ := sigmaNu_pos hd ν
  unfold stepMF qNu
  rw [Real.rpow_sub hσ, Real.rpow_one]
  have := alpha_pos hd ν
  have := sigma_rpow_pos hd ν
  field_simp

/-- **Transformations** (step `il-tr`): `16 M_{F,ν}/σ_ν = 16 c_F q_ν ≤ 2^{-ν-2}`. -/
theorem transf_arith (hsmall : d.eps0 ≤ w6Gamma0 * d.al0 * d.sigma 0 ^ w6T) (ν : ℕ) :
    16 * stepMF w6CF w6T (d.alpha ν) (d.sigma ν) (d.eps ν) / d.sigma ν ≤ 1 / 2 ^ (ν + 2) := by
  rw [stepMF_eq hd ν]
  have hσ := sigmaNu_pos hd ν
  have hq := q_le_two_pow hd hsmall ν
  have hcF := w6CF_pos
  have hγX := w6Gamma0_le_inv
  have hX := w6GammaBase_pos
  -- `64 c_F γ₀ ≤ 1`: `X ≥ 2^{56} C₂ ≥ 2^{56} · 168 c_F`
  have hXc : 64 * w6CF ≤ w6GammaBase := by
    have h := w6GammaBase_ge; have := w6C0_pos
    rw [w6C2_eq] at h
    have : (64 : ℝ) * w6CF ≤ 2 ^ (56 : ℕ) * (896 + 168 * w6CF) := by
      have : (0 : ℝ) ≤ 2 ^ (56 : ℕ) * 896 := by positivity
      have : (64 : ℝ) * w6CF ≤ 2 ^ (56 : ℕ) * (168 * w6CF) := by
        have : (64 : ℝ) ≤ 2 ^ (56 : ℕ) * 168 := by norm_num
        nlinarith
      nlinarith
    linarith
  have h64 : 64 * w6CF * w6Gamma0 ≤ 1 := by
    calc 64 * w6CF * w6Gamma0 ≤ 64 * w6CF * w6GammaBase⁻¹ := by gcongr
      _ ≤ w6GammaBase * w6GammaBase⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hX.ne'
  have hp : (0 : ℝ) < 2 ^ ν := by positivity
  have e : 16 * (w6CF * d.qNu ν * d.sigma ν) / d.sigma ν = 16 * w6CF * d.qNu ν := by field_simp
  rw [e, pow_add]
  calc 16 * w6CF * d.qNu ν ≤ 16 * w6CF * (w6Gamma0 / 2 ^ ν) := by gcongr
    _ = (64 * w6CF * w6Gamma0) * (1 / (2 ^ ν * 2 ^ 2)) := by field_simp; ring
    _ ≤ 1 * (1 / (2 ^ ν * 2 ^ 2)) := by gcongr
    _ = 1 / (2 ^ ν * 2 ^ 2) := one_mul _

end W6SeqData

end KAM.Wave
