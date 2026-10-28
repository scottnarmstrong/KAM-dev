/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Interfaces.Constants

/-!
# Part 10 assembly: the choice of constants (`bpN:p10:choice`, `bpN:p10:choice-props`)

The Theorem-1 quantities `s₁, F₁, ε₁, R₀, ε', τ, ρ` in terms of the seven data, the packed choice
`(C, T, c, ε₀)` (made before `h`, `f`, `ε`), and the numerical steps `cp-dict`, `cp-rad`, `cp-size`
and the time prefactor helper. All proofs reduce to the arithmetic lemmas of
`Interfaces/Constants`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Nekhoroshev

variable {n : ℕ}

/-- Theorem-1 quantities, reusing the existing seven-data carrier and constants. -/
def HeadParams.s1 (p : HeadParams n) : ℝ := p.s / 2
def HeadParams.F1 (p : HeadParams n) : ℝ := KAM.Weighted.coth (Real.pi * p.s / 4) ^ n
def HeadParams.eps1 (p : HeadParams n) : ℝ := p.mu * p.r0 ^ 2 / (2 ^ 10 * p.A ^ (2 * n))
def HeadParams.R0 (p : HeadParams n) : ℝ := p.r0 / p.A
def HeadParams.epsPrime (p : HeadParams n) (ε : ℝ) : ℝ := p.F1 * ε
def HeadParams.tau (p : HeadParams n) (ε : ℝ) : ℝ :=
  p.T * Real.exp (p.c * ε ^ (-HeadParams.expo n))
def HeadParams.rho (p : HeadParams n) (ε : ℝ) : ℝ := p.C * ε ^ HeadParams.expo n

/-- choice: values are the already existing HeadParams constants, chosen before h and f. -/
def choice (p : HeadParams n) : ℝ × ℝ × ℝ × ℝ := (p.C, p.T, p.c, p.eps0)

/-- cp-ab and hd-const. -/
theorem choice_props (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) :
    0 < p.C ∧ 0 < p.T ∧ 0 < p.c ∧ 0 < p.eps0 ∧
    p.C * p.eps0 ^ HeadParams.expo n ≤ p.R / 4 ∧
    0 < p.mu ∧ p.mu ≤ p.B ∧ 22 ≤ p.A ∧
    p.r0 ≤ p.s / 2 ∧ p.r0 ≤ p.R / 8 ∧
    p.r0 ≤ p.ell / (2 * p.B) ∧ p.r0 ≤ 4 * p.wmin / p.mu := by
  have hn1 : 1 ≤ n := by omega
  have hmu := p.mu_pos hn1 hp
  have h2 := p.two_mu_le_B hn1 hp
  exact ⟨p.C_pos hn1 hp, p.T_pos hn1 hp, p.c_pos hn1 hp, p.eps0_pos hn1 hp,
    (const_eps0 hn1 p hp).1, hmu, by linarith, (const_size hn1 p hp).2.2.1,
    p.r0_le_half_s, p.r0_le_R_div_eight, p.r0_le_ell_div, p.r0_le_wmin_div⟩

/-- `ε₁ > 0`. -/
private theorem eps1_pos {n : ℕ} (hn : 1 ≤ n) (p : HeadParams n) (hp : p.Pos) : 0 < p.eps1 := by
  have hmu := p.mu_pos hn hp
  have hr0 := p.r0_pos hn hp
  have hA := p.A_pos hn hp
  unfold HeadParams.eps1
  positivity

/-- `F₁ > 0`. -/
private theorem F1_pos {n : ℕ} (p : HeadParams n) (hp : p.Pos) : 0 < p.F1 := by
  have := p.coth_pos hp
  unfold HeadParams.F1
  positivity

private theorem epsStar_eq {n : ℕ} (p : HeadParams n) : p.epsStar = 2 * Real.pi * p.eps1 := by
  unfold HeadParams.epsStar HeadParams.eps1
  ring

private theorem F_eq {n : ℕ} (p : HeadParams n) : p.F = 2 * Real.pi * p.F1 := by
  unfold HeadParams.F HeadParams.F1
  ring

/-- cp-dict; no perturbation norm or smallness is assumed as a conclusion. -/
theorem cp_dict (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) (ε : ℝ) :
    p.epsStar = 2 * Real.pi * p.eps1 ∧ p.F = 2 * Real.pi * p.F1 ∧
    (p.epsPrime ε ≤ p.eps1 ↔ ε ≤ p.epsStar / p.F) ∧
    (0 < ε → ε ≤ p.eps0 → 0 < p.epsPrime ε ∧ p.epsPrime ε ≤ p.eps1) := by
  have hn1 : 1 ≤ n := by omega
  have hF1 := F1_pos p hp
  have hpi := Real.pi_pos
  have hdiv : p.epsStar / p.F = p.eps1 / p.F1 := by
    rw [epsStar_eq, F_eq]
    field_simp
  have hiff : p.epsPrime ε ≤ p.eps1 ↔ ε ≤ p.epsStar / p.F := by
    rw [hdiv, le_div_iff₀ hF1]
    unfold HeadParams.epsPrime
    rw [mul_comm]
  refine ⟨epsStar_eq p, F_eq p, hiff, fun hε hε0 => ⟨mul_pos hF1 hε, ?_⟩⟩
  exact hiff.mpr (hε0.trans (const_eps0 hn1 p hp).2)

/-- cp-rad: exact radius and exponential constants in period-one coordinates. -/
theorem cp_rad (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) {ε : ℝ} (hε : 0 < ε) :
    p.R0 / 2 * (p.epsPrime ε / p.eps1) ^ HeadParams.expo n = p.rho ε / 2 ∧
    Real.pi * p.s1 / (3 * Real.sqrt n) * (p.eps1 / p.epsPrime ε) ^ HeadParams.expo n =
      p.c * ε ^ (-HeadParams.expo n) := by
  have hn1 : 1 ≤ n := by omega
  have hF1 := F1_pos p hp
  have hpi := Real.pi_pos
  have h1 : p.F * ε / p.epsStar = p.epsPrime ε / p.eps1 := by
    rw [epsStar_eq, F_eq]
    unfold HeadParams.epsPrime
    have := (eps1_pos hn1 p hp).ne'
    field_simp
  have h2 : p.epsStar / (p.F * ε) = p.eps1 / p.epsPrime ε := by
    rw [epsStar_eq, F_eq]
    unfold HeadParams.epsPrime
    have := (eps1_pos hn1 p hp).ne'
    field_simp
  obtain ⟨c1, c2⟩ := const_conclusion hn1 p hp hε
  rw [h1] at c1
  rw [h2] at c2
  constructor
  · unfold HeadParams.R0 HeadParams.rho
    rw [← c1]
    ring
  · rw [← c2]
    unfold HeadParams.s1 HeadParams.s0
    congr 1
    ring

theorem cp_size (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos) {ε : ℝ}
    (hε : 0 < ε) (hε0 : ε ≤ p.eps0) :
    0 < p.rho ε ∧ p.rho ε ≤ p.R / 4 ∧ 0 < p.tau ε := by
  have hn1 : 1 ≤ n := by omega
  have hC := p.C_pos hn1 hp
  refine ⟨?_, ?_, ?_⟩
  · exact mul_pos hC (Real.rpow_pos_of_pos hε _)
  · calc p.rho ε = p.C * ε ^ HeadParams.expo n := rfl
      _ ≤ p.C * p.eps0 ^ HeadParams.expo n :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hε.le hε0 (by unfold HeadParams.expo; positivity)) hC.le
      _ ≤ p.R / 4 := (const_eps0 hn1 p hp).1
  · exact mul_pos (p.T_pos hn1 hp) (Real.exp_pos _)

/-- Conditional arithmetic helper: Omega is a scalar, not a supplied dynamical conclusion. -/
theorem head_time_prefactor (hn : 3 ≤ n) (p : HeadParams n) (hp : p.Pos)
    {Ω : ℝ} (hΩ : 0 < Ω) (hΩM : Ω ≤ Real.sqrt n * p.M) :
    2 * p.T ≤ p.A ^ 2 * p.s1 / Ω := by
  have hn1 : 1 ≤ n := by omega
  have hpi := Real.pi_pos
  have hM := hp.hM
  have hsq : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_iff]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    exact ⟨by linarith, by nlinarith⟩
  have hΩ' : 2 * Real.pi * Ω ≤ 2 * Real.pi * n * p.M := by
    calc 2 * Real.pi * Ω ≤ 2 * Real.pi * (Real.sqrt n * p.M) :=
          mul_le_mul_of_nonneg_left hΩM (by positivity)
      _ ≤ 2 * Real.pi * (n * p.M) := by gcongr
      _ = 2 * Real.pi * n * p.M := by ring
  have h := const_time_arith hn1 p hp (2 * Real.pi * Ω) (by positivity) hΩ'
  refine h.trans (le_of_eq ?_)
  unfold HeadParams.s0 HeadParams.s1
  field_simp

end KAM.Nekhoroshev

end
