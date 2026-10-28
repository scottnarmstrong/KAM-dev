/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Threshold
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Part 11 (N11-O2): the explicit threshold constants

Literal forms of the proof steps `stepN:p11:final-time` and `stepN:p11:final-mu` of Part 11c.
`nthr_final_time` gives the closed form of the block time
`T_P = C_T μ^(-1/2) exp(c₂ μ^(-1/(2n)))` and the explicit lower bound defining `μ_f`;
`nthr_final_mu` gives `μ₀ = min {μ_a, …, μ_f}` with the explicit `μ_a, …, μ_e` and the
inequalities valid for `0 < μ < μ₀`. Both are unsigned exports of the objects of `Threshold`.
-/

@[expose] public noncomputable section
open Set Filter Topology

namespace KAM.Nekhoroshev
namespace PartialConstants

/-- The constant `C_T` of step `final-time`. -/
def thrCT (c : PartialConstants) : ℝ :=
  c.s * c.m * c.r0 / (240 * c.Mc * (c.A * c.cK) ^ c.n) * (2 * Real.pi / c.kappaC)

/-- The rate `c₂` of step `final-time`. -/
def thrC2 (c : PartialConstants) : ℝ := Real.pi * c.s * c.cK / (3 * Real.sqrt c.n)

/-- `μ_a = 2 π ε₀ / κ_C`. -/
def thrMuA (c : PartialConstants) : ℝ := 2 * Real.pi * c.eps0 / c.kappaC

/-- `μ_b = ρ^(1/b_n)`. -/
def thrMuB (c : PartialConstants) : ℝ := c.ρ ^ (1 / partialDriftExponent c.n)

/-- `μ_c = (π s c_K / (3 √n))^(2n)`. -/
def thrMuC (c : PartialConstants) : ℝ :=
  (Real.pi * c.s * c.cK / (3 * Real.sqrt c.n)) ^ (2 * c.n)

/-- `μ_d = (c_K / (256 k ρ R₀))^(1/γ₁)` with `γ₁ = 1/(2n) - 2 b_n`. -/
def thrMuD (c : PartialConstants) (κ : ℝ) : ℝ :=
  (c.cK / (256 * κ * c.ρ * c.R0)) ^ (1 / (1 / (2 * (c.n : ℝ)) - 2 * partialDriftExponent c.n))

/-- `μ_e = (c_K / R₀)^(1/γ₂)` with `γ₂ = 1/(2n) - b_n`. -/
def thrMuE (c : PartialConstants) : ℝ :=
  (c.cK / c.R0) ^ (1 / (1 / (2 * (c.n : ℝ)) - partialDriftExponent c.n))

end PartialConstants

/-- `μ^b < X` from `μ < X^(1/b)`. -/
theorem nthr_rpow_lt_of_lt {μ X b : ℝ} (hμ : 0 < μ) (hb : 0 < b) (hX : 0 < X)
    (h : μ < X ^ (1 / b)) : μ ^ b < X := by
  have := Real.rpow_lt_rpow hμ.le h hb
  rwa [← Real.rpow_mul hX.le, one_div_mul_cancel hb.ne', Real.rpow_one] at this

/-- Closed form of the block time. -/
theorem nthr_blockTime_closed (c : PartialConstants) (hn : 2 ≤ c.n) (hρ : 0 < c.ρ)
    (hg : 0 < c.g) (hm : 0 < c.m) (hMc : 0 < c.Mc) {μ : ℝ} (hμ : 0 < μ) :
    c.blockTime μ = c.thrCT * μ ^ (-(1/2 : ℝ)) *
      Real.exp (c.thrC2 * μ ^ (-(1/(2*(c.n:ℝ))))) := by
  obtain ⟨hs, hm1, hM1, hr0, hA, he0, hR0, hκC, hcK⟩ := c.nthr_pos hρ hg hm hMc
  have hn0 : (0:ℝ) < c.n := by exact_mod_cast (by omega : 0 < c.n)
  have hsq : 0 < Real.sqrt c.n := Real.sqrt_pos.2 hn0
  set y : ℝ := μ ^ (-(1/(2*(c.n:ℝ)))) with hydef
  have hy0 : 0 < y := Real.rpow_pos_of_pos hμ _
  have hK : c.K μ = c.cK * y := c.nthr_K_eq hκC he0 hμ
  have hyn : y ^ c.n = μ ^ (-(1/2 : ℝ)) := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le]; congr 1; field_simp
  have hkap : c.kappa μ = 2*Real.pi*c.cK*c.s/Real.sqrt c.n * y := by
    unfold PartialConstants.kappa; rw [hK]; field_simp
  have hex : c.kappa μ / 6 = c.thrC2 * y := by
    rw [hkap]; unfold PartialConstants.thrC2; field_simp; ring
  have hμp : 0 < μ ^ (-(1/2 : ℝ)) := Real.rpow_pos_of_pos hμ _
  have hz : (μ ^ (-(1/2 : ℝ))) ^ 2 * μ = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ.le, ← Real.rpow_add_one hμ.ne']
    norm_num
  unfold PartialConstants.blockTime PartialConstants.rTheta PartialConstants.eps
  rw [hex, hK, mul_pow, mul_pow, hyn]
  unfold PartialConstants.thrCT PartialConstants.m1 PartialConstants.M1
  have hAc : 0 < (c.A * c.cK) ^ c.n := by positivity
  generalize μ ^ (-(1/2 : ℝ)) = z at *
  field_simp
  linear_combination (-(c.A ^ c.n * c.cK ^ c.n)) * hz

/-- `stepN:p11:final-time`: `T_P = C_T μ^(-1/2) exp(c₂ μ^(-1/(2n)))`, `C_T, c₂ > 0`, and
`μ T_P e^(-μ^(-a_n)) ≥ C_T μ^(1/2) e^((c₂/2) μ^(-1/(2n))) → ∞`, which defines `μ_f`. -/
theorem nthr_final_time (c : PartialConstants) (hn : 2 ≤ c.n) (hρ : 0 < c.ρ)
    (hg : 0 < c.g) (hm : 0 < c.m) (hMc : 0 < c.Mc) :
    0 < c.thrCT ∧ 0 < c.thrC2 ∧
    (∀ μ : ℝ, 0 < μ → c.blockTime μ = c.thrCT * μ ^ (-(1/2 : ℝ)) *
      Real.exp (c.thrC2 * μ ^ (-(1/(2*(c.n:ℝ)))))) ∧
    Tendsto (fun μ : ℝ => c.thrCT * μ ^ (1/2 : ℝ) *
      Real.exp (c.thrC2 / 2 * μ ^ (-(1/(2*(c.n:ℝ)))))) (𝓝[>] 0) atTop ∧
    ∃ μf : ℝ, 0 < μf ∧ ∀ μ : ℝ, 0 < μ → μ < μf →
      c.thrCT * μ ^ (1/2 : ℝ) * Real.exp (c.thrC2 / 2 * μ ^ (-(1/(2*(c.n:ℝ))))) ≤
        μ * c.blockTime μ * Real.exp (-(μ ^ (-partialTimeExponent c.n))) ∧
      1 ≤ c.thrCT * μ ^ (1/2 : ℝ) * Real.exp (c.thrC2 / 2 * μ ^ (-(1/(2*(c.n:ℝ))))) ∧
      μ⁻¹ * Real.exp (μ ^ (-partialTimeExponent c.n)) ≤ c.blockTime μ := by
  obtain ⟨hs, hm1, hM1, hr0, hA, he0, hR0, hκC, hcK⟩ := c.nthr_pos hρ hg hm hMc
  obtain ⟨hT, hTD, hD2⟩ := exponents hn
  have hn0 : (0:ℝ) < c.n := by exact_mod_cast (by omega : 0 < c.n)
  have hsq : 0 < Real.sqrt c.n := Real.sqrt_pos.2 hn0
  set E : ℝ := 1/(2*(c.n:ℝ)) with hEdef
  have hE : 0 < E := by positivity
  set T := partialTimeExponent c.n with hTdef
  have hCT : 0 < c.thrCT := by unfold PartialConstants.thrCT; positivity
  have hC2 : 0 < c.thrC2 := by unfold PartialConstants.thrC2; positivity
  have hclosed := fun μ (hμ : 0 < μ) => nthr_blockTime_closed c hn hρ hg hm hMc hμ
  have hyl : Tendsto (fun μ : ℝ => μ ^ (-E)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hE)
  have hyn : ∀ μ : ℝ, 0 < μ → (μ ^ (-E)) ^ c.n = μ ^ (-(1/2 : ℝ)) := by
    intro μ hμ
    rw [← Real.rpow_natCast, ← Real.rpow_mul hμ.le]; congr 1; rw [hEdef]; field_simp
  have hhalf : ∀ μ : ℝ, 0 < μ → μ ^ (1/2 : ℝ) = ((μ ^ (-E)) ^ c.n)⁻¹ := by
    intro μ hμ
    rw [hyn μ hμ, ← Real.rpow_neg hμ.le]; norm_num
  have hlim : Tendsto (fun μ : ℝ => c.thrCT * μ ^ (1/2 : ℝ) *
      Real.exp (c.thrC2 / 2 * μ ^ (-E))) (𝓝[>] 0) atTop := by
    have h0 := (tendsto_exp_mul_div_rpow_atTop (c.n : ℝ) (c.thrC2 / 2) (by positivity)).comp hyl
    have h1 := h0.const_mul_atTop hCT
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with μ hμ
    have hμ' : (0:ℝ) < μ := hμ
    simp only [Function.comp_apply]
    rw [hhalf μ hμ', Real.rpow_natCast]
    ring
  have hτ : T / E < 1 := by
    rw [div_lt_one hE]; rw [hEdef] at hD2 ⊢; linarith
  have h1 : ∀ᶠ μ : ℝ in 𝓝[>] 0, 1 * (μ ^ (-E)) ^ (T / E) ≤ c.thrC2 / 2 * μ ^ (-E) :=
    hyl.eventually (nthr_rpow_le_eventually 1 (by positivity) hτ)
  have h2 := hlim.eventually (eventually_ge_atTop (1:ℝ))
  have hall := h1.and (h2.and self_mem_nhdsWithin)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  refine ⟨hCT, hC2, hclosed, hlim, u, hu, fun μ hμ hμu => ?_⟩
  obtain ⟨hk1, hk2, -⟩ := hsub ⟨hμ, hμu⟩
  set y : ℝ := μ ^ (-E) with hydef
  have hτ' : μ ^ (-T) = y ^ (T/E) := by
    rw [hydef, ← Real.rpow_mul hμ.le]; congr 1; field_simp
  have hbt := hclosed μ hμ
  have hμμ : μ * μ ^ (-(1/2 : ℝ)) = μ ^ (1/2 : ℝ) := by
    rw [← Real.rpow_one_add' hμ.le (by norm_num)]; norm_num
  have hmain : c.thrCT * μ ^ (1/2 : ℝ) * Real.exp (c.thrC2 / 2 * y) ≤
      μ * c.blockTime μ * Real.exp (-(μ ^ (-T))) := by
    rw [hbt, hτ']
    have e : μ * (c.thrCT * μ ^ (-(1/2 : ℝ)) * Real.exp (c.thrC2 * y)) *
        Real.exp (-(y ^ (T/E))) =
        c.thrCT * μ ^ (1/2 : ℝ) * Real.exp (c.thrC2 * y - y ^ (T/E)) := by
      rw [← hμμ, Real.exp_sub, Real.exp_neg]; field_simp
    rw [e]
    gcongr
    linarith
  refine ⟨hmain, hk2, ?_⟩
  have hex : Real.exp (μ ^ (-T)) ≤ μ * c.blockTime μ := by
    have h := hk2.trans hmain
    rw [Real.exp_neg, ← div_eq_mul_inv] at h
    exact (one_le_div (Real.exp_pos _)).1 h
  rw [inv_mul_le_iff₀ hμ]; exact hex

end KAM.Nekhoroshev
end
