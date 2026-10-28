/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Constants
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Part 11 (N11-O): the uniform threshold

All constants of `PartialConstants` are fixed before `μ`; the single statement `threshold`
produces `μ₀ > 0` such that for every `0 < μ < μ₀` the six numerical comparisons used by the
block theorem and the provider hold. With `y = μ^(-1/(2n))` one has `K μ = cK * y`,
`kappa μ = c₁ * y`, `d μ = y^(-δ)` and `μ^(-T) = y^τ`, `δ < 1/2`, `τ < 1`, so every comparison is
a polynomial-against-exponential asymptotic in `y → ∞`.
-/

@[expose] public noncomputable section
open Set Filter Topology
open KAM.Weighted

namespace KAM.Nekhoroshev
variable {n k : ℕ}

namespace PartialConstants

/-- Positivity of the derived constants. -/
theorem nthr_pos (c : PartialConstants) (hρ : 0 < c.ρ) (hg : 0 < c.g)
    (hm : 0 < c.m) (hMc : 0 < c.Mc) :
    0 < c.s ∧ 0 < c.m1 ∧ 0 < c.M1 ∧ 0 < c.r0 ∧ 0 < c.A ∧ 0 < c.eps0 ∧ 0 < c.R0 ∧
      0 < c.kappaC ∧ 0 < c.cK := by
  have hs : 0 < c.s := by unfold s; positivity
  have hm1 : 0 < c.m1 := by unfold m1; positivity
  have hM1 : 0 < c.M1 := by unfold M1; positivity
  have hr0 : 0 < c.r0 := by
    unfold r0; exact lt_min (by positivity) (by positivity)
  have hA : 0 < c.A := by unfold A; positivity
  have he0 : 0 < c.eps0 := by unfold eps0; positivity
  have hR0 : 0 < c.R0 := by unfold R0; positivity
  have hκ : 0 < c.kappaC := by
    unfold kappaC coth
    have : 0 < Real.pi * c.s := by positivity
    exact pow_pos (div_pos (Real.cosh_pos _) (Real.sinh_pos_iff.2 this)) _
  exact ⟨hs, hm1, hM1, hr0, hA, he0, hR0, hκ, by unfold cK; positivity⟩

/-- `K μ = cK * μ^(-1/(2n))`. -/
theorem nthr_K_eq (c : PartialConstants) (hκ : 0 < c.kappaC) (he0 : 0 < c.eps0) {μ : ℝ}
    (hμ : 0 < μ) : c.K μ = c.cK * μ ^ (-(1/(2*(c.n:ℝ)))) := by
  have h : c.eps0 / c.eps μ = (2*Real.pi*c.eps0/c.kappaC) * μ⁻¹ := by
    unfold eps; field_simp
  unfold K cK
  rw [h, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hμ.le,
    Real.rpow_neg hμ.le]

end PartialConstants

/-- `X * y^δ ≤ a * y` eventually, for `δ < 1` and `0 < a`. -/
theorem nthr_rpow_le_eventually (X : ℝ) {a δ : ℝ} (ha : 0 < a) (hδ : δ < 1) :
    ∀ᶠ y : ℝ in atTop, X * y ^ δ ≤ a * y := by
  have ht := (tendsto_rpow_neg_atTop (y := 1 - δ) (by linarith)).eventually
    (gt_mem_nhds (show (0:ℝ) < a / (|X| + 1) by positivity))
  filter_upwards [ht, eventually_gt_atTop 0] with y hy hy0
  have h1 : y ^ δ = y ^ (-(1 - δ)) * y := by
    rw [← Real.rpow_add_one hy0.ne']; congr 1; ring
  have hp : 0 < y ^ (-(1 - δ)) := Real.rpow_pos_of_pos hy0 _
  rw [h1]
  have hX : X ≤ |X| + 1 := (le_abs_self X).trans (by linarith)
  have h2 : (|X| + 1) * y ^ (-(1 - δ)) ≤ a := by
    rw [lt_div_iff₀ (by positivity)] at hy; nlinarith
  calc X * (y ^ (-(1 - δ)) * y) = (X * y ^ (-(1 - δ))) * y := by ring
    _ ≤ ((|X| + 1) * y ^ (-(1 - δ))) * y := by gcongr
    _ ≤ a * y := by gcongr

/-- The exponential comparison `y^n exp(y^τ) ≤ C exp(a y / 6)` eventually. -/
theorem nthr_exp_eventually (n : ℕ) {C a τ : ℝ} (hC : 0 < C) (ha : 0 < a) (hτ : τ < 1) :
    ∀ᶠ y : ℝ in atTop, y ^ n * Real.exp (y ^ τ) ≤ C * Real.exp (a * y / 6) := by
  have h1 := nthr_rpow_le_eventually 1 (a := a / 12) (by positivity) hτ
  have h2 := (tendsto_exp_mul_div_rpow_atTop (n:ℝ) (a/12) (by positivity)).eventually
    (eventually_ge_atTop C⁻¹)
  filter_upwards [h1, h2, eventually_gt_atTop 0] with y hy1 hy2 hy0
  have hn : y ^ (n:ℝ) = y ^ n := Real.rpow_natCast y n
  rw [hn] at hy2
  have hp : 0 < y ^ n := by positivity
  rw [le_div_iff₀ hp] at hy2
  have hy3 : y ^ n ≤ C * Real.exp (a / 12 * y) := by
    have := mul_le_mul_of_nonneg_left hy2 hC.le
    rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at this
    linarith
  have hy4 : Real.exp (y ^ τ) ≤ Real.exp (a / 12 * y) :=
    Real.exp_le_exp.2 (by linarith)
  calc y ^ n * Real.exp (y ^ τ) ≤ (C * Real.exp (a / 12 * y)) * Real.exp (a / 12 * y) := by
        gcongr
    _ = C * Real.exp (a * y / 6) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The six comparisons for abstract constants, with `κ` standing for `(k : ℝ)`. -/
theorem nthr_key (c : PartialConstants) (κ : ℝ) (hn : 2 ≤ c.n) (hρ : 0 < c.ρ) (hg : 0 < c.g)
    (hm : 0 < c.m) (hMc : 0 < c.Mc) :
    ∃ μ0 : ℝ, 0 < μ0 ∧ ∀ μ : ℝ, 0 < μ → μ < μ0 →
      c.eps μ ≤ c.eps0 ∧ c.d μ ≤ c.ρ ∧ 6 ≤ c.kappa μ ∧
      256*κ*c.ρ*c.R0/(c.d μ)^2 ≤ c.K μ ∧ c.R0/(2*c.K μ) ≤ c.d μ/2 ∧
      μ⁻¹*Real.exp (μ^(-partialTimeExponent c.n)) ≤ c.blockTime μ := by
  obtain ⟨hs, hm1, hM1, hr0, hA, he0, hR0, hκC, hcK⟩ := c.nthr_pos hρ hg hm hMc
  obtain ⟨hT, hTD, hD2⟩ := exponents hn
  set T := partialTimeExponent c.n with hTdef
  set D := partialDriftExponent c.n with hDdef
  have hn0 : (0:ℝ) < c.n := by exact_mod_cast (by omega : 0 < c.n)
  set E : ℝ := 1/(2*(c.n:ℝ)) with hEdef
  have hE : 0 < E := by positivity
  have hD : 0 < D := hT.trans hTD
  have hsq : 0 < Real.sqrt c.n := Real.sqrt_pos.2 hn0
  set c1 : ℝ := 2*Real.pi*c.cK*c.s/Real.sqrt c.n with hc1
  have hc1p : 0 < c1 := by positivity
  set C0 : ℝ := c.s*c.m1*c.r0*(2*Real.pi)/(240*c.M1*c.kappaC*(c.A*c.cK)^c.n) with hC0
  have hC0p : 0 < C0 := by positivity
  have h1 : ∀ᶠ μ : ℝ in 𝓝[>] 0, μ < c.eps0 * (2*Real.pi) / c.kappaC :=
    by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < c.eps0 * (2*Real.pi) / c.kappaC by positivity)]
      with μ h using h.2
  have h2 : ∀ᶠ μ : ℝ in 𝓝[>] 0, μ < c.ρ ^ (1/D) :=
    by
    filter_upwards [Ioo_mem_nhdsGT (Real.rpow_pos_of_pos hρ (1/D))] with μ h using h.2
  have hy : ∀ᶠ y : ℝ in atTop, 0 < y ∧ 6 ≤ c1 * y ∧ 256*κ*c.ρ*c.R0 * y ^ (2*(D/E)) ≤ c.cK * y ∧
      c.R0 * y ^ (D/E) ≤ c.cK * y ∧
      y ^ c.n * Real.exp (y ^ (T/E)) ≤ C0 * Real.exp (c1 * y / 6) := by
    have hδ1 : D / E < 1 := by
      rw [div_lt_one hE]; rw [hEdef] at hD2 ⊢; linarith
    have hδ2 : 2 * (D / E) < 1 := by
      rw [← mul_div_assoc, div_lt_one hE]; exact hD2
    have hτ : T / E < 1 := by rw [div_lt_one hE]; rw [hEdef] at hD2 ⊢; linarith
    filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (6 / c1),
      nthr_rpow_le_eventually (256*κ*c.ρ*c.R0) hcK hδ2, nthr_rpow_le_eventually c.R0 hcK hδ1,
      nthr_exp_eventually c.n hC0p hc1p hτ] with y hy0 hy1 hy2 hy3 hy4
    exact ⟨hy0, by rwa [div_le_iff₀ hc1p, mul_comm] at hy1, hy2, hy3, hy4⟩
  have hy' := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hE)).eventually hy
  have hall := (h1.and (h2.and (hy'.and self_mem_nhdsWithin)))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  refine ⟨u, hu, fun μ hμ hμu => ?_⟩
  obtain ⟨hμ1, hμ2, ⟨-, hk6, hk4, hk5, hk6'⟩, -⟩ := hsub ⟨hμ, hμu⟩
  set y : ℝ := μ ^ (-E) with hydef
  have hy0 : 0 < y := Real.rpow_pos_of_pos hμ _
  have hK : c.K μ = c.cK * y := c.nthr_K_eq hκC he0 hμ
  have hdy : c.d μ = y ^ (-(D/E)) := by
    rw [hydef, ← Real.rpow_mul hμ.le]; show μ ^ D = _
    congr 1; field_simp
  have hkap : c.kappa μ = c1 * y := by
    unfold PartialConstants.kappa; rw [hK, hc1]; field_simp
  have hτ' : μ ^ (-T) = y ^ (T/E) := by
    rw [hydef, ← Real.rpow_mul hμ.le]; congr 1; field_simp
  have hyp : 0 < y ^ (D/E) := Real.rpow_pos_of_pos hy0 _
  have hbt : c.blockTime μ = C0 * Real.exp (c1 * y / 6) / (y ^ c.n * μ) := by
    unfold PartialConstants.blockTime PartialConstants.rTheta PartialConstants.eps
    rw [hkap, hK, hC0, show (c.A * (c.cK * y)) ^ c.n = (c.A * c.cK) ^ c.n * y ^ c.n by
      rw [← mul_assoc, mul_pow]]
    field_simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hκC] at hμ1
    unfold PartialConstants.eps; rw [div_le_iff₀ (by positivity)]; nlinarith
  · have := Real.rpow_le_rpow hμ.le hμ2.le hD.le
    rwa [← Real.rpow_mul hρ.le, one_div_mul_cancel hD.ne', Real.rpow_one] at this
  · rw [hkap]; exact hk6
  · have hd2 : (c.d μ) ^ 2 = (y ^ (2 * (D/E)))⁻¹ := by
      rw [hdy, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le, ← Real.rpow_neg hy0.le]
      congr 1; push_cast; ring
    rw [hd2, div_inv_eq_mul, hK]; exact hk4
  · rw [hdy, Real.rpow_neg hy0.le, hK, div_le_iff₀ (by positivity)]
    have h := (le_div_iff₀ hyp).2 hk5
    have e : (y ^ (D/E))⁻¹ / 2 * (2 * (c.cK * y)) = c.cK * y / y ^ (D/E) := by
      field_simp
    rw [e]; exact h
  · rw [hbt, hτ', le_div_iff₀ (by positivity)]
    have e : μ⁻¹ * Real.exp (y ^ (T/E)) * (y ^ c.n * μ) = y ^ c.n * Real.exp (y ^ (T/E)) := by
      field_simp
    rw [e]; exact hk6'

/-- N11-O: all constants are fixed before `μ`; six comparisons hold for all small `μ`. -/
theorem threshold (a : PartialData n k) (hne : a.G.Nonempty) :
    ∃ μ0 : ℝ, 0 < μ0 ∧ ∀ μ : ℝ, 0 < μ → μ < μ0 →
      let c := constants a
      c.eps μ ≤ c.eps0 ∧ c.d μ ≤ a.ρ ∧ 6 ≤ c.kappa μ ∧
      256*k*a.ρ*c.R0/(c.d μ)^2 ≤ c.K μ ∧ c.R0/(2*c.K μ) ≤ c.d μ/2 ∧
      μ⁻¹*Real.exp (μ^(-partialTimeExponent n)) ≤ c.blockTime μ := by
  obtain ⟨hg, hm, -⟩ := a.definite
  exact nthr_key (constants a) (k:ℝ) a.hn a.hρ hg hm a.hMc

end KAM.Nekhoroshev
end
