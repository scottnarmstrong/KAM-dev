/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Freq.SmallDivisorFiber
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The tail of the small-divisor series at any Diophantine exponent, over `ℚ`

`KAM.CertificateSharp.SdsData` bounds the tail `T_N` at `τ = 1` only (`SdsData.tailBound`,
`sds_tail_le`), and `sdsFiberBound_sound` asks for a `(γ, 1)`-Diophantine `(ω', 1)`, a premise that
no vector of `ℝ³` satisfies (Dirichlet). The real bound `KAM.sdTail_le` holds at every `τ`; this
module is its rational form at `τ ∈ ℕ`, with any upper bound `E' ≥ e^{-2πδ(N+1)}`:

* `cLoQ δ τ N = 6.28 δ - 2τ/(N + 1)`, `tailQ γ δ τ N E' = 2(1 + 2^τ) γ⁻² (6.3 δ) (N+1)^{2τ} E'
  (1 + c_lo⁻¹)`; at `τ = 1`, `E' = E₁^{N+1}` this is `SdsData.tailBound`;
* `sdTail_le_tailQ`: `2τ < 2πδ(N + 1)` and `T_N ≤ tailQ`;
* `expLowQ δ J`, the Taylor polynomial of `e^{6.28 δ}`, and `exp_neg_le_of_expLowQ`:
  `1 ≤ x · expLowQ δ J` gives `e^{-2πδ} ≤ x`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Fiber

open KAM KAM.Certificate KAM.CertificateSharp

/-- The Taylor polynomial of degree `J` of `e^{6.28 δ}` (`SdsData.expLow`). -/
def expLowQ (δ : ℚ) (J : ℕ) : ℚ :=
  ({ box := [], γ := 0, δ := δ, N := 0, J := J, E1 := 0 } : SdsData).expLow

/-- `1 ≤ x · expLowQ δ J` gives `e^{-2πδ} ≤ x`. -/
theorem exp_neg_le_of_expLowQ {δ x : ℚ} {J : ℕ} (hδ : 0 < δ) (h : 1 ≤ x * expLowQ δ J) :
    Real.exp (-(2 * Real.pi * δ)) ≤ (x : ℝ) :=
  exp_neg_le_E1 ({ box := [], γ := 0, δ := δ, N := 0, J := J, E1 := x } : SdsData)
    (by exact_mod_cast hδ) h

/-- The lower bound `c_lo = 6.28 δ - 2τ/(N + 1)` of `2πδ - 2τ/(N + 1)`. -/
def cLoQ (δ : ℚ) (τ N : ℕ) : ℚ := 628 / 100 * δ - 2 * τ / (N + 1)

/-- The rational bound of the tail `T_N` at the exponent `τ`, from `E' ≥ e^{-2πδ(N+1)}`. -/
def tailQ (γ δ : ℚ) (τ N : ℕ) (Ep : ℚ) : ℚ :=
  2 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ * (63 / 10 * δ) * (((N : ℚ) + 1) ^ (2 * τ) * Ep) *
    (1 + (cLoQ δ τ N)⁻¹)

/-- **The tail at the exponent `τ`.** -/
theorem sdTail_le_tailQ {γ δ Ep : ℚ} {τ N : ℕ} (hδ : 0 < δ) (hc : 0 < cLoQ δ τ N)
    (hEp : Real.exp (-(2 * Real.pi * δ) * (N + 1)) ≤ (Ep : ℝ)) :
    2 * (τ : ℝ) < 2 * Real.pi * δ * (N + 1) ∧ sdTail (γ : ℝ) τ δ N ≤ (tailQ γ δ τ N Ep : ℝ) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hcLo : (0 : ℝ) < 628 / 100 * δ - 2 * τ / ((N : ℝ) + 1) := by
    have : (0 : ℝ) < ((cLoQ δ τ N : ℚ) : ℝ) := by exact_mod_cast hc
    unfold cLoQ at this
    push_cast at this
    exact this
  have hN : 2 * (τ : ℝ) < 2 * Real.pi * δ * (N + 1) := by
    have h1 : 2 * τ / ((N : ℝ) + 1) < 628 / 100 * δ := by linarith
    rw [div_lt_iff₀ hN1] at h1
    nlinarith
  refine ⟨hN, (sdTail_le (γ := γ) (τ := τ) hδ' hN hEp).trans ?_⟩
  have hE0 : (0 : ℝ) ≤ Ep := (Real.exp_pos _).le.trans hEp
  unfold tailQ cLoQ
  push_cast
  set c : ℝ := 2 * Real.pi * δ - 2 * τ / ((N : ℝ) + 1) with hcdef
  have hcge : (628 / 100 * (δ : ℝ) - 2 * τ / ((N : ℝ) + 1)) ≤ c := by
    rw [hcdef]; nlinarith
  have hc0 : 0 < c := lt_of_lt_of_le hcLo hcge
  have hfrac : (1 + c) / c ≤ 1 + (628 / 100 * (δ : ℝ) - 2 * τ / ((N : ℝ) + 1))⁻¹ := by
    rw [add_div, div_self hc0.ne', ← one_div, add_comm]
    gcongr
  have hfr0 : 0 ≤ (1 + c) / c := div_nonneg (by linarith) hc0.le
  have hpow : ((N : ℝ) + 1) ^ (2 * (τ : ℝ)) = ((N : ℝ) + 1) ^ (2 * τ) := by
    rw [show (2 * (τ : ℝ)) = ((2 * τ : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ (τ : ℝ) = (2 : ℝ) ^ τ := Real.rpow_natCast _ _
  rw [hpow, h2]
  have hb : 2 * Real.pi * δ ≤ 63 / 10 * δ := by nlinarith
  have hP : 0 ≤ ((N : ℝ) + 1) ^ (2 * τ) * (Ep : ℝ) := by positivity
  have hC : (0 : ℝ) ≤ 2 * (1 + 2 ^ τ) * ((γ : ℝ) ^ 2)⁻¹ := by positivity
  calc 2 * (1 + 2 ^ τ) * ((γ : ℝ) ^ 2)⁻¹ * (2 * Real.pi * δ) *
        (((N : ℝ) + 1) ^ (2 * τ) * Ep) * ((1 + c) / c)
      ≤ 2 * (1 + 2 ^ τ) * ((γ : ℝ) ^ 2)⁻¹ * (63 / 10 * δ) *
          (((N : ℝ) + 1) ^ (2 * τ) * Ep) * ((1 + c) / c) := by
        refine mul_le_mul_of_nonneg_right ?_ hfr0
        refine mul_le_mul_of_nonneg_right ?_ hP
        exact mul_le_mul_of_nonneg_left hb hC
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left hfrac ?_
        have : (0 : ℝ) ≤ 63 / 10 * δ := by positivity
        positivity

end KAM.CertificateSharp.Fiber

end
