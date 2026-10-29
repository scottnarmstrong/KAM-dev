/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverage
public import KAM.Planetary.Preparation.SlowConclude
public import KAM.Planetary.Preparation.SlowSmall
public import KAM.Planetary.Preparation.SlowCoeff
public import KAM.Planetary.Preparation.SlowMW

/-!
# Slow averaging: assembly of `avg_slow_of_spec` (P11A-P7d)

`avg_slow_of_spec`: for `C` with `P11SecularSpec D C`, `1 ≤ ν` and fast data satisfying
`P11FastSpec` for all small `ε`, there are `ε₂`, `c₂` such that `P11SlowSpecOf` holds for every
`ε ≤ ε₂`. P7b supplies `Ẑ, h₀, f₂` (`p11_slow_osc`), P7c the divisor clause and the
averaging step (`p11_slow_divisor`, `p11_slow_conclude`); the constant `c₂` dominates all the
explicit constants and `ε₂` is chosen by the eventual lemmas of `SlowSmall`/`SlowRates`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric Filter
open scoped BigOperators Topology
namespace KAM.Planetary

section Assembly

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- The eventual smallness conditions on `ε` used by the assembly. -/
theorem p11_slow_eventually (hC : P11SecularSpec D C) {nu c : ℝ} (hnu : 1 ≤ nu) (hc : 0 ≤ c) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), (0 < eps ∧ eps * C.MF ≤ Real.exp (-1) ∧
      eps ≤ Real.exp (-1) ∧ 3 * eps ≤ C.rz ^ 2 / 32) ∧ p11eta1 C eps ≤ 1 ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) → Real.pi * eps ≤ p11s2 C nu eps) ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) →
        p11K2 C nu eps * (c * (eps + p11eta1 C eps)) ≤
          C.gamma * p11K2 C nu eps ^ (-C.tau) / 8) ∧
      (0 < eps → eps * C.MF ≤ Real.exp (-1) →
        eps * p11K2 C nu eps * p11SlowMW C ≤ C.gamma * p11K2 C nu eps ^ (-C.tau) / 2 *
          min (p11s1 C eps / 4) (Real.pi * C.rz ^ 2 / 32)) ∧
      c * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * C.tau + 1) ≤
        (eps * (C.gamma / 4 * (3 * nu / (Real.pi * (C.sigma / 12)) * Real.log (1 / eps)) ^
          (-C.tau))) * Real.pi * eps / (128 * (3 * nu / (Real.pi * (C.sigma / 12)) *
          Real.log (1 / eps))) := by
  obtain ⟨hγ0, hτ0, -, -, -, hσ0, -, -, -, -⟩ := fast_consts hC
  obtain ⟨cη, eps1, heps1, hη⟩ := p11eta1_source_rate hC
  have hπ := Real.pi_pos
  have hnu0 : 0 < nu := by linarith
  have ha : 0 < 3 * nu / (Real.pi * (C.sigma / 12)) := by positivity
  have hη1 : ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), p11eta1 C eps ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT heps1, Ioo_mem_nhdsGT (Real.exp_pos (-1)),
      eventually_eps_log_le (m := 2 * C.tau + 1) (by linarith) (show 0 < 1 / (|cη| + 1) by
        positivity)] with eps h0 h0' h2
    have hl1 := log_inv_ge_one h0.1 h0'.2.le
    have hl : 0 ≤ eps * Real.log (1 / eps) ^ (2 * C.tau + 1) :=
      mul_nonneg h0.1.le (Real.rpow_nonneg (by linarith) _)
    have h3 : cη * eps * Real.log (1 / eps) ^ (2 * C.tau + 1) ≤ |cη| *
        (eps * Real.log (1 / eps) ^ (2 * C.tau + 1)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self cη) hl
    refine (hη eps h0.1 h0.2.le).trans (h3.trans ?_)
    calc |cη| * (eps * Real.log (1 / eps) ^ (2 * C.tau + 1)) ≤ |cη| * (1 / (|cη| + 1)) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith
  filter_upwards [slow_base_eventually hC, hη1, slow_pe_eventually hC hnu,
    slow_cz_eventually hC hnu hc, slow_R_eventually hC hnu (p11SlowMW_nonneg hC),
    slow_b2_eventually c ha hγ0 hτ0.le] with eps h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Assembly

end KAM.Planetary

end
