/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperTubeMain
public import KAM.Planetary.Preparation.SlowSmall

/-!
# Asymptotic smallness for the wrapper (P11A-P10, `stepP:p11:wr-nu`)

Eventual (as `ε → 0⁺`) validity of the numerical hypotheses of `p11_wr_tube`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace KAM.Planetary

section Asym

variable {n : ℕ}

/-- Eventually `ε^a ℓ^b ≤ δ`. -/
theorem p11_ev_pow_log {a b δ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), eps^a*Real.log (1/eps)^b ≤ δ :=
  ((e4 ha hb).eventually (gt_mem_nhds hδ)).mono fun _ h => h.le

theorem p11_ev_lt {r : ℝ} (hr : 0 < r) : ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), eps < r :=
  eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hr)

/-- `hP1`, `hP2` of `p11_wr_tube` hold for small `ε`. -/
theorem p11_ev_slowDisp (c τ : ℝ) (hc : 0 ≤ c) (hτ : 0 ≤ τ) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), 0 < eps →
      c*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*τ+1) ≤ eps ∧
      c*eps^(5/2 : ℝ)*Real.log (1/eps)^(3*τ+1) ≤ eps := by
  filter_upwards [p11_ev_pow_log (a := 1/2) (b := 3*τ+1) (δ := 1/(c+1)) (by norm_num)
    (by linarith) (by positivity), p11_ev_lt one_pos] with eps h h1 heps
  have hℓ : 0 ≤ Real.log (1/eps)^(3*τ+1) := Real.rpow_nonneg (by
    rw [one_div, Real.log_inv]
    have := Real.log_nonpos heps.le h1.le
    linarith) _
  have e1 : eps^(3/2 : ℝ) = eps*eps^(1/2 : ℝ) := by
    rw [← Real.rpow_one_add' heps.le (by norm_num)]; norm_num
  have hkey : c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*τ+1) ≤ 1 := by
    have h2 : c*(eps^(1/2 : ℝ)*Real.log (1/eps)^(3*τ+1)) ≤ c*(1/(c+1)) :=
      mul_le_mul_of_nonneg_left h hc
    calc c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*τ+1) = c*(eps^(1/2 : ℝ)*_) := by ring
      _ ≤ c*(1/(c+1)) := h2
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
  have hP1 : c*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*τ+1) ≤ eps := by
    rw [e1]
    calc c*(eps*eps^(1/2 : ℝ))*Real.log (1/eps)^(3*τ+1) =
        eps*(c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*τ+1)) := by ring
      _ ≤ eps*1 := mul_le_mul_of_nonneg_left hkey heps.le
      _ = eps := mul_one _
  refine ⟨hP1, le_trans ?_ hP1⟩
  have : eps^(5/2 : ℝ) ≤ eps^(3/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge heps h1.le (by norm_num)
  have h3 : 0 ≤ Real.log (1/eps)^(3*τ+1) := hℓ
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc) h3

end Asym

end KAM.Planetary

end
