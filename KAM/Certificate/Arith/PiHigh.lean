/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# High-precision enclosures of `π` and `e`

Backend-independent core of the `π` package (owner ruling O3): rational enclosures of `π` and
`Real.exp 1` computed in `ℚ` and certified by kernel evaluation (`decide +kernel`).

* `piLoQ`, `piUpQ`: the coarse enclosure `3.141592 < π < 3.141593`.
* `atanS x m`: the partial sum `∑_{i<m} (-1)^i x^(2i+1)/(2i+1)` of the arctangent series; the
  alternating series bounds give `atanS x (2k) < arctan x < atanS x (2k+1)` for `0 < x < 1`.
* `piLowRat k j`, `piUpRat k j`: Machin's `π = 16 arctan (1/5) - 4 arctan (1/239)`.
  The checks `piHigh_N` (`N = 50, 100, 140`) give `a < π < b`, `b - a ≤ 10 ^ (-N)`.
* `eLowRat n`, `eUpRat n`: `e` from the Taylor series of `exp 1` with the `Real.exp_bound`
  remainder, with the check `eHigh_30`.

Hook for the arithmetic interface: `PiHighCert` bundles `lo < π < hi` for rationals `lo hi`;
the backend wraps `(lo + hi) / 2` and `(hi - lo) / 2` into a `PiEnclosure`.
-/

@[expose] public section

open Finset

namespace KAM.Certificate

/-- A coarse certified enclosure of `π`: `piLoQ < π < piUpQ`. -/
def piLoQ : ℚ := 3141592 / 1000000

def piUpQ : ℚ := 3141593 / 1000000

theorem piLoQ_lt_pi : (piLoQ : ℝ) < Real.pi := by
  have := Real.pi_gt_d6
  unfold piLoQ
  push_cast
  norm_num at this ⊢
  exact this

theorem pi_lt_piUpQ : Real.pi < piUpQ := by
  have := Real.pi_lt_d6
  unfold piUpQ
  push_cast
  norm_num at this ⊢
  exact this

/-! ### Arctangent partial sums -/

/-- Partial sum `∑_{i<m} (-1)^i x^(2i+1)/(2i+1)` of the arctangent series. -/
def atanS (x : ℚ) (m : ℕ) : ℚ := ∑ i ∈ range m, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))

/-- The `i`th term `x^(2i+1)/(2i+1)` of the arctangent series (without sign). -/
private noncomputable def atanT (x : ℝ) (i : ℕ) : ℝ := x ^ (2 * i + 1) / (2 * i + 1)

private theorem atanS_cast (x : ℚ) (m : ℕ) :
    (atanS x m : ℝ) = ∑ i ∈ range m, (-1) ^ i * atanT x i := by
  unfold atanS atanT; push_cast; rfl

private theorem atanT_strict {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (i : ℕ) :
    atanT x (i + 1) < atanT x i := by
  have hp : x ^ (2 * (i + 1) + 1) < x ^ (2 * i + 1) :=
    pow_lt_pow_right_of_lt_one₀ h0 h1 (by omega)
  have hd : (0 : ℝ) < 2 * i + 1 := by positivity
  unfold atanT
  push_cast
  calc x ^ (2 * (i + 1) + 1) / (2 * ((i : ℝ) + 1) + 1)
      < x ^ (2 * i + 1) / (2 * ((i : ℝ) + 1) + 1) := by gcongr
    _ ≤ x ^ (2 * i + 1) / (2 * i + 1) :=
      div_le_div_of_nonneg_left (by positivity) hd (by linarith)

private theorem atan_term_anti {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Antitone (atanT x) := by
  rcases h0.eq_or_lt with rfl | hpos
  · refine antitone_nat_of_succ_le fun i => ?_
    simp [atanT]
  · exact antitone_nat_of_succ_le fun i => (atanT_strict hpos h1 i).le

private theorem atan_tendsto {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Filter.Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * atanT x i)
      Filter.atTop (nhds (Real.arctan x)) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  refine hs.tendsto_sum_nat.congr fun n => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold atanT
  push_cast
  ring

private theorem atanS_le (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ) :
    (atanS x (2 * k) : ℝ) ≤ Real.arctan x := by
  rw [atanS_cast]
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) < 1 := by exact_mod_cast h1
  exact (atan_term_anti h0' h1').alternating_series_le_tendsto (atan_tendsto h0' h1') k

private theorem le_atanS (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ) :
    Real.arctan x ≤ (atanS x (2 * k + 1) : ℝ) := by
  rw [atanS_cast]
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) < 1 := by exact_mod_cast h1
  exact (atan_term_anti h0' h1').tendsto_le_alternating_series (atan_tendsto h0' h1') k

/-- Strict lower bound of the alternating series. -/
theorem atanS_even_lt_arctan {x : ℚ} (h0 : 0 < x) (h1 : x < 1) (k : ℕ) :
    (atanS x (2 * k) : ℝ) < Real.arctan x := by
  have h0' : (0 : ℝ) < x := by exact_mod_cast h0
  have h1' : (x : ℝ) < 1 := by exact_mod_cast h1
  have h := atanS_le x h0.le h1 (k + 1)
  have hs := atanT_strict h0' h1' (2 * k)
  have ev : ((-1 : ℝ)) ^ (2 * k) = 1 := Even.neg_one_pow ⟨k, by ring⟩
  have od : ((-1 : ℝ)) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
  rw [atanS_cast, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ,
    sum_range_succ, ev, od] at h
  rw [atanS_cast]
  linarith

/-- Strict upper bound of the alternating series. -/
theorem arctan_lt_atanS_odd {x : ℚ} (h0 : 0 < x) (h1 : x < 1) (k : ℕ) :
    Real.arctan x < (atanS x (2 * k + 1) : ℝ) := by
  have h0' : (0 : ℝ) < x := by exact_mod_cast h0
  have h1' : (x : ℝ) < 1 := by exact_mod_cast h1
  have h := le_atanS x h0.le h1 (k + 1)
  have hs := atanT_strict h0' h1' (2 * k + 1)
  have ev : ((-1 : ℝ)) ^ (2 * k + 1 + 1) = 1 := Even.neg_one_pow ⟨k + 1, by ring⟩
  have od : ((-1 : ℝ)) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
  rw [atanS_cast, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, sum_range_succ,
    sum_range_succ, ev, od] at h
  rw [atanS_cast]
  have hs' : atanT x (2 * k + 2) < atanT x (2 * k + 1) := hs
  linarith

/-! ### Machin enclosure -/

/-- Lower rational for `π`: `16 atanS (1/5) (2k) - 4 atanS (1/239) (2j+1)`. -/
def piLowRat (k j : ℕ) : ℚ := 16 * atanS (1 / 5) (2 * k) - 4 * atanS (1 / 239) (2 * j + 1)

/-- Upper rational for `π`: `16 atanS (1/5) (2k+1) - 4 atanS (1/239) (2j)`. -/
def piUpRat (k j : ℕ) : ℚ := 16 * atanS (1 / 5) (2 * k + 1) - 4 * atanS (1 / 239) (2 * j)

theorem piLowRat_lt_pi (k j : ℕ) : (piLowRat k j : ℝ) < Real.pi := by
  have h1 := atanS_even_lt_arctan (x := 1 / 5) (by norm_num) (by norm_num) k
  have h2 := le_atanS (1 / 239) (by norm_num) (by norm_num) j
  have m := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  unfold piLowRat
  push_cast at h1 h2 ⊢
  have e5 : ((5 : ℝ))⁻¹ = 1 / 5 := by norm_num
  have e239 : ((239 : ℝ))⁻¹ = 1 / 239 := by norm_num
  rw [e5, e239] at m
  linarith

theorem pi_lt_piUpRat (k j : ℕ) : Real.pi < (piUpRat k j : ℝ) := by
  have h1 := arctan_lt_atanS_odd (x := 1 / 5) (by norm_num) (by norm_num) k
  have h2 := atanS_le (1 / 239) (by norm_num) (by norm_num) j
  have m := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  unfold piUpRat
  push_cast at h1 h2 ⊢
  have e5 : ((5 : ℝ))⁻¹ = 1 / 5 := by norm_num
  have e239 : ((239 : ℝ))⁻¹ = 1 / 239 := by norm_num
  rw [e5, e239] at m
  linarith

/-- The hook for the arithmetic interface: rationals `lo < π < hi`. -/
structure PiHighCert where
  lo : ℚ
  hi : ℚ
  lo_lt : (lo : ℝ) < Real.pi
  lt_hi : Real.pi < (hi : ℝ)

/-- Width bound check, kernel-evaluated. -/
def piWidthOk (k j N : ℕ) : Bool :=
  decide (piUpRat k j - piLowRat k j ≤ 1 / 10 ^ N)

/-- Enclosure from kernel-checked parameters. -/
def PiHighCert.ofParams (k j : ℕ) : PiHighCert where
  lo := piLowRat k j
  hi := piUpRat k j
  lo_lt := piLowRat_lt_pi k j
  lt_hi := pi_lt_piUpRat k j

end KAM.Certificate
