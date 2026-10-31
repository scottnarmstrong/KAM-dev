/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Majorant

/-!
# Folded sequences of a point of `𝔚` (blueprint-W `bpW:w3:quartic`, Step Majorize)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is still
being built. Package W3-SETTING.

For `y ∈ 𝔚` (weighted coordinates) the sequence `u_i = |w_i| + |w_{-i}|` (`birkFoldNorm a p y`,
`w = birkCoord a p y`) lies in `ℓ^{a,p}` and `‖u‖_{a,p} ≤ √2 ‖y‖` (`isEll_birkFoldNorm`,
`ellTsumNorm_birkFoldNorm_le`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- `u_i = |w_i| + |w_{-i}|` for `w = birkCoord a p y`. -/
def birkFoldNorm (a p : ℝ) (y : BirkSpace) : ℕ+ → ℝ :=
  birkFold (fun l => ‖birkCoord a p y l‖)

theorem birkFoldNorm_nonneg (a p : ℝ) (y : BirkSpace) (i : ℕ+) : 0 ≤ birkFoldNorm a p y i := by
  unfold birkFoldNorm birkFold; positivity

theorem ellWeight_mul_norm_birkCoord (a p : ℝ) (y : BirkSpace) (l : BirkIdx) :
    ellWeight a p l.2 * ‖birkCoord a p y l‖ = ‖y l‖ := by
  rw [birkCoord, norm_div, norm_ellWeight_cast]
  have := ellWeight_pos a p l.2
  field_simp

theorem ellWeight_mul_birkFoldNorm (a p : ℝ) (y : BirkSpace) (i : ℕ+) :
    ellWeight a p i * birkFoldNorm a p y i = ‖y (true, i)‖ + ‖y (false, i)‖ := by
  unfold birkFoldNorm birkFold
  rw [mul_add, ellWeight_mul_norm_birkCoord a p y (true, i),
    ellWeight_mul_norm_birkCoord a p y (false, i)]

theorem summable_sq_birkFoldNorm (a p : ℝ) (y : BirkSpace) :
    Summable fun i : ℕ+ => (ellWeight a p i * ‖birkFoldNorm a p y i‖) ^ 2 := by
  have hb := (birk_summable_iff (fun l => by positivity)).1 (lp_two_hasSum_sq y).summable
  have hg := hb.1.add hb.2
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun i => ?_) (hg.mul_left 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (birkFoldNorm_nonneg a p y i), ellWeight_mul_birkFoldNorm]
  nlinarith [sq_nonneg (‖y (true, i)‖ - ‖y (false, i)‖)]

/-- `u ∈ ℓ^{a,p}`. -/
theorem isEll_birkFoldNorm (a p : ℝ) (y : BirkSpace) : IsEll a p (birkFoldNorm a p y) :=
  (wave_isEll_iff_summable a p _).2 (summable_sq_birkFoldNorm a p y)

/-- `‖u‖_{a,p} ≤ √2 ‖y‖`. -/
theorem ellTsumNorm_birkFoldNorm_le (a p : ℝ) (y : BirkSpace) :
    ellTsumNorm a p (birkFoldNorm a p y) ≤ Real.sqrt 2 * ‖y‖ := by
  rw [wave_ellTsumNorm_eq]
  have h := birk_hasSum_sq_pair y
  have hb := (birk_summable_iff (fun l => by positivity)).1 (lp_two_hasSum_sq y).summable
  have hle : ∑' i : ℕ+, (ellWeight a p i * ‖birkFoldNorm a p y i‖) ^ 2 ≤ 2 * ‖y‖ ^ 2 := by
    rw [← h.tsum_eq, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_) (summable_sq_birkFoldNorm a p y)
      ((hb.1.add hb.2).mul_left 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (birkFoldNorm_nonneg a p y i), ellWeight_mul_birkFoldNorm]
    nlinarith [sq_nonneg (‖y (true, i)‖ - ‖y (false, i)‖)]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  exact hle

end KAM.Wave

end
