/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.Analysis.RealAlgebra
public import KAM.Wave.Algebra.Extension
public import KAM.Wave.Normal.Analysis.EllSeq

/-!
# Even majorants of one-sided sequences (blueprint `bpW:w0n:cubic-bound`, `stepW:w0n:majorant`)

Infrastructure used by several nodes; the dependency graph is still being built.

For `f : ℕ+ → ℝ` the even two-sided majorant is `x_i = |f_{|i|}|` for `i ≠ 0`, `x_0 = 0`
(`KAM.Wave.waveEvenAbs`). Its two-sided weighted norm is `√2` times the one-sided one
(`KAM.Wave.hasSum_waveEvenAbs_weighted_sq`), and convolutions of even sequences are even
(`KAM.Wave.waveConv_even`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The even majorant `x_i = |f_{|i|}|` (`i ≠ 0`), `x_0 = 0`. -/
def waveEvenAbs (f : ℕ+ → ℝ) (i : ℤ) : ℝ :=
  if i = 0 then 0 else |f (Int.natAbs i).toPNat'|

lemma waveEvenAbs_nonneg (f : ℕ+ → ℝ) (i : ℤ) : 0 ≤ waveEvenAbs f i := by
  unfold waveEvenAbs; split_ifs <;> positivity

lemma waveEvenAbs_zero (f : ℕ+ → ℝ) : waveEvenAbs f 0 = 0 := by simp [waveEvenAbs]

lemma waveEvenAbs_neg (f : ℕ+ → ℝ) (i : ℤ) : waveEvenAbs f (-i) = waveEvenAbs f i := by
  simp [waveEvenAbs]

lemma waveEvenAbs_pnat (f : ℕ+ → ℝ) (n : ℕ+) : waveEvenAbs f ((n : ℕ) : ℤ) = |f n| := by
  have hn : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simp only [waveEvenAbs, hn, ite_false, Int.natAbs_natCast]
  congr 2
  exact PNat.coe_injective (by simp)

lemma w0a_conv_even {X Y : ℤ → ℝ} (hX : ∀ i, X (-i) = X i) (hY : ∀ i, Y (-i) = Y i) (l : ℤ) :
    waveConv X Y (-l) = waveConv X Y l := by
  unfold waveConv
  rw [← (Equiv.neg ℤ).tsum_eq (fun i => X i * Y (l - i))]
  refine tsum_congr fun i => ?_
  simp only [Equiv.neg_apply]
  have : l - -i = -(-l - i) := by ring
  rw [this, hY, hX]

/-- Sums over `ℤ` of an even function. -/
lemma w0aHasSum_int_even_pnat' {f : ℤ → ℝ} (hev : ∀ i, f (-i) = f i) {S : ℝ}
    (hS : HasSum (fun n : ℕ+ => f ((n : ℕ) : ℤ)) S) : HasSum f (f 0 + 2 * S) := by
  have h1 : HasSum (fun n : ℕ => f ((n : ℤ) + 1)) S := by
    have := (Equiv.pnatEquivNat.symm.hasSum_iff (f := fun n : ℕ+ => f ((n : ℕ) : ℤ))).2 hS
    convert this using 1
    funext n
    simp [Equiv.pnatEquivNat_symm_apply]
  exact w0aHasSum_int_even hev h1

/-- Sums over `ℤ` of an even function vanishing at `0`. -/
lemma w0aHasSum_int_even_pnat {f : ℤ → ℝ} (hev : ∀ i, f (-i) = f i) (h0 : f 0 = 0) {S : ℝ}
    (hS : HasSum (fun n : ℕ+ => f ((n : ℕ) : ℤ)) S) : HasSum f (2 * S) := by
  simpa [h0] using w0aHasSum_int_even_pnat' hev hS

end KAM.Wave

end
