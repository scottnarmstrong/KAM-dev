/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Algebra.Algebra
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Real nonnegative specializations of the landed convolution algebra
(blueprint `bpW:w0n:algebra`, used by `bpW:w0n:cubic-bound`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

Bridges from the landed complex statements of `KAM.Wave.Algebra` (`wave_algebra`, `waveConv`,
`waveTwoWeight`, `waveAlgConst`) to real nonnegative sequences: `KAM.Wave.w0a_convAlgebra_nonneg`
and `KAM.Wave.w0a_summable_of_weighted`, plus two small helpers on even sums over `ℤ`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The `ℓ²(ℤ)` norm `(Σ_i X_i²)^{1/2}` of a real sequence (junk off `ℓ²`). -/
def w0aL2 (X : ℤ → ℝ) : ℝ := Real.sqrt (∑' i : ℤ, X i ^ 2)

lemma w0a_twoWeight_neg (a s : ℝ) (i : ℤ) : waveTwoWeight a s (-i) = waveTwoWeight a s i := by
  simp [waveTwoWeight, waveJap]

/-- `Σ_{i ∈ ℤ} f i` for an even `f` is `f 0 + 2 Σ_{n ≥ 1} f n`. -/
lemma w0aHasSum_int_even {f : ℤ → ℝ} (hev : ∀ i, f (-i) = f i) {S : ℝ}
    (hS : HasSum (fun n : ℕ => f ((n : ℤ) + 1)) S) : HasSum f (f 0 + 2 * S) := by
  have h1 : HasSum (fun n : ℕ => f (n : ℤ)) (f 0 + S) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using hS
  have h2 : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) S := by
    simpa only [hev] using hS
  have := h1.of_nat_of_neg_add_one h2
  convert this using 1
  ring

lemma w0a_twoMem_ofReal {a s : ℝ} {X : ℤ → ℝ} (hX0 : ∀ i, 0 ≤ X i) :
    WaveTwoMem a s (fun i => (X i : ℂ)) ↔ Summable fun i => (waveTwoWeight a s i * X i) ^ 2 := by
  unfold WaveTwoMem
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hX0 _)]

lemma w0a_twoNorm_ofReal (a s : ℝ) {X : ℤ → ℝ} (hX0 : ∀ i, 0 ≤ X i) :
    waveTwoNorm a s (fun i => (X i : ℂ)) = w0aL2 (fun i => waveTwoWeight a s i * X i) := by
  unfold waveTwoNorm w0aL2
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hX0 _)]

lemma w0a_conv_ofReal (X Y : ℤ → ℝ) :
    waveConv (fun i => (X i : ℂ)) (fun i => (Y i : ℂ)) =
      fun l => ((waveConv X Y l : ℝ) : ℂ) := by
  funext l
  simp [waveConv, Complex.ofReal_tsum]

/-- The convolution algebra inequality of `bpW:w0n:algebra` for nonnegative real sequences. -/
theorem w0a_convAlgebra_nonneg {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {X Y : ℤ → ℝ}
    (hX0 : ∀ i, 0 ≤ X i) (hY0 : ∀ i, 0 ≤ Y i)
    (hX : Summable fun i => (waveTwoWeight a s i * X i) ^ 2)
    (hY : Summable fun i => (waveTwoWeight a s i * Y i) ^ 2) :
    Summable (fun l => (waveTwoWeight a s l * waveConv X Y l) ^ 2) ∧
      w0aL2 (fun l => waveTwoWeight a s l * waveConv X Y l) ≤
        waveAlgConst s * w0aL2 (fun i => waveTwoWeight a s i * X i) *
          w0aL2 (fun i => waveTwoWeight a s i * Y i) := by
  have hnn : ∀ l, 0 ≤ waveConv X Y l := fun l =>
    tsum_nonneg fun i => mul_nonneg (hX0 _) (hY0 _)
  obtain ⟨-, hmem, hnorm⟩ := wave_algebra ha hs ((w0a_twoMem_ofReal hX0).2 hX)
    ((w0a_twoMem_ofReal hY0).2 hY)
  rw [w0a_conv_ofReal] at hmem hnorm
  rw [w0a_twoNorm_ofReal a s hnn, w0a_twoNorm_ofReal a s hX0, w0a_twoNorm_ofReal a s hY0] at hnorm
  exact ⟨(w0a_twoMem_ofReal hnn).1 hmem, hnorm⟩

/-- A nonnegative sequence of `ℓ^{a,s}_b`, `s ≥ 1`, is summable. -/
lemma w0a_summable_of_weighted {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {x : ℤ → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx : Summable fun i => (waveTwoWeight a s i * x i) ^ 2) :
    Summable x := by
  have := (wave_l1_le_of_mem ha (by linarith) ((w0a_twoMem_ofReal hx0).2 hx)).1
  simpa [Complex.norm_real, abs_of_nonneg (hx0 _)] using this

end KAM.Wave

end
