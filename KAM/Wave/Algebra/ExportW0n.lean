/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Algebra.Algebra
public import KAM.Wave.Normal.Analysis.CubicHeadline
import Mathlib.Tactic.FieldSimp

/-!
# The weighted convolution algebra of W0 as single statements
(blueprint `bpW:w0n:algebra`, step `stepW:w0n:weight`)

Off-frontier, source-faithful infrastructure (W-GRAPH-CLOSE); the dependency graph is still being
built.

* `wave_weight_step` (step `stepW:w0n:weight`): for `i, l ∈ ℤ`, `w_l = ⟨l⟩^s e^{a|l|}`:
  `e^{a|l|} ≤ e^{a|i|} e^{a|l-i|}`, `⟨l⟩ ≤ ⟨i⟩ + ⟨l-i⟩`,
  `w_l ≤ 2^{s-1}(w_i e^{a|l-i|} + e^{a|i|} w_{l-i})
  ≤ 2^{s-1}(w_i w_{l-i}/⟨l-i⟩^s + w_i w_{l-i}/⟨i⟩^s)` (the last step is an equality).
  It repackages `wave_weight_ineq`, `waveJap_sub_le` (`Algebra.lean`).
* `wave_algebra_w0n` (Lemma `bpW:w0n:algebra`): `wave_algebra` together with
  `K_{3/2}² = 8(1 + 2ζ(3))` (`waveAlgConst_three_halves_sq`, `CubicHeadline.lean`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- **Step `stepW:w0n:weight`** of `bpW:w0n:algebra`: for `a ≥ 0`, `s ≥ 1`, `i, l ∈ ℤ` and
`w_l = ⟨l⟩^s e^{a|l|}`: `e^{a|l|} ≤ e^{a|i|} e^{a|l-i|}`, `⟨l⟩ ≤ ⟨i⟩ + ⟨l-i⟩`, and
`w_l ≤ 2^{s-1}(w_i e^{a|l-i|} + e^{a|i|} w_{l-i}) = 2^{s-1}(w_i w_{l-i}/⟨l-i⟩^s + w_i w_{l-i}/⟨i⟩^s)`.
-/
theorem wave_weight_step {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) (l i : ℤ) :
    Real.exp (a * |(l : ℝ)|) ≤ Real.exp (a * |(i : ℝ)|) * Real.exp (a * |((l - i : ℤ) : ℝ)|) ∧
    waveJap l ≤ waveJap i + waveJap (l - i) ∧
    waveTwoWeight a s l ≤ 2 ^ (s - 1) *
      (waveTwoWeight a s i * Real.exp (a * |((l - i : ℤ) : ℝ)|) +
        Real.exp (a * |(i : ℝ)|) * waveTwoWeight a s (l - i)) ∧
    waveTwoWeight a s l ≤ 2 ^ (s - 1) *
      (waveTwoWeight a s i * waveTwoWeight a s (l - i) / waveJap (l - i) ^ s +
        waveTwoWeight a s i * waveTwoWeight a s (l - i) / waveJap i ^ s) := by
  have hE : Real.exp (a * |(l : ℝ)|) ≤
      Real.exp (a * |(i : ℝ)|) * Real.exp (a * |((l - i : ℤ) : ℝ)|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := abs_add_le (i : ℝ) ((l - i : ℤ) : ℝ)
    have h3 : |(l : ℝ)| ≤ |(i : ℝ)| + |((l - i : ℤ) : ℝ)| := by simpa using this
    nlinarith
  have hW := wave_weight_ineq ha hs l i
  have e1 : waveTwoWeight a s i * Real.exp (a * |((l - i : ℤ) : ℝ)|) =
      waveTwoWeight a s i * waveTwoWeight a s (l - i) / waveJap (l - i) ^ s := by
    have := (Real.rpow_pos_of_pos (waveJap_pos (l - i)) s).ne'
    unfold waveTwoWeight
    field_simp
  have e2 : Real.exp (a * |(i : ℝ)|) * waveTwoWeight a s (l - i) =
      waveTwoWeight a s i * waveTwoWeight a s (l - i) / waveJap i ^ s := by
    have := (Real.rpow_pos_of_pos (waveJap_pos i) s).ne'
    unfold waveTwoWeight
    field_simp
  refine ⟨hE, waveJap_sub_le l i, ?_, ?_⟩
  · calc _ ≤ _ := hW
      _ = _ := by ring
  · rw [← e1, ← e2]
    calc _ ≤ _ := hW
      _ = _ := by ring

/-- **The weighted convolution algebra** (blueprint Lemma `bpW:w0n:algebra`): for `a ≥ 0`, `s ≥ 1`
and `c, d ∈ ℓ^{a,s}_b`, every convolution sum converges absolutely, `c * d ∈ ℓ^{a,s}_b` and
`‖c * d‖_{a,s} ≤ K_s ‖c‖_{a,s} ‖d‖_{a,s}` with `K_s = 2^s (1 + 2ζ(2s))^{1/2}`; in particular
`K_{3/2}² = 8(1 + 2ζ(3))`. -/
theorem wave_algebra_w0n {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {c d : ℤ → ℂ}
    (hc : WaveTwoMem a s c) (hd : WaveTwoMem a s d) :
    ((∀ l, Summable fun i => ‖c i‖ * ‖d (l - i)‖) ∧ WaveTwoMem a s (waveConv c d) ∧
      waveTwoNorm a s (waveConv c d) ≤ waveAlgConst s * waveTwoNorm a s c * waveTwoNorm a s d) ∧
    waveAlgConst (3 / 2) ^ 2 = 8 * (1 + 2 * (riemannZeta 3).re) :=
  ⟨wave_algebra ha hs hc hd, waveAlgConst_three_halves_sq⟩

end KAM.Wave
