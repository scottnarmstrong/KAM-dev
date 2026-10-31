/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Cubic.SelectionCore

/-!
# The two-sided majorant (blueprint `bpW:w1:selection` (b), step `stepW:w1:maj2`)

Off-frontier, source-faithful infrastructure used by several nodes; the dependency graph is
still being built.

For `w : ℤ → ℂ` let `x̃_i = (‖w_i‖ + ‖w_{-i}‖) / √|i|` (`i ≠ 0`), `x̃_0 = 0`
(`KAM.Wave.waveTwoMaj`). It is even and nonnegative, and for `w ∈ ℓ^{a,p}_b`,
`‖x̃‖_{a,p+1/2} ≤ 2 ‖w‖_{a,p}` (`KAM.Wave.waveTwoMaj_weighted`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The even majorant `x̃_i = (‖w_i‖ + ‖w_{-i}‖)/√|i|` (`i ≠ 0`), `x̃_0 = 0`. -/
def waveTwoMaj (w : ℤ → ℂ) (i : ℤ) : ℝ :=
  if i = 0 then 0 else (‖w i‖ + ‖w (-i)‖) / Real.sqrt |(i : ℝ)|

lemma waveTwoMaj_nonneg (w : ℤ → ℂ) (i : ℤ) : 0 ≤ waveTwoMaj w i := by
  unfold waveTwoMaj; split_ifs <;> positivity

lemma waveTwoMaj_neg (w : ℤ → ℂ) (i : ℤ) : waveTwoMaj w (-i) = waveTwoMaj w i := by
  unfold waveTwoMaj
  by_cases h : i = 0
  · simp [h]
  · have h' : -i ≠ 0 := neg_ne_zero.2 h
    simp only [h, h', if_false, neg_neg, Int.cast_neg, abs_neg]
    rw [add_comm]

lemma waveTwoMaj_zero (w : ℤ → ℂ) : waveTwoMaj w 0 = 0 := by simp [waveTwoMaj]

lemma waveJap_of_ne_zero {i : ℤ} (hi : i ≠ 0) : waveJap i = |(i : ℝ)| := by
  have : (1 : ℝ) ≤ |(i : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
  unfold waveJap
  exact max_eq_right this

lemma waveTwoWeight_of_ne_zero (a s : ℝ) {i : ℤ} (hi : i ≠ 0) :
    waveTwoWeight a s i = |(i : ℝ)| ^ s * Real.exp (a * |(i : ℝ)|) := by
  unfold waveTwoWeight; rw [waveJap_of_ne_zero hi]

/-- `stepW:w1:maj2`: the weighted norm of the two-sided majorant is at most `2 ‖w‖_{a,p}`. -/
theorem waveTwoMaj_weighted {a p : ℝ} {w : ℤ → ℂ} (hw : WaveTwoMem a p w) :
    Summable (fun i : ℤ => (waveTwoWeight a (p + 1 / 2) i * waveTwoMaj w i) ^ 2) ∧
      w0aL2 (fun i : ℤ => waveTwoWeight a (p + 1 / 2) i * waveTwoMaj w i) ≤
        2 * waveTwoNorm a p w := by
  set u : ℤ → ℝ := fun i => (waveTwoWeight a p i * ‖w i‖) ^ 2 with hu
  have hu1 : Summable u := hw
  have hu2 : Summable fun i => u (-i) := hu1.comp_injective neg_injective
  have hpt : ∀ i : ℤ, (waveTwoWeight a (p + 1 / 2) i * waveTwoMaj w i) ^ 2 ≤
      2 * (u i + u (-i)) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simp only [waveTwoMaj_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, neg_zero, hu]
      positivity
    · have hr : (0 : ℝ) < |(i : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast abs_pos.2 hi
      have hs : 0 < Real.sqrt |(i : ℝ)| := Real.sqrt_pos.2 hr
      have h1 : waveTwoWeight a (p + 1 / 2) i * waveTwoMaj w i =
          waveTwoWeight a p i * (‖w i‖ + ‖w (-i)‖) := by
        rw [waveTwoWeight_of_ne_zero a _ hi, waveTwoWeight_of_ne_zero a _ hi]
        simp only [waveTwoMaj, hi, if_false]
        rw [Real.rpow_add hr, Real.sqrt_eq_rpow]
        field_simp
      have h2 : waveTwoWeight a p (-i) = waveTwoWeight a p i := w0a_twoWeight_neg a p i
      rw [h1]
      simp only [hu, h2]
      nlinarith [sq_nonneg (waveTwoWeight a p i * ‖w i‖ - waveTwoWeight a p i * ‖w (-i)‖)]
  have hs : Summable fun i : ℤ => (waveTwoWeight a (p + 1 / 2) i * waveTwoMaj w i) ^ 2 :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) hpt ((hu1.add hu2).mul_left 2)
  refine ⟨hs, ?_⟩
  have hsum : ∑' i : ℤ, u (-i) = ∑' i : ℤ, u i := (Equiv.neg ℤ).tsum_eq u
  have hle : ∑' i : ℤ, (waveTwoWeight a (p + 1 / 2) i * waveTwoMaj w i) ^ 2 ≤
      4 * ∑' i : ℤ, u i := by
    calc _ ≤ ∑' i : ℤ, 2 * (u i + u (-i)) :=
          Summable.tsum_le_tsum hpt hs ((hu1.add hu2).mul_left 2)
      _ = 2 * (∑' i : ℤ, u i + ∑' i : ℤ, u (-i)) := by
          rw [tsum_mul_left, Summable.tsum_add hu1 hu2]
      _ = _ := by rw [hsum]; ring
  unfold w0aL2 waveTwoNorm
  calc Real.sqrt (∑' i : ℤ, (waveTwoWeight a (p + 1 / 2) i * waveTwoMaj w i) ^ 2)
      ≤ Real.sqrt (4 * ∑' i : ℤ, u i) := Real.sqrt_le_sqrt hle
    _ = 2 * Real.sqrt (∑' i : ℤ, u i) := by
        rw [Real.sqrt_mul (by norm_num)]
        congr 1
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

end KAM.Wave

end
