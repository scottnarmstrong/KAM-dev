/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.PSeries
public import KAM.Wave.Normal.Analysis.ConvYoung

/-!
# Weighted convolution algebra for nonnegative sequences
(blueprint `bpW:w0n:algebra`, used by `bpW:w0n:cubic-bound`)

Infrastructure used by several nodes; the dependency graph is still being built.

This is a *local helper* for `bpW:w0n:cubic-bound`: the inequality of `bpW:w0n:algebra`
(`‖c * d‖_{a,s} ≤ K_s ‖c‖_{a,s} ‖d‖_{a,s}`, `K_s = 2^s (1 + 2ζ(2s))^{1/2}`, `s ≥ 1`, `a ≥ 0`)
for **nonnegative** two-sided sequences, which suffices for the majorant argument. The general
(complex, signed) statement of `bpW:w0n:algebra` belongs to another package and is not proved here.

* `KAM.Wave.waveW2 a s l = ⟨l⟩^s e^{a|l|}` with `⟨l⟩ = max 1 |l|`;
* `KAM.Wave.waveAlgConst s = 2^s (1 + 2 Σ_{n ≥ 1} n^{-2s})^{1/2}`;
* `KAM.Wave.wave_convAlgebra_nonneg`: the weighted inequality.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- `⟨l⟩ = max 1 |l|`. -/
def waveJap (l : ℤ) : ℝ := max 1 |(l : ℝ)|

/-- The two-sided weight `⟨l⟩^s e^{a |l|}` of `ℓ^{a,s}_b` (blueprint `bpW:w0:twosided`). -/
def waveW2 (a s : ℝ) (l : ℤ) : ℝ := waveJap l ^ s * Real.exp (a * |(l : ℝ)|)

/-- The constant `K_s = 2^s (1 + 2 ζ(2s))^{1/2}` of `bpW:w0n:algebra`, with `ζ(2s)` the series
`Σ_{n ≥ 1} n^{-2s}`. -/
def waveAlgConst (s : ℝ) : ℝ :=
  (2 : ℝ) ^ s * Real.sqrt (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s)))

lemma one_le_waveJap (l : ℤ) : 1 ≤ waveJap l := le_max_left _ _

lemma abs_le_waveJap (l : ℤ) : |(l : ℝ)| ≤ waveJap l := le_max_right _ _

lemma one_le_waveW2 {a : ℝ} (ha : 0 ≤ a) {s : ℝ} (hs : 0 ≤ s) (l : ℤ) : 1 ≤ waveW2 a s l := by
  unfold waveW2
  have h1 : 1 ≤ waveJap l ^ s := Real.one_le_rpow (one_le_waveJap l) hs
  have h2 : 1 ≤ Real.exp (a * |(l : ℝ)|) := Real.one_le_exp (by positivity)
  nlinarith

lemma waveW2_pos {a : ℝ} (s : ℝ) (l : ℤ) : 0 < waveW2 a s l := by
  unfold waveW2
  have : 0 < waveJap l := lt_of_lt_of_le one_pos (one_le_waveJap l)
  positivity

/-- `(α + β)^s ≤ 2^{s-1} (α^s + β^s)` for `s ≥ 1`. -/
lemma wave_add_rpow_le {α β s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : 1 ≤ s) :
    (α + β) ^ s ≤ (2 : ℝ) ^ (s - 1) * (α ^ s + β ^ s) := by
  have := NNReal.rpow_add_le_mul_rpow_add_rpow ⟨α, hα⟩ ⟨β, hβ⟩ hs
  exact_mod_cast this

/-- The weight inequality `w_{u+i} ≤ 2^{s-1} (w_u e^{a|i|} + e^{a|u|} w_i)`
(`stepW:w0n:weight`). -/
lemma waveW2_add_le {a : ℝ} (ha : 0 ≤ a) {s : ℝ} (hs : 1 ≤ s) (u i : ℤ) :
    waveW2 a s (u + i) ≤ (2 : ℝ) ^ (s - 1) *
      (waveW2 a s u * Real.exp (a * |(i : ℝ)|) + Real.exp (a * |(u : ℝ)|) * waveW2 a s i) := by
  have hJ : waveJap (u + i) ≤ waveJap u + waveJap i := by
    refine max_le ?_ ?_
    · linarith [one_le_waveJap u, one_le_waveJap i]
    · push_cast
      linarith [abs_add_le (u : ℝ) (i : ℝ), abs_le_waveJap u, abs_le_waveJap i]
  have hE : Real.exp (a * |((u + i : ℤ) : ℝ)|) ≤ Real.exp (a * |(u : ℝ)|) * Real.exp (a * |(i : ℝ)|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    nlinarith [abs_add_le (u : ℝ) (i : ℝ)]
  have hp : waveJap (u + i) ^ s ≤ (2 : ℝ) ^ (s - 1) * (waveJap u ^ s + waveJap i ^ s) := by
    calc waveJap (u + i) ^ s ≤ (waveJap u + waveJap i) ^ s :=
          Real.rpow_le_rpow (by have := one_le_waveJap (u + i); linarith) hJ (by linarith)
      _ ≤ _ := wave_add_rpow_le (by linarith [one_le_waveJap u]) (by linarith [one_le_waveJap i]) hs
  unfold waveW2
  have hE0 : 0 ≤ Real.exp (a * |((u + i : ℤ) : ℝ)|) := (Real.exp_pos _).le
  calc waveJap (u + i) ^ s * Real.exp (a * |((u + i : ℤ) : ℝ)|)
      ≤ ((2 : ℝ) ^ (s - 1) * (waveJap u ^ s + waveJap i ^ s)) *
          (Real.exp (a * |(u : ℝ)|) * Real.exp (a * |(i : ℝ)|)) := by
        apply mul_le_mul hp hE hE0
        have : 0 ≤ waveJap u ^ s + waveJap i ^ s := by
          have := Real.rpow_nonneg (by linarith [one_le_waveJap u] : (0 : ℝ) ≤ waveJap u) s
          have := Real.rpow_nonneg (by linarith [one_le_waveJap i] : (0 : ℝ) ≤ waveJap i) s
          linarith
        positivity
    _ = _ := by ring

/-- `Σ_{i ∈ ℤ} f i` for an even `f` is `f 0 + 2 Σ_{n ≥ 1} f n`. -/
lemma waveHasSum_int_even {f : ℤ → ℝ} (hev : ∀ i, f (-i) = f i) {S : ℝ}
    (hS : HasSum (fun n : ℕ => f ((n : ℤ) + 1)) S) : HasSum f (f 0 + 2 * S) := by
  have h1 : HasSum (fun n : ℕ => f (n : ℤ)) (f 0 + S) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa using hS
  have h2 : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) S := by
    simpa only [hev] using hS
  have := h1.of_nat_of_neg_add_one h2
  convert this using 1
  ring

lemma waveJap_neg (i : ℤ) : waveJap (-i) = waveJap i := by simp [waveJap]

lemma waveJap_natCast_succ (n : ℕ) : waveJap ((n : ℤ) + 1) = (n : ℝ) + 1 := by
  unfold waveJap
  have : ((((n : ℤ) + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [this, abs_of_nonneg (by positivity)]
  exact max_eq_right (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- `Σ_{i ∈ ℤ} ⟨i⟩^{-2s} = 1 + 2 Σ_{n ≥ 1} n^{-2s}` for `s > 1/2`. -/
lemma waveHasSum_jap_rpow {s : ℝ} (hs : 1 < 2 * s) :
    HasSum (fun i : ℤ => waveJap i ^ (-(2 * s)))
      (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) := by
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(2 * s)) := by
    have := (summable_nat_add_iff 1).2
      (Real.summable_nat_rpow.2 (by linarith : -(2 * s) < -1))
    simpa using this
  have hS : HasSum (fun n : ℕ => waveJap (((n : ℤ)) + 1) ^ (-(2 * s)))
      (∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) := by
    have e : ∀ n : ℕ, waveJap ((n : ℤ) + 1) ^ (-(2 * s)) = ((n : ℝ) + 1) ^ (-(2 * s)) := fun n => by
      rw [waveJap_natCast_succ]
    simp only [e]
    have : ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s)) = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 * s)) := by
      rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℝ) ^ (-(2 * s)))]
      simp
    rw [this]
    exact hsum.hasSum
  have := waveHasSum_int_even (f := fun i : ℤ => waveJap i ^ (-(2 * s)))
    (fun i => by simp [waveJap_neg]) hS
  convert this using 2
  simp [waveJap]

lemma waveL2_const_mul {c : ℝ} (hc : 0 ≤ c) (B : ℤ → ℝ) :
    waveL2 (fun l => c * B l) = c * waveL2 B := by
  unfold waveL2
  have : ∀ l, (c * B l) ^ 2 = c ^ 2 * B l ^ 2 := fun l => by ring
  simp only [this, tsum_mul_left]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

lemma waveL2_mono {A B : ℤ → ℝ} (h : ∀ l, A l ^ 2 ≤ B l ^ 2) (hA : Summable fun l => A l ^ 2)
    (hB : Summable fun l => B l ^ 2) : waveL2 A ≤ waveL2 B :=
  Real.sqrt_le_sqrt (Summable.tsum_le_tsum h hA hB)

/-- Cauchy–Schwarz against `⟨i⟩^{-s}`: `Σ_i D_i ⟨i⟩^{-s} ≤ (1 + 2ζ(2s))^{1/2} ‖D‖₂`. -/
lemma wave_tsum_jap_mul_le {s : ℝ} (hs : 1 ≤ s) {D : ℤ → ℝ} (hD0 : ∀ i, 0 ≤ D i)
    (hD : Summable fun i => D i ^ 2) :
    Summable (fun i => D i * waveJap i ^ (-s)) ∧
      ∑' i, D i * waveJap i ^ (-s) ≤
        Real.sqrt (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) * waveL2 D := by
  have hP := waveHasSum_jap_rpow (s := s) (by linarith)
  have hg2 : ∀ i, (waveJap i ^ (-s)) ^ 2 = waveJap i ^ (-(2 * s)) := fun i => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [one_le_waveJap i])]
    congr 1; push_cast; ring
  have hcs := waveCauchySchwarz_tsum (f := D) (g := fun i => waveJap i ^ (-s)) hD0
    (fun i => Real.rpow_nonneg (by linarith [one_le_waveJap i]) _) hD
    (by simpa only [hg2] using hP.summable)
  refine ⟨hcs.1, ?_⟩
  refine hcs.2.trans ?_
  simp only [hg2, hP.tsum_eq]
  rw [mul_comm]
  rfl

/-- The weighted convolution inequality for nonnegative sequences (`bpW:w0n:algebra`, nonnegative
case, `K_s = 2^s (1 + 2ζ(2s))^{1/2}`). -/
theorem wave_convAlgebra_nonneg {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {X Y : ℤ → ℝ}
    (hX0 : ∀ i, 0 ≤ X i) (hY0 : ∀ i, 0 ≤ Y i)
    (hX : Summable fun i => (waveW2 a s i * X i) ^ 2)
    (hY : Summable fun i => (waveW2 a s i * Y i) ^ 2) :
    Summable (fun l => (waveW2 a s l * waveConv X Y l) ^ 2) ∧
      waveL2 (fun l => waveW2 a s l * waveConv X Y l) ≤
        waveAlgConst s * waveL2 (fun i => waveW2 a s i * X i) *
          waveL2 (fun i => waveW2 a s i * Y i) := by
  have hw1 : ∀ i, 1 ≤ waveW2 a s i := fun i => one_le_waveW2 ha (by linarith) i
  have hwpos : ∀ i, 0 < waveW2 a s i := fun i => waveW2_pos s i
  have hEw : ∀ i : ℤ, Real.exp (a * |(i : ℝ)|) = waveW2 a s i * waveJap i ^ (-s) := fun i => by
    have hj : 0 < waveJap i := lt_of_lt_of_le one_pos (one_le_waveJap i)
    have h1 : waveJap i ^ s * waveJap i ^ (-s) = 1 := by
      rw [← Real.rpow_add hj]; simp
    unfold waveW2
    calc Real.exp (a * |(i : ℝ)|)
        = (waveJap i ^ s * waveJap i ^ (-s)) * Real.exp (a * |(i : ℝ)|) := by rw [h1, one_mul]
      _ = _ := by ring
  obtain ⟨C, hCd⟩ : ∃ C : ℤ → ℝ, C = fun i => waveW2 a s i * X i := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D : ℤ → ℝ, D = fun i => waveW2 a s i * Y i := ⟨_, rfl⟩
  obtain ⟨C1, hC1d⟩ : ∃ C1 : ℤ → ℝ, C1 = fun i : ℤ => Real.exp (a * |(i : ℝ)|) * X i := ⟨_, rfl⟩
  obtain ⟨D1, hD1d⟩ : ∃ D1 : ℤ → ℝ, D1 = fun i : ℤ => Real.exp (a * |(i : ℝ)|) * Y i := ⟨_, rfl⟩
  have hC0 : ∀ i, 0 ≤ C i := fun i => by rw [hCd]; exact mul_nonneg (hwpos i).le (hX0 i)
  have hD0 : ∀ i, 0 ≤ D i := fun i => by rw [hDd]; exact mul_nonneg (hwpos i).le (hY0 i)
  have hC10 : ∀ i, 0 ≤ C1 i := fun i => by rw [hC1d]; exact mul_nonneg (Real.exp_pos _).le (hX0 i)
  have hD10 : ∀ i, 0 ≤ D1 i := fun i => by rw [hD1d]; exact mul_nonneg (Real.exp_pos _).le (hY0 i)
  have hC2 : Summable fun i => C i ^ 2 := by rw [hCd]; exact hX
  have hD2 : Summable fun i => D i ^ 2 := by rw [hDd]; exact hY
  have hXl2 : Summable fun i => X i ^ 2 := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hX
    have : X i ≤ waveW2 a s i * X i := by nlinarith [hX0 i, hw1 i]
    exact pow_le_pow_left₀ (hX0 i) this 2
  have hYl2 : Summable fun i => Y i ^ 2 := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hY
    have : Y i ≤ waveW2 a s i * Y i := by nlinarith [hY0 i, hw1 i]
    exact pow_le_pow_left₀ (hY0 i) this 2
  have hD1e : D1 = fun i => D i * waveJap i ^ (-s) := by
    rw [hD1d, hDd]; funext i; rw [hEw i]; ring
  have hC1e : C1 = fun i => C i * waveJap i ^ (-s) := by
    rw [hC1d, hCd]; funext i; rw [hEw i]; ring
  have hl1D := wave_tsum_jap_mul_le hs hD0 hD2
  have hl1C := wave_tsum_jap_mul_le hs hC0 hC2
  rw [← hD1e] at hl1D
  rw [← hC1e] at hl1C
  have yA := waveYoung hC0 hD10 hC2 hl1D.1
  have yB := waveYoung hD0 hC10 hD2 hl1C.1
  have hcomm : ∀ l, waveConv C1 D l = waveConv D C1 l := waveConv_comm _ _
  have T2 : ∀ l, Summable fun i => C1 (l - i) * D i := by
    intro l
    have := (Equiv.subLeft l).summable_iff.2 (yB.1 l)
    refine this.congr fun i => ?_
    simp [mul_comm]
  -- pointwise estimate
  have hpt : ∀ l i, waveW2 a s l * (X (l - i) * Y i) ≤
      (2 : ℝ) ^ (s - 1) * (C (l - i) * D1 i + C1 (l - i) * D i) := by
    intro l i
    have h := waveW2_add_le ha hs (l - i) i
    rw [sub_add_cancel] at h
    have hXY : 0 ≤ X (l - i) * Y i := mul_nonneg (hX0 _) (hY0 _)
    calc waveW2 a s l * (X (l - i) * Y i)
        ≤ ((2 : ℝ) ^ (s - 1) * (waveW2 a s (l - i) * Real.exp (a * |(i : ℝ)|)
            + Real.exp (a * |((l - i : ℤ) : ℝ)|) * waveW2 a s i)) * (X (l - i) * Y i) :=
          mul_le_mul_of_nonneg_right h hXY
      _ = _ := by rw [hCd, hD1d, hC1d, hDd]; ring
  have hAsum : ∀ l, Summable fun i => waveW2 a s l * (X (l - i) * Y i) := by
    intro l
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hwpos l).le
      (mul_nonneg (hX0 _) (hY0 _))) (hpt l) (((yA.1 l).add (T2 l)).mul_left _)
  have hA_le : ∀ l, waveW2 a s l * waveConv X Y l ≤
      (2 : ℝ) ^ (s - 1) * (waveConv C D1 l + waveConv D C1 l) := by
    intro l
    rw [← hcomm l]
    unfold waveConv
    rw [← tsum_mul_left, ← (yA.1 l).tsum_add (T2 l), ← tsum_mul_left]
    exact Summable.tsum_le_tsum (hpt l) (hAsum l) (((yA.1 l).add (T2 l)).mul_left _)
  have hA0 : ∀ l, 0 ≤ waveW2 a s l * waveConv X Y l := fun l =>
    mul_nonneg (hwpos l).le (tsum_nonneg fun i => mul_nonneg (hX0 _) (hY0 _))
  have hP10 : ∀ l, 0 ≤ waveConv C D1 l := fun l => tsum_nonneg fun i => mul_nonneg (hC0 _) (hD10 _)
  have hP20 : ∀ l, 0 ≤ waveConv D C1 l := fun l => tsum_nonneg fun i => mul_nonneg (hD0 _) (hC10 _)
  have hmink := waveL2_add_le hP10 hP20 yA.2.1 yB.2.1
  have hc0 : (0 : ℝ) ≤ (2 : ℝ) ^ (s - 1) := by positivity
  have hBsum : Summable fun l => ((2 : ℝ) ^ (s - 1) * (waveConv C D1 l + waveConv D C1 l)) ^ 2 := by
    have := hmink.1.mul_left (((2 : ℝ) ^ (s - 1)) ^ 2)
    exact this.congr fun l => by ring
  have hAsq : Summable fun l => (waveW2 a s l * waveConv X Y l) ^ 2 :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _)
      (fun l => pow_le_pow_left₀ (hA0 l) (hA_le l) 2) hBsum
  refine ⟨hAsq, ?_⟩
  have h1 : waveL2 (fun l => waveW2 a s l * waveConv X Y l) ≤
      waveL2 (fun l => (2 : ℝ) ^ (s - 1) * (waveConv C D1 l + waveConv D C1 l)) :=
    waveL2_mono (fun l => pow_le_pow_left₀ (hA0 l) (hA_le l) 2) hAsq hBsum
  rw [waveL2_const_mul hc0] at h1
  have hK : waveAlgConst s = 2 * (2 : ℝ) ^ (s - 1) * Real.sqrt (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) := by
    unfold waveAlgConst
    rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
    field_simp
  have hL2C : 0 ≤ waveL2 (fun i => waveW2 a s i * X i) := Real.sqrt_nonneg _
  have hL2D : 0 ≤ waveL2 (fun i => waveW2 a s i * Y i) := Real.sqrt_nonneg _
  have hC' : waveL2 C = waveL2 (fun i => waveW2 a s i * X i) := by rw [hCd]
  have hD' : waveL2 D = waveL2 (fun i => waveW2 a s i * Y i) := by rw [hDd]
  have hr1 := yA.2.2
  have hr2 := yB.2.2
  have hsq0 : 0 ≤ Real.sqrt (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) := Real.sqrt_nonneg _
  have hS1 : waveL2 C * ∑' i, D1 i ≤ waveL2 C * (Real.sqrt (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) * waveL2 D) :=
    mul_le_mul_of_nonneg_left hl1D.2 (Real.sqrt_nonneg _)
  have hS2 : waveL2 D * ∑' i, C1 i ≤ waveL2 D * (Real.sqrt (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) * waveL2 C) :=
    mul_le_mul_of_nonneg_left hl1C.2 (Real.sqrt_nonneg _)
  rw [hC'] at hS1 hS2 hr1
  rw [hD'] at hS1 hS2 hr2
  rw [hK]
  have h2 : waveL2 (fun l => waveConv C D1 l + waveConv D C1 l) ≤
      waveL2 (fun l => waveConv C D1 l) + waveL2 (fun l => waveConv D C1 l) := hmink.2
  have h3 : waveL2 (waveConv C D1) ≤ _ := hr1
  have h4 : waveL2 (waveConv D C1) ≤ _ := hr2
  calc _ ≤ (2 : ℝ) ^ (s - 1) * waveL2 (fun l => waveConv C D1 l + waveConv D C1 l) := h1
    _ ≤ (2 : ℝ) ^ (s - 1) * (waveL2 (waveConv C D1) + waveL2 (waveConv D C1)) :=
        mul_le_mul_of_nonneg_left h2 hc0
    _ ≤ (2 : ℝ) ^ (s - 1) * (waveL2 (fun i => waveW2 a s i * X i) * ∑' i, D1 i +
          waveL2 (fun i => waveW2 a s i * Y i) * ∑' i, C1 i) := by
        gcongr
    _ ≤ (2 : ℝ) ^ (s - 1) * (waveL2 (fun i => waveW2 a s i * X i) *
          (Real.sqrt (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) * waveL2 (fun i => waveW2 a s i * Y i)) +
        waveL2 (fun i => waveW2 a s i * Y i) *
          (Real.sqrt (1 + 2 * ∑' n : ℕ+, (n : ℝ) ^ (-(2 * s))) * waveL2 (fun i => waveW2 a s i * X i))) := by
        gcongr
    _ = _ := by ring

end KAM.Wave

end
