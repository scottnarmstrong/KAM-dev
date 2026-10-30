/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import KAM.Wave.Normal.Analysis.EllSeq

/-!
# Young's inequality `ℓ² * ℓ¹ ⊆ ℓ²` for nonnegative two-sided sequences
(helper for blueprint `bpW:w0n:algebra`, `bpW:w0n:cubic-bound`)

Infrastructure used by several nodes; the dependency graph is still being built.

For `X Y : ℤ → ℝ` the convolution is `(X * Y)_l = Σ_i X_{l-i} Y_i` (`KAM.Wave.waveConv`) and
`‖X‖₂ = (Σ X_i²)^{1/2}` (`KAM.Wave.waveL2`). `KAM.Wave.waveYoung`: for nonnegative `X ∈ ℓ²`,
`Y ∈ ℓ¹`, every convolution sum converges, `X * Y ∈ ℓ²` and `‖X * Y‖₂ ≤ ‖X‖₂ ‖Y‖₁`.
Also Minkowski's inequality (`KAM.Wave.waveL2_add_le`) and commutativity of `waveConv`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- The two-sided convolution `(X * Y)_l = Σ_{i ∈ ℤ} X_{l-i} Y_i`. -/
def waveConv (X Y : ℤ → ℝ) (l : ℤ) : ℝ := ∑' i : ℤ, X (l - i) * Y i

/-- The `ℓ²(ℤ)` norm `(Σ_i X_i²)^{1/2}` (junk off `ℓ²`). -/
def waveL2 (X : ℤ → ℝ) : ℝ := Real.sqrt (∑' i : ℤ, X i ^ 2)

lemma waveConv_comm (X Y : ℤ → ℝ) (l : ℤ) : waveConv X Y l = waveConv Y X l := by
  unfold waveConv
  rw [← (Equiv.subLeft l).tsum_eq]
  exact tsum_congr fun i => by simp [mul_comm]

lemma summable_shift_sq {X : ℤ → ℝ} (hX : Summable fun i => X i ^ 2) (k : ℤ) :
    Summable fun i => X (k - i) ^ 2 := by
  have := (Equiv.subLeft k).summable_iff.2 hX
  exact this

lemma tsum_shift_sq (X : ℤ → ℝ) (k : ℤ) : ∑' i, X (k - i) ^ 2 = ∑' i, X i ^ 2 :=
  (Equiv.subLeft k).tsum_eq (fun i => X i ^ 2)

/-- Young's inequality for nonnegative two-sided sequences. -/
theorem waveYoung {X Y : ℤ → ℝ} (hX0 : ∀ i, 0 ≤ X i) (hY0 : ∀ i, 0 ≤ Y i)
    (hX : Summable fun i => X i ^ 2) (hY : Summable Y) :
    (∀ l, Summable fun i => X (l - i) * Y i) ∧
      Summable (fun l => waveConv X Y l ^ 2) ∧
      waveL2 (waveConv X Y) ≤ waveL2 X * ∑' i, Y i := by
  set SX := ∑' i, X i ^ 2 with hSX
  set SY := ∑' i, Y i with hSY
  have hSY0 : 0 ≤ SY := tsum_nonneg hY0
  have hSX0 : 0 ≤ SX := tsum_nonneg fun i => sq_nonneg _
  -- the auxiliary double series
  have hfib : ∀ l, Summable fun i => Y i * X (l - i) ^ 2 := by
    intro l
    refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hY0 i) (sq_nonneg _))
      (fun i => ?_) (hY.mul_right SX)
    exact mul_le_mul_of_nonneg_left (hX.le_tsum (l - i) (fun _ _ => sq_nonneg _)) (hY0 i)
  have hH : Summable fun p : ℤ × ℤ => Y p.1 * X (p.2 - p.1) ^ 2 := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (hY0 _) (sq_nonneg _))]
    refine ⟨fun i => ?_, ?_⟩
    · have := (Equiv.subRight i).summable_iff.2 hX
      exact (this.mul_left (Y i))
    · have : ∀ i, ∑' l, Y i * X (l - i) ^ 2 = Y i * SX := fun i => by
        rw [tsum_mul_left]
        congr 1
        exact (Equiv.subRight i).tsum_eq (fun l => X l ^ 2)
      simp only [this]
      exact hY.mul_right SX
  have hH' : Summable fun p : ℤ × ℤ => Y p.2 * X (p.1 - p.2) ^ 2 :=
    (Equiv.prodComm ℤ ℤ).summable_iff.2 hH
  have hG := ((summable_prod_of_nonneg (fun p : ℤ × ℤ => mul_nonneg (hY0 p.2) (sq_nonneg _))).1
    hH').2
  have hGsum : ∑' l, ∑' i, Y i * X (l - i) ^ 2 = SY * SX := by
    rw [← hH'.tsum_prod]
    rw [← (Equiv.prodComm ℤ ℤ).tsum_eq]
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [hH.tsum_prod]
    have : ∀ i, ∑' l, Y i * X (l - i) ^ 2 = Y i * SX := fun i => by
      rw [tsum_mul_left]
      congr 1
      exact (Equiv.subRight i).tsum_eq (fun l => X l ^ 2)
    simp only [this]
    rw [tsum_mul_right]
  -- Cauchy–Schwarz for each `l`
  have hcs : ∀ l, (Summable fun i => X (l - i) * Y i) ∧
      waveConv X Y l ^ 2 ≤ SY * ∑' i, Y i * X (l - i) ^ 2 := by
    intro l
    have h := waveCauchySchwarz_tsum (f := fun i => Real.sqrt (Y i))
      (g := fun i => Real.sqrt (Y i) * X (l - i)) (fun i => Real.sqrt_nonneg _)
      (fun i => mul_nonneg (Real.sqrt_nonneg _) (hX0 _))
      (by simpa [Real.sq_sqrt (hY0 _)] using hY)
      (by simpa [mul_pow, Real.sq_sqrt (hY0 _)] using hfib l)
    have e1 : ∀ i, Real.sqrt (Y i) * (Real.sqrt (Y i) * X (l - i)) = X (l - i) * Y i := fun i => by
      rw [← mul_assoc, Real.mul_self_sqrt (hY0 i), mul_comm]
    have e2 : ∀ i, Real.sqrt (Y i) ^ 2 = Y i := fun i => Real.sq_sqrt (hY0 i)
    have e3 : ∀ i, (Real.sqrt (Y i) * X (l - i)) ^ 2 = Y i * X (l - i) ^ 2 := fun i => by
      rw [mul_pow, e2]
    simp only [e1, e2, e3] at h
    refine ⟨h.1, ?_⟩
    have hc0 : 0 ≤ waveConv X Y l := tsum_nonneg fun i => mul_nonneg (hX0 _) (hY0 _)
    have := h.2
    unfold waveConv
    calc (∑' i, X (l - i) * Y i) ^ 2 ≤ (Real.sqrt SY * Real.sqrt (∑' i, Y i * X (l - i) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hc0 this 2
      _ = SY * ∑' i, Y i * X (l - i) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hSY0,
            Real.sq_sqrt (tsum_nonneg fun i => mul_nonneg (hY0 i) (sq_nonneg _))]
  have hsq : Summable fun l => waveConv X Y l ^ 2 :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => (hcs l).2) (hG.mul_left SY)
  refine ⟨fun l => (hcs l).1, hsq, ?_⟩
  have hle : ∑' l, waveConv X Y l ^ 2 ≤ SY * (SY * SX) := by
    calc ∑' l, waveConv X Y l ^ 2 ≤ ∑' l, SY * ∑' i, Y i * X (l - i) ^ 2 :=
          Summable.tsum_le_tsum (fun l => (hcs l).2) hsq (hG.mul_left SY)
      _ = SY * (SY * SX) := by rw [tsum_mul_left, hGsum]
  unfold waveL2
  calc Real.sqrt (∑' l, waveConv X Y l ^ 2) ≤ Real.sqrt (SY ^ 2 * SX) :=
        Real.sqrt_le_sqrt (by nlinarith [hle])
    _ = Real.sqrt SX * SY := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hSY0, mul_comm]

/-- Minkowski's inequality for nonnegative square-summable sequences. -/
theorem waveL2_add_le {X Y : ℤ → ℝ} (hX0 : ∀ i, 0 ≤ X i) (hY0 : ∀ i, 0 ≤ Y i)
    (hX : Summable fun i => X i ^ 2) (hY : Summable fun i => Y i ^ 2) :
    Summable (fun i => (X i + Y i) ^ 2) ∧ waveL2 (fun i => X i + Y i) ≤ waveL2 X + waveL2 Y := by
  have hcs := waveCauchySchwarz_tsum hX0 hY0 hX hY
  have hs : Summable fun i => (X i + Y i) ^ 2 := by
    have := (hX.add hY).add (hcs.1.mul_left 2)
    refine this.congr fun i => ?_
    ring
  refine ⟨hs, ?_⟩
  unfold waveL2
  have h2 : Summable fun i => 2 * (X i * Y i) := hcs.1.mul_left 2
  have e : ∑' i, (X i + Y i) ^ 2 = ∑' i, X i ^ 2 + 2 * ∑' i, X i * Y i + ∑' i, Y i ^ 2 := by
    rw [← tsum_mul_left, ← hX.tsum_add h2, ← (hX.add h2).tsum_add hY]
    exact tsum_congr fun i => by ring
  have hA : Real.sqrt (∑' i, X i ^ 2) ^ 2 = ∑' i, X i ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg (X i))
  have hB : Real.sqrt (∑' i, Y i ^ 2) ^ 2 = ∑' i, Y i ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg (Y i))
  show Real.sqrt (∑' i, (X i + Y i) ^ 2) ≤ _
  rw [e]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [hcs.2, hA, hB]

end KAM.Wave

end
