/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Diophantine
public import KAM.Frozen.Defs.IsDiophantine

/-!
# The limit bridge (blueprint `bpP:p11a:limit-bridge`, P11A-W8)

A frequency within `γ |k|₁^(-τ-1)` of a frequency that is `2γ |k|₁^(-τ)`-non-resonant in the
direction `k` is `γ |k|₁^(-τ)`-non-resonant (`limit_bridge`), and a point of the doubled good set
whose perturbed frequencies converge to `v` produces a `(γ, τ)`-Diophantine `v`
(`limit_bridge_diophantine`, in the frozen sense of `KAM.IsDiophantine`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace KAM.Planetary

theorem limit_bridge {m : ℕ} {gamma tau : ℝ} (hg : 0 < gamma)
    {k : Fin m → ℤ} (hk : k ≠ 0) {u v : P11Vec m}
    (hu : 2*gamma*KAM.Fourier.modeSize k^(-tau) ≤ |p11dotZ k u|)
    (ht : ‖u-v‖ ≤ gamma*KAM.Fourier.modeSize k^(-tau-1)) :
    gamma*KAM.Fourier.modeSize k^(-tau) ≤ |p11dotZ k v| := by
  have hs : 0 < KAM.Fourier.modeSize k := by
    refine lt_of_le_of_ne (KAM.Fourier.modeSize_nonneg k) fun h => hk ?_
    funext i
    have := KAM.Fourier.abs_coord_le_modeSize k i
    rw [← h] at this
    simpa using abs_nonpos_iff.1 this
  set s := KAM.Fourier.modeSize k with hsdef
  have hdiff : |p11dotZ k (u - v)| ≤ s * ‖u - v‖ := by
    unfold p11dotZ
    calc |∑ i, (k i : ℝ) * (u - v) i| ≤ ∑ i, |(k i : ℝ) * (u - v) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |(k i : ℝ)| * ‖u - v‖ := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm (u - v) i)
            (abs_nonneg _)
      _ = s * ‖u - v‖ := by rw [← Finset.sum_mul]; rfl
  have hrw : s * (gamma * s ^ (-tau - 1)) = gamma * s ^ (-tau) := by
    rw [Real.rpow_sub hs, Real.rpow_one]
    field_simp
  have hlin : p11dotZ k v = p11dotZ k u - p11dotZ k (u - v) := by
    unfold p11dotZ
    simp [mul_sub, Finset.sum_sub_distrib]
  have h1 : |p11dotZ k u| - |p11dotZ k (u - v)| ≤ |p11dotZ k v| := by
    rw [hlin]; exact abs_sub_abs_le_abs_sub _ _
  have h2 : s * ‖u - v‖ ≤ gamma * s ^ (-tau) := by
    rw [← hrw]; exact mul_le_mul_of_nonneg_left ht hs.le
  linarith

theorem limit_bridge_diophantine {n m : ℕ} {K : Set (P11Vec n)}
    {wt : (Fin m → ℤ) → P11Vec n → P11Vec m} {gamma tau : ℝ}
    (hg : 0 < gamma) {b : P11Vec n}
    (hb : b ∈ p11Good K wt (fun k => 2*gamma*KAM.Fourier.modeSize k^(-tau)))
    (v : P11Vec m)
    (ht : ∀ k, k ≠ 0 → ‖wt k b-v‖ ≤ gamma*KAM.Fourier.modeSize k^(-tau-1)) :
    KAM.IsDiophantine gamma tau v := by
  intro k hk
  have h := limit_bridge hg hk (hb.2 k hk) (ht k hk)
  have hs : 0 ≤ KAM.Fourier.modeSize k := KAM.Fourier.modeSize_nonneg k
  rw [Real.rpow_neg hs, ← div_eq_mul_inv] at h
  exact h

end KAM.Planetary
