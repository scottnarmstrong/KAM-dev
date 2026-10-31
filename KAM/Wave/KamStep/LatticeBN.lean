/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LatticeBW
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The modified lattice constant `B^♮_σ` (`bpW:w5:w4-modified` (iii), step `m-const`)

`waveBN τ σ = ∑_k (1+|k|₁)² A_k² e^{-2π|k|₁σ}` (`B^♮_σ`) and
`waveBNconst τ = 4 (C_0 + C_2 + C_{2τ} + C_{2τ+2})` (`b^♮(τ)`, four terms counted with
    multiplicity).
Main results: `waveBW_le_waveBN` (`B^W_σ ≤ B^♮_σ`) and `waveBN_le`
(`B^♮_σ ≤ b^♮(τ) σ^{-(2τ+4)}` for `0 < σ ≤ 1`).
-/

@[expose] public section

namespace KAM.Wave

open Finset

/-- `B^♮_σ = ∑_k (1+|k|₁)² A_k² e^{-2π|k|₁σ}`. -/
noncomputable def waveBN (τ σ : ℝ) : ℝ :=
  ∑' k : Fin 2 → ℤ, (1 + Fourier.modeSize k) ^ 2 * waveA τ k ^ 2 *
    Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)

/-- `b^♮(τ) = 4 (C_0 + C_2 + C_{2τ} + C_{2τ+2})`. -/
noncomputable def waveBNconst (τ : ℝ) : ℝ :=
  4 * (waveC 0 + waveC 2 + waveC (2 * τ) + waveC (2 * τ + 2))

theorem waveS_le_waveBNconst {q τ σ : ℝ} (hq : 0 ≤ q) (hqτ : q ≤ 2 * τ + 2) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) : waveS q σ ≤ waveC q / σ ^ (2 * τ + 4) := by
  refine (waveS_le_waveC hq hσ hσ1).trans ?_
  refine div_le_div_of_nonneg_left (waveC_nonneg hq) (by positivity) ?_
  exact Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by linarith)

theorem waveBN_pointwise {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) (k : Fin 2 → ℤ) :
    (1 + Fourier.modeSize k) ^ 2 * waveA τ k ^ 2 *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
      4 * (Fourier.modeSize k ^ (0 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ + 2) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
  set x := Fourier.modeSize k with hx
  have hx0 : 0 ≤ x := Fourier.modeSize_nonneg k
  set e := Real.exp (-(2 * Real.pi * σ) * x) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hp2 : x ^ (2 * τ + 2) = x ^ 2 * x ^ (2 * τ) := by
    rw [Real.rpow_add' hx0 (by linarith), Real.rpow_two, mul_comm]
  have hy : 0 ≤ x ^ (2 * τ) := by positivity
  rw [Real.rpow_zero, Real.rpow_two, hp2]
  have hx2 : 0 ≤ x ^ 2 := by positivity
  have hA : waveA τ k ^ 2 ≤ 2 * (1 + x ^ (2 * τ)) := by
    by_cases hk : k = 0
    · have : waveA τ k = 1 := by simp only [waveA, hk, ↓reduceIte]
      rw [this]; nlinarith
    · have hA : waveA τ k = 1 + x ^ τ := by simp only [waveA, hk, ↓reduceIte, hx]
      have hy2 : (x ^ τ) ^ 2 = x ^ (2 * τ) := by
        rw [show 2 * τ = τ * 2 by ring, Real.rpow_mul hx0, Real.rpow_two]
      rw [hA]
      nlinarith [sq_nonneg (x ^ τ - 1)]
  have h1 : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith [sq_nonneg (x - 1)]
  have h3 : (1 + x) ^ 2 * waveA τ k ^ 2 ≤ (2 * (1 + x ^ 2)) * (2 * (1 + x ^ (2 * τ))) :=
    mul_le_mul h1 hA (by positivity) (by positivity)
  calc (1 + x) ^ 2 * waveA τ k ^ 2 * e ≤ (2 * (1 + x ^ 2)) * (2 * (1 + x ^ (2 * τ))) * e :=
        mul_le_mul_of_nonneg_right h3 he0
    _ = _ := by ring

theorem waveBN_summable {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) :
    Summable (fun k : Fin 2 → ℤ => (1 + Fourier.modeSize k) ^ 2 * waveA τ k ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
  have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ (1 + Fourier.modeSize k) ^ 2 * waveA τ k ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := fun k => by positivity
  have hs := ((((waveS_summable (q := 0) le_rfl hσ).add (waveS_summable (q := 2) (by norm_num)
      hσ)).add
      (waveS_summable (q := 2 * τ) (by linarith) hσ)).add
      (waveS_summable (q := 2 * τ + 2) (by linarith) hσ)).mul_left 4
  exact Summable.of_nonneg_of_le hnn (waveBN_pointwise hτ σ) hs

theorem waveBW_le_waveBN {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) : waveBW τ σ ≤ waveBN τ σ := by
  have hle : ∀ k : Fin 2 → ℤ, (1 + Fourier.modeSize k) * waveA τ k ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
      (1 + Fourier.modeSize k) ^ 2 * waveA τ k ^ 2 *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := fun k => by
    have hx := Fourier.modeSize_nonneg k
    have : (1 + Fourier.modeSize k) ≤ (1 + Fourier.modeSize k) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (by positivity))
      (Real.exp_pos _).le
  exact Summable.tsum_le_tsum hle (waveBW_summable hτ hσ) (waveBN_summable hτ hσ)

/-- **The modified lattice constant** (`bpW:w5:w4-modified` (iii)): for `τ ≥ 0`, `0 < σ ≤ 1`,
`B^♮_σ ≤ b^♮(τ) σ^{-(2τ+4)}`. -/
theorem waveBN_le {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    waveBN τ σ ≤ waveBNconst τ / σ ^ (2 * τ + 4) := by
  have hs := waveBN_summable hτ hσ
  have h0 := waveS_summable (q := 0) le_rfl hσ
  have h1 := waveS_summable (q := 2) (by norm_num) hσ
  have h2 := waveS_summable (q := 2 * τ) (by linarith) hσ
  have h3 := waveS_summable (q := 2 * τ + 2) (by linarith) hσ
  have hsum := ((h0.add h1).add h2).add h3
  have hle := Summable.tsum_le_tsum (waveBN_pointwise hτ σ) hs (hsum.mul_left 4)
  unfold waveBN
  refine hle.trans ?_
  have e : ∑' k : Fin 2 → ℤ,
      (Fourier.modeSize k ^ (0 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ + 2) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) =
      waveS 0 σ + waveS 2 σ + waveS (2 * τ) σ + waveS (2 * τ + 2) σ := by
    rw [((h0.add h1).add h2).tsum_add h3, (h0.add h1).tsum_add h2, h0.tsum_add h1]; rfl
  rw [tsum_mul_left, e]
  have b0 := waveS_le_waveBNconst (q := 0) (τ := τ) le_rfl (by linarith) hσ hσ1
  have b1 := waveS_le_waveBNconst (q := 2) (τ := τ) (by norm_num) (by linarith) hσ hσ1
  have b2 := waveS_le_waveBNconst (q := 2 * τ) (τ := τ) (by linarith) (by linarith) hσ hσ1
  have b3 := waveS_le_waveBNconst (q := 2 * τ + 2) (τ := τ) (by linarith) le_rfl hσ hσ1
  unfold waveBNconst
  rw [mul_div_assoc, add_div, add_div, add_div]
  linarith

end KAM.Wave
