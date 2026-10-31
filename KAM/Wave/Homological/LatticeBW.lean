/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The small-divisor lattice constant `b_W(τ)` (blueprint-W `bpW:w4:lattice` (iv))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

`waveA τ k` is `A_k` (`A_0 = 1`, `A_k = 1 + |k|₁^τ` otherwise), `waveBW τ σ` is `B^W_σ`, and
`waveBWconst τ = b_W(τ)`. Main results: `waveSum_A_le_waveBW` (`∑ A_k e^{-2π|k|₁σ} ≤ B^W_σ`) and
`waveBW_le` (`B^W_σ ≤ b_W(τ) σ^{-(2τ+3)}` for `0 < σ ≤ 1`).
-/

@[expose] public section

namespace KAM.Wave

open Finset

/-- `A_k`: `A_0 = 1` and `A_k = 1 + |k|₁^τ` for `k ≠ 0` (blueprint `bpW:w4:melnikov`). -/
noncomputable def waveA (τ : ℝ) (k : Fin 2 → ℤ) : ℝ :=
  if k = 0 then 1 else 1 + Fourier.modeSize k ^ τ

/-- `B^W_σ = ∑_k (1+|k|₁) A_k² e^{-2π|k|₁σ}` (blueprint `bpW:w4:lattice` (iv)). -/
noncomputable def waveBW (τ σ : ℝ) : ℝ :=
  ∑' k : Fin 2 → ℤ, (1 + Fourier.modeSize k) * waveA τ k ^ 2 *
    Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)

/-- The constants `C_q` of `bpW:w4:lattice` (iv), `C_0 = (1 + 1/π)²`. -/
noncomputable def waveC (q : ℝ) : ℝ :=
  if q = 0 then (1 + Real.pi⁻¹) ^ 2 else 4 / Real.pi * ((q + 1) / (Real.exp 1 * Real.pi)) ^ (q + 1)

/-- `b_W(τ) = 2 (C_0 + C_1 + C_{2τ} + C_{2τ+1})` (blueprint `bpW:w4:lattice` (iv)). -/
noncomputable def waveBWconst (τ : ℝ) : ℝ :=
  2 * (waveC 0 + waveC 1 + waveC (2 * τ) + waveC (2 * τ + 1))

theorem waveC_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ waveC q := by
  unfold waveC; split_ifs <;> positivity

theorem waveA_ge_one {τ : ℝ} (k : Fin 2 → ℤ) : 1 ≤ waveA τ k := by
  unfold waveA
  split_ifs
  · exact le_rfl
  · have := Fourier.modeSize_nonneg k
    have : 0 ≤ Fourier.modeSize k ^ τ := by positivity
    linarith

theorem waveS_summable {q σ : ℝ} (hq : 0 ≤ q) (hσ : 0 < σ) :
    Summable (fun k : Fin 2 → ℤ =>
      Fourier.modeSize k ^ q * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
  rcases hq.eq_or_lt with h | h
  · subst h; exact (waveS_zero_eq hσ).summable
  · exact (waveS_le h hσ).1

/-- `S_q(σ) ≤ C_q σ^{-(q+2)}` for `q ≥ 0`, `0 < σ ≤ 1`. -/
theorem waveS_le_waveC {q σ : ℝ} (hq : 0 ≤ q) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    waveS q σ ≤ waveC q / σ ^ (q + 2) := by
  rcases hq.eq_or_lt with h | h
  · subst h
    have h0 := waveS_zero_le hσ
    unfold waveC
    simp only [ite_true, zero_add]
    have h1 : 1 + (Real.pi * σ)⁻¹ ≤ (1 + Real.pi⁻¹) / σ := by
      rw [le_div_iff₀ hσ]
      have : (1 + (Real.pi * σ)⁻¹) * σ = σ + Real.pi⁻¹ := by field_simp
      rw [this]; linarith
    calc waveS 0 σ ≤ (1 + (Real.pi * σ)⁻¹) ^ 2 := h0
      _ ≤ ((1 + Real.pi⁻¹) / σ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = (1 + Real.pi⁻¹) ^ 2 / σ ^ (2 : ℝ) := by
          rw [div_pow, Real.rpow_two]
  · refine (waveS_le h hσ).2.trans (le_of_eq ?_)
    unfold waveC
    simp only [h.ne', ↓reduceIte]
    have hσq : σ ^ (q + 2) = σ * σ ^ (q + 1) := by
      rw [show q + 2 = 1 + (q + 1) by ring, Real.rpow_add hσ, Real.rpow_one]
    rw [hσq, show (q + 1) / (Real.exp 1 * (Real.pi * σ)) =
      (q + 1) / (Real.exp 1 * Real.pi) * σ⁻¹ by field_simp,
      Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hσ.le]
    field_simp

theorem waveS_le_waveBWconst {q τ σ : ℝ} (hq : 0 ≤ q) (hqτ : q ≤ 2 * τ + 1) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) : waveS q σ ≤ waveC q / σ ^ (2 * τ + 3) := by
  refine (waveS_le_waveC hq hσ hσ1).trans ?_
  refine div_le_div_of_nonneg_left (waveC_nonneg hq) (by positivity) ?_
  exact Real.rpow_le_rpow_of_exponent_ge hσ hσ1 (by linarith)

theorem waveBW_pointwise {τ : ℝ} (hτ : 0 ≤ τ) (σ : ℝ) (k : Fin 2 → ℤ) :
    (1 + Fourier.modeSize k) * waveA τ k ^ 2 * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
      2 * (Fourier.modeSize k ^ (0 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ + 1) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
  set x := Fourier.modeSize k with hx
  have hx0 : 0 ≤ x := Fourier.modeSize_nonneg k
  set e := Real.exp (-(2 * Real.pi * σ) * x) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hp1 : x ^ (2 * τ + 1) = x * x ^ (2 * τ) := by
    rw [Real.rpow_add' hx0 (by linarith), Real.rpow_one, mul_comm]
  have hy : 0 ≤ x ^ (2 * τ) := by positivity
  rw [Real.rpow_zero, Real.rpow_one, hp1]
  by_cases hk : k = 0
  · have : waveA τ k = 1 := by simp only [waveA, hk, ↓reduceIte]
    rw [this]
    nlinarith [mul_nonneg hy he0, mul_nonneg hx0 he0, mul_nonneg (mul_nonneg hx0 hy) he0]
  · have hA : waveA τ k = 1 + x ^ τ := by simp only [waveA, hk, ↓reduceIte, hx]
    have hy2 : (x ^ τ) ^ 2 = x ^ (2 * τ) := by
      rw [show 2 * τ = τ * 2 by ring, Real.rpow_mul hx0, Real.rpow_two]
    rw [hA]
    have hyτ : 0 ≤ x ^ τ := by positivity
    have h1 : (1 + x ^ τ) ^ 2 ≤ 2 * (1 + x ^ (2 * τ)) := by
      nlinarith [sq_nonneg (x ^ τ - 1)]
    have h2 : (1 + x) * (1 + x ^ τ) ^ 2 ≤ (1 + x) * (2 * (1 + x ^ (2 * τ))) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    calc (1 + x) * (1 + x ^ τ) ^ 2 * e ≤ (1 + x) * (2 * (1 + x ^ (2 * τ))) * e :=
          mul_le_mul_of_nonneg_right h2 he0
      _ = _ := by ring

/-- `∑ A_k e^{-2π|k|₁σ} ≤ B^W_σ`, and `B^W_σ` is a convergent series
(blueprint `bpW:w4:lattice` (iv), first claim). -/
theorem waveBW_summable {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) :
    Summable (fun k : Fin 2 → ℤ => (1 + Fourier.modeSize k) * waveA τ k ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
  have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ (1 + Fourier.modeSize k) * waveA τ k ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := fun k => by
    have := Fourier.modeSize_nonneg k; positivity
  have hs : Summable (fun k : Fin 2 → ℤ =>
      2 * (Fourier.modeSize k ^ (0 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ + 1) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k))) :=
    (((((waveS_summable le_rfl hσ).add (waveS_summable zero_le_one hσ)).add
      (waveS_summable (by linarith) hσ)).add (waveS_summable (by linarith) hσ))).mul_left 2
  exact Summable.of_nonneg_of_le hnn (waveBW_pointwise hτ σ) hs

theorem waveSum_A_le_waveBW {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) :
    Summable (fun k : Fin 2 → ℤ => waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) ∧
      ∑' k : Fin 2 → ℤ, waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
        waveBW τ σ := by
  have hB := waveBW_summable hτ hσ
  have hle : ∀ k : Fin 2 → ℤ, waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) ≤
      (1 + Fourier.modeSize k) * waveA τ k ^ 2 *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := by
    intro k
    have hA := waveA_ge_one (τ := τ) k
    have hx := Fourier.modeSize_nonneg k
    have : waveA τ k ≤ (1 + Fourier.modeSize k) * waveA τ k ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) :=
    fun k => by have := waveA_ge_one (τ := τ) k; positivity
  have hs := Summable.of_nonneg_of_le hnn hle hB
  exact ⟨hs, Summable.tsum_le_tsum hle hs hB⟩

/-- **The lattice constant** (blueprint `bpW:w4:lattice` (iv)): for `τ ≥ 0`, `0 < σ ≤ 1`,
`B^W_σ ≤ b_W(τ) σ^{-(2τ+3)}`. -/
theorem waveBW_le {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    waveBW τ σ ≤ waveBWconst τ / σ ^ (2 * τ + 3) := by
  have hs := waveBW_summable hτ hσ
  have h0 := waveS_summable (q := 0) le_rfl hσ
  have h1 := waveS_summable (q := 1) zero_le_one hσ
  have h2 := waveS_summable (q := 2 * τ) (by linarith) hσ
  have h3 := waveS_summable (q := 2 * τ + 1) (by linarith) hσ
  have hsum := ((h0.add h1).add h2).add h3
  have hle := Summable.tsum_le_tsum (waveBW_pointwise hτ σ) hs (hsum.mul_left 2)
  unfold waveBW
  refine hle.trans ?_
  have e : ∑' k : Fin 2 → ℤ,
      (Fourier.modeSize k ^ (0 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) +
        Fourier.modeSize k ^ (2 * τ + 1) * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) =
      waveS 0 σ + waveS 1 σ + waveS (2 * τ) σ + waveS (2 * τ + 1) σ := by
    rw [((h0.add h1).add h2).tsum_add h3, (h0.add h1).tsum_add h2, h0.tsum_add h1]; rfl
  rw [tsum_mul_left, e]
  have b0 := waveS_le_waveBWconst (q := 0) (τ := τ) le_rfl (by linarith) hσ hσ1
  have b1 := waveS_le_waveBWconst (q := 1) (τ := τ) zero_le_one (by linarith) hσ hσ1
  have b2 := waveS_le_waveBWconst (q := 2 * τ) (τ := τ) (by linarith) (by linarith) hσ hσ1
  have b3 := waveS_le_waveBWconst (q := 2 * τ + 1) (τ := τ) (by linarith) le_rfl hσ hσ1
  unfold waveBWconst
  rw [mul_div_assoc, add_div, add_div, add_div]
  linarith

end KAM.Wave
