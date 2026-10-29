/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowRates

/-!
# Slow averaging: the literal (B2) conclusion (GAP-E, `stepP:p11:as-b2`)

`slow_b2_literal`: for `K₂ = (3 ν₂ / (π σ₃)) ℓ`, `ℓ = log (1/ε)`, `ν₂ ≥ 1`, and all small `ε`:
`E₂ ≤ α₍₂₎ π ε/(128 K₂)`, the closed form `α₍₂₎ π ε/(128 K₂) = (π γ₀/512) ε² K₂^{-τ₀-1}`,
the ratio of `E₂` to it (`ε^{1/2}` times a power of `ℓ`), and `κ = 2 π K₂ σ₃ = 6 ν₂ ℓ ≥ 6`.
-/

@[expose] public noncomputable section
open Set Filter Topology
namespace KAM.Planetary

/-- `stepP:p11:as-b2` (B2), literally, including `κ = 2π K₂ σ₃ = 6 ν₂ log (1/ε) ≥ 6`. -/
theorem slow_b2_literal (c0 γ τ ν σ : ℝ) (hγ : 0 < γ) (hτ : 0 ≤ τ) (hν : 1 ≤ ν) (hσ : 0 < σ) :
    ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0),
      let K := 3 * ν / (Real.pi * σ) * Real.log (1 / eps)
      c0 * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * τ + 1) ≤
        (eps * (γ / 4 * K ^ (-τ))) * Real.pi * eps / (128 * K) ∧
      (eps * (γ / 4 * K ^ (-τ))) * Real.pi * eps / (128 * K) =
        Real.pi * γ / 512 * eps ^ 2 * K ^ (-τ - 1) ∧
      c0 * eps ^ (5 / 2 : ℝ) * Real.log (1 / eps) ^ (2 * τ + 1) =
        (Real.pi * γ / 512 * eps ^ 2 * K ^ (-τ - 1)) *
          (512 * c0 / (Real.pi * γ) * (3 * ν / (Real.pi * σ)) ^ (τ + 1) *
            (eps ^ (1 / 2 : ℝ) * Real.log (1 / eps) ^ (3 * τ + 2))) ∧
      2 * Real.pi * K * σ = 6 * ν * Real.log (1 / eps) ∧
      6 ≤ 2 * Real.pi * K * σ := by
  have hpi := Real.pi_pos
  have ha : 0 < 3 * ν / (Real.pi * σ) := by positivity
  have h01 : ∀ᶠ eps : ℝ in nhdsWithin 0 (Ioi 0), eps ∈ Ioo (0 : ℝ) (Real.exp (-1)) :=
    Ioo_mem_nhdsGT (Real.exp_pos _)
  filter_upwards [slow_b2_eventually (a := 3 * ν / (Real.pi * σ)) c0 ha hγ hτ, h01]
    with eps h1 h2
  obtain ⟨he0, he1⟩ := h2
  have hl1 : 1 ≤ Real.log (1 / eps) := log_inv_ge_one he0 he1.le
  have hl : 0 < Real.log (1 / eps) := by linarith
  intro K
  have hK : 0 < K := by positivity
  have hκ : 2 * Real.pi * K * σ = 6 * ν * Real.log (1 / eps) := by
    simp only [K]; field_simp; ring
  have hclosed : (eps * (γ / 4 * K ^ (-τ))) * Real.pi * eps / (128 * K) =
      Real.pi * γ / 512 * eps ^ 2 * K ^ (-τ - 1) := by
    rw [Real.rpow_sub hK, Real.rpow_one]
    field_simp
    ring
  refine ⟨h1, hclosed, ?_, hκ, by rw [hκ]; nlinarith⟩
  have hpow : Real.log (1 / eps) ^ (2 * τ + 1) * K ^ (τ + 1) =
      (3 * ν / (Real.pi * σ)) ^ (τ + 1) * Real.log (1 / eps) ^ (3 * τ + 2) := by
    simp only [K]
    rw [Real.mul_rpow ha.le hl.le, ← mul_assoc, mul_comm _ ((3 * ν / (Real.pi * σ)) ^ (τ + 1)),
      mul_assoc, ← Real.rpow_add hl]
    ring_nf
  have hKm : K ^ (-τ - 1) * K ^ (τ + 1) = 1 := by
    rw [← Real.rpow_add hK]; simp
  have he : eps ^ (5 / 2 : ℝ) = eps ^ 2 * eps ^ (1 / 2 : ℝ) := eps_pow_five_half he0
  rw [he]
  have : c0 * (eps ^ 2 * eps ^ (1 / 2 : ℝ)) * Real.log (1 / eps) ^ (2 * τ + 1) =
      c0 * (eps ^ 2 * eps ^ (1 / 2 : ℝ)) * Real.log (1 / eps) ^ (2 * τ + 1) *
        (K ^ (-τ - 1) * K ^ (τ + 1)) := by rw [hKm, mul_one]
  rw [this]
  have hγπ : Real.pi * γ ≠ 0 := by positivity
  calc _ = c0 * (eps ^ 2 * eps ^ (1 / 2 : ℝ)) * K ^ (-τ - 1) *
        (Real.log (1 / eps) ^ (2 * τ + 1) * K ^ (τ + 1)) := by ring
    _ = _ := by rw [hpow]; field_simp
