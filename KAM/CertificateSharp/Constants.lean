/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.Constants
public import KAM.Strip.CohomologicalRussmann
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Rational mirrors of the sharp isoenergetic constants

For `n, τ ∈ ℕ` (Rüssmann's data `κ = τ`, `a = 2τ`) every constant of
`KAM/Sharp/Constants.lean` and `KAM/Iso/Sharp/Constants.lean` has a kernel-computable rational
mirror (suffix `Q`): the same formula over `ℚ`, `c_R` replaced by the rational upper bound `cRRQ` of
`KAM.cohConstR n τ` (`cohConstR_le_cRRQ`), and the real powers by natural powers.
`sharpIsoC1_le_sharpIsoC1Q`, `sharpIsoC2_le_…`, `sharpIsoC3_le_…` state that the real sharp
constants at rational data are at most their mirrors.

Only `c_R` is inexact: the other data are the casts of the rational certificate parameters.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Sharp KAM.Iso.Sharp

/-! ### The coherence constant -/

/-- A rational `≥ √x` (AM–GM with a rational `s ≈ √x`). -/
def sqrtUpQ (x : ℚ) : ℚ :=
  let s : ℚ := ((Nat.sqrt ⌈x * 1000000⌉₊ + 1 : ℕ) : ℚ) / 1000
  (x / s + s) / 2

theorem sqrt_le_sqrtUpQ (x : ℚ) (hx : 0 ≤ x) : Real.sqrt (x : ℝ) ≤ (sqrtUpQ x : ℝ) := by
  unfold sqrtUpQ
  set s : ℚ := ((Nat.sqrt ⌈x * 1000000⌉₊ + 1 : ℕ) : ℚ) / 1000 with hs
  have hs0 : (0 : ℝ) < (s : ℝ) := by rw [hs]; push_cast; positivity
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  push_cast
  have h1 := Real.sq_sqrt hx0
  have h2 := Real.sqrt_nonneg (x : ℝ)
  have h3 : 2 * (s : ℝ) * Real.sqrt (x : ℝ) ≤ (x : ℝ) + (s : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (x : ℝ) - (s : ℝ))]
  have : Real.sqrt (x : ℝ) ≤ ((x : ℝ) / s + s) / 2 := by
    rw [div_add' _ _ _ hs0.ne', div_div, le_div_iff₀ (by positivity)]
    nlinarith
  exact this

/-- The radicand of `cohConstR` with `π`, `e` replaced by `3.141592`, `2.718`. -/
def cRRadQ (n τ : ℕ) : ℚ :=
  2 ^ n * (6 * (1 + 2 ^ τ) * (2 * τ / (2718 / 1000 * (3141592 / 1000000 : ℚ))) ^ (2 * τ))

/-- A kernel-computable upper bound for `cohConstR n τ`. -/
def cRRQ (n τ : ℕ) : ℚ := (2 * (3141592 / 1000000 : ℚ))⁻¹ * sqrtUpQ (cRRadQ n τ)

theorem cohConstR_le_cRRQ (n τ : ℕ) : cohConstR n (τ : ℝ) ≤ cRRQ n τ := by
  have hπ : ((3141592 / 1000000 : ℚ) : ℝ) < Real.pi := by
    have := Real.pi_gt_d6
    push_cast
    linarith
  have he : ((2718 / 1000 : ℚ) : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    push_cast
    linarith
  have hπ0 : (0 : ℝ) < ((3141592 / 1000000 : ℚ) : ℝ) := by norm_num
  have he0 : (0 : ℝ) < ((2718 / 1000 : ℚ) : ℝ) := by norm_num
  have hrad : (2 : ℝ) ^ n * (6 * (1 + 2 ^ (τ : ℝ)) *
      (2 * (τ : ℝ) / (Real.exp 1 * Real.pi)) ^ (2 * (τ : ℝ))) ≤ (cRRadQ n τ : ℝ) := by
    have h2 : (2 * (τ : ℝ)) = ((2 * τ : ℕ) : ℝ) := by push_cast; ring
    rw [h2, Real.rpow_natCast, Real.rpow_natCast]
    have h2' : (2 * (τ : ℝ) / (Real.exp 1 * Real.pi)) ≤
        2 * τ / (((2718 / 1000 : ℚ) : ℝ) * ((3141592 / 1000000 : ℚ) : ℝ)) := by gcongr
    unfold cRRadQ
    push_cast at h2' ⊢
    gcongr
  unfold cohConstR cRRQ
  push_cast
  have h1 : ((2 : ℝ) * Real.pi)⁻¹ ≤ (2 * ((3141592 / 1000000 : ℚ) : ℝ))⁻¹ := by gcongr
  have h3 := (Real.sqrt_le_sqrt hrad).trans (sqrt_le_sqrtUpQ (cRRadQ n τ) (by
    unfold cRRadQ; positivity))
  push_cast at h1 h3 ⊢
  gcongr

end KAM.CertificateSharp
