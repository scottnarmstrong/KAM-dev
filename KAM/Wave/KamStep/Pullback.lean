/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The pull-back estimate: abstract core (`bpW:w5:pullback` step `p-ass`; `bpW:w5:commutator`)

Operator-level core of the pull-back `(φ^t)^* Y = (Dφ^t)^{-1} Y ∘ φ^t`, in an arbitrary normed space
`E`. For two parameters `ξ, ζ` let `A_ξ, A_ζ ∈ L(E)` have inverses `B_ξ, B_ζ` with `‖B‖ ≤ 2`
(`stepInv_sub`: `B_ξ - B_ζ = B_ξ (A_ζ - A_ξ) B_ζ`). With `‖y₁‖ ≤ Y₀`, the sup bound is `2Y₀`
and the `λ`-difference bound is `(9/2 Y₀ + 2 λ Y_L) |ξ-ζ|` (`stepPullback_diff`), which gives
`|(φ^t)^* Y|^λ ≤ 7 |Y|^λ` (`stepPullback_const`). The commutator constant `24 ε M_F/(ση²)` is
`stepCommutator_arith`.
-/

@[expose] public section

namespace KAM.Wave

open ContinuousLinearMap

/-- `B_ξ - B_ζ = B_ξ (A_ζ - A_ξ) B_ζ` for inverses of `A_ξ, A_ζ`. -/
theorem stepInv_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Aξ Aζ Bξ Bζ : E →L[ℂ] E} (h1 : Bξ * Aξ = 1) (h2 : Aζ * Bζ = 1) :
    Bξ - Bζ = Bξ * (Aζ - Aξ) * Bζ := by
  have : Bξ * (Aζ - Aξ) * Bζ = Bξ * (Aζ * Bζ) - (Bξ * Aξ) * Bζ := by
    simp only [mul_sub, sub_mul, mul_assoc]
  rw [this, h1, h2]; simp

/-- **Difference of pull-backs** (`p-ass`): `λ‖B_ξ y₁ - B_ζ y₂‖ ≤ (9/2 Y₀ + 2λ Y_L) d`, given
`λ‖A_ξ - A_ζ‖ ≤ d`, `‖B‖ ≤ 2`, `‖y₁‖ ≤ Y₀` and `λ‖y₁ - y₂‖ ≤ (λ Y_L + Y₀/4) d`. -/
theorem stepPullback_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {lam d Y0 YL : ℝ} {Aξ Aζ Bξ Bζ : E →L[ℂ] E} {y1 y2 : E} (hlam : 0 ≤ lam) (hd : 0 ≤ d)
    (hY0 : 0 ≤ Y0) (h1 : Bξ * Aξ = 1) (h2 : Aζ * Bζ = 1) (hBξ : ‖Bξ‖ ≤ 2) (hBζ : ‖Bζ‖ ≤ 2)
    (hA : lam * ‖Aξ - Aζ‖ ≤ d) (hy1 : ‖y1‖ ≤ Y0)
    (hy : lam * ‖y1 - y2‖ ≤ (lam * YL + Y0 / 4) * d) :
    lam * ‖Bξ y1 - Bζ y2‖ ≤ (9 / 2 * Y0 + 2 * lam * YL) * d := by
  have e : Bξ y1 - Bζ y2 = (Bξ - Bζ) y1 + Bζ (y1 - y2) := by
    simp [sub_apply, map_sub]
  rw [e, stepInv_sub h1 h2]
  have n1 : ‖(Bξ * (Aζ - Aξ) * Bζ) y1‖ ≤ 2 * ‖Aξ - Aζ‖ * 2 * Y0 := by
    calc ‖(Bξ * (Aζ - Aξ) * Bζ) y1‖ ≤ ‖Bξ * (Aζ - Aξ) * Bζ‖ * ‖y1‖ := le_opNorm _ _
      _ ≤ (‖Bξ‖ * ‖Aζ - Aξ‖ * ‖Bζ‖) * Y0 := by
          gcongr
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (2 * ‖Aξ - Aζ‖ * 2) * Y0 := by
          rw [norm_sub_rev Aζ Aξ]
          gcongr
      _ = _ := by ring
  have n2 : ‖Bζ (y1 - y2)‖ ≤ 2 * ‖y1 - y2‖ :=
    (le_opNorm _ _).trans (by gcongr)
  calc lam * ‖(Bξ * (Aζ - Aξ) * Bζ) y1 + Bζ (y1 - y2)‖ ≤
        lam * (2 * ‖Aξ - Aζ‖ * 2 * Y0 + 2 * ‖y1 - y2‖) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add n1 n2)) hlam
    _ = 4 * Y0 * (lam * ‖Aξ - Aζ‖) + 2 * (lam * ‖y1 - y2‖) := by ring
    _ ≤ 4 * Y0 * d + 2 * ((lam * YL + Y0 / 4) * d) := by
        gcongr
    _ = _ := by ring

/-- **Constant of the pull-back** (`p-ass`): `2Y₀ + (9/2 Y₀ + 2λY_L) ≤ 7 (Y₀ + λ Y_L)`. -/
theorem stepPullback_const {lam Y0 YL : ℝ} (hlam : 0 ≤ lam) (hY0 : 0 ≤ Y0) (hYL : 0 ≤ YL) :
    2 * Y0 + (9 / 2 * Y0 + 2 * lam * YL) ≤ 7 * (Y0 + lam * YL) := by
  nlinarith [mul_nonneg hlam hYL]

/-- **Commutator constant** (`bpW:w5:commutator`, step `k-bd`):
`2 · (2/σ) · 6ε · M_F · η⁻² = 24 ε M_F/(ση²)`. -/
theorem stepCommutator_arith {σ η ε M : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    2 * (2 / σ) * (6 * ε) * M / η ^ 2 = 24 * ε * M / (σ * η ^ 2) := by
  field_simp; ring

end KAM.Wave
