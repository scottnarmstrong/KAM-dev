/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Poly.Compose
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The exact modal rotation of `SJSU18-O2` (T2-CONF, N5a)

`V′ = M / N`, the rotation of an integer quaternion times `diag(1, 1, -1)` (phase-1 gate SR-2,
`scripts/sjsu/rigor/results/vprime.json`), with `M` integer and `N = 100000000000001529127486481`.
`V′ᵀ V′ = 1` exactly (`sjsuV_orth`, from `Mᵀ M = N² · 1` in the integers). Coefficients of the
model are `c = cint / 10^E`, `E = 33` (`sjsuE`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube Matrix

/-- The integer matrix `M = N V′` (rows). -/
def sjsuM : Mat3 :=
  ((-48019446297323503922039919, 86727845717025933874035264, 13130634203362617196091152),
    (87703699581007555571901504, 47218835381544392770991857, 8856786381938561031584664),
    (-1481167479775658620383472, -15769031755141582025036904, 98737752559000942891653519))

/-- The common denominator `N` of `V′`. -/
def sjsuN : ℕ := 100000000000001529127486481

/-- The decimal scale of the model coefficients: `c · 10^E` is an integer for every row. -/
def sjsuE : ℕ := 33

/-- `V′ = M / N` as a real matrix. -/
def sjsuV : Matrix (Fin 3) (Fin 3) ℝ := fun j k => (Mat3.entry sjsuM j k : ℝ) / sjsuN

/-- `V′` as a rational matrix. -/
def sjsuVq : Fin 3 → Fin 3 → ℚ := fun j k => (Mat3.entry sjsuM j k : ℚ) / sjsuN

/-- `Mᵀ M = N² · 1` in the integers. -/
theorem sjsuM_orth (k l : Fin 3) :
    Mat3.entry sjsuM 0 k * Mat3.entry sjsuM 0 l + Mat3.entry sjsuM 1 k * Mat3.entry sjsuM 1 l +
      Mat3.entry sjsuM 2 k * Mat3.entry sjsuM 2 l = if k = l then (sjsuN : ℤ) ^ 2 else 0 := by
  revert k l
  decide +kernel

/-- **`V′ᵀ V′ = 1` exactly.** -/
theorem sjsuV_orth : sjsuVᵀ * sjsuV = 1 := by
  have hN : (sjsuN : ℝ) ≠ 0 := by norm_num [sjsuN]
  ext k l
  have h := sjsuM_orth k l
  have hR : (Mat3.entry sjsuM 0 k : ℝ) * Mat3.entry sjsuM 0 l +
      (Mat3.entry sjsuM 1 k : ℝ) * Mat3.entry sjsuM 1 l +
      (Mat3.entry sjsuM 2 k : ℝ) * Mat3.entry sjsuM 2 l = if k = l then (sjsuN : ℝ) ^ 2 else 0 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    rw [this]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, sjsuV,
    Matrix.one_apply]
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, ← add_div, ← add_div, hR]
  split_ifs
  · field_simp
  · simp

end KAM.EffectiveStability.SJSU

end
