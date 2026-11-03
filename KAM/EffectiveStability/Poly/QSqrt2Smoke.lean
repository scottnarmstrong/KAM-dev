/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly

/-!
# Smoke tests of the `ℚ(√2)` coefficient layer (track B, B3-COEF)

Kernel evaluation (`decide +kernel`) of the identity checker over `QSqrt2`: `√2 · √2 = 2`, the
Hénon–Heiles quadratic part `I₁ − (√2/2) I₂` and its bracket with `q₂`, a cubic bracket; the
sup-bound majorant; and the real semantics of the quadratic part through `toReal`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open CartPoly

/-- The Hénon–Heiles quadratic part `I₀ - (√2/2) I₁` (indices `0`, `1`) over `ℚ(√2)`. -/
def hhQuadSmoke : CartPolyK QSqrt2 :=
  cartAdd (cartAction 0) (cartSmul (⟨0, -1 / 2⟩ : QSqrt2) (cartAction 1))

/-- The cubic part `q₀² q₁ - q₁³ / 3` over `ℚ(√2)` (rational coefficients embedded). -/
def hhCubicSmoke : CartPolyK QSqrt2 :=
  cartAdd (cartMul (cartMul (cartQVar 0) (cartQVar 0)) (cartQVar 1))
    (cartSmul (⟨-1 / 3, 0⟩ : QSqrt2) (cartMul (cartMul (cartQVar 1) (cartQVar 1)) (cartQVar 1)))

example : cartEqCheck (cartMul (cartConst (⟨0, 1⟩ : QSqrt2)) (cartConst (⟨0, 1⟩ : QSqrt2)))
    (cartConst (⟨2, 0⟩ : QSqrt2)) = true := by decide +kernel

example : cartEqCheck (cartBracket hhQuadSmoke (cartQVar 1))
    (cartSmul (⟨0, 1 / 2⟩ : QSqrt2) (cartPVar 1)) = true := by decide +kernel

example : cartEqCheck (cartBracket hhQuadSmoke (cartPVar 1))
    (cartSmul (⟨0, -1 / 2⟩ : QSqrt2) (cartQVar 1)) = true := by decide +kernel

example : cartEqCheck (cartBracket hhQuadSmoke (cartQVar 1))
    (cartSmul (⟨0, 1 / 3⟩ : QSqrt2) (cartPVar 1)) = false := by decide +kernel

example : cartEqCheck (cartBracket hhCubicSmoke hhQuadSmoke)
    (cartNeg (cartBracket hhQuadSmoke hhCubicSmoke)) = true := by decide +kernel

example : cartEqCheck (cartBracket (cartAction 0) (cartQVar 0)) (cartNeg (cartPVar 0))
    = true := by decide +kernel

example : cartSupBound hhQuadSmoke [1, 1] [1, 1] ≤ 2 := by decide +kernel

/-- The real semantics of the quadratic part, through `toReal`. -/
theorem hhQuadSmoke_eval (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    cartEval hhQuadSmoke z = KAM.Planetary.oscillatorAction z.2 z.1 0 -
      Real.sqrt 2 / 2 * KAM.Planetary.oscillatorAction z.2 z.1 1 := by
  have h1 : (algebraMap QSqrt2 ℝ) (⟨0, -1 / 2⟩ : QSqrt2) = -(Real.sqrt 2 / 2) := by
    rw [algebraMap_qsqrt2_real]; push_cast; ring
  have a0 : cartEval (cartAction 0 : CartPolyK QSqrt2) z =
      KAM.Planetary.oscillatorAction z.2 z.1 0 := cartEval_action (K := QSqrt2) (0 : Fin 2) z
  have a1 : cartEval (cartAction 1 : CartPolyK QSqrt2) z =
      KAM.Planetary.oscillatorAction z.2 z.1 1 := cartEval_action (K := QSqrt2) (1 : Fin 2) z
  rw [hhQuadSmoke, cartEval_add, cartEval_smul, a0, a1, h1]
  ring

end KAM.EffectiveStability
