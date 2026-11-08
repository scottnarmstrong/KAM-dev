/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.HenonHeiles.Data.Residual

/-!
# The Hénon–Heiles polynomial as a real function (track B, B3-CERT)

`cartEval hhH` over `ℝ` (through the global instance `instAlgebraQSqrt2Real`) is the displayed
function `(q₀² + p₀²)/2 - (√2/2)(q₁² + p₁²)/2 + q₀² q₁ - q₁³/3`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.HenonHeiles

open CartPoly

theorem hhH_eval (w : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    cartEval hhH w = (w.1 0 ^ 2 + w.2 0 ^ 2) / 2 - Real.sqrt 2 / 2 * ((w.1 1 ^ 2 + w.2 1 ^ 2) / 2)
      + w.1 0 ^ 2 * w.1 1 - w.1 1 ^ 3 / 3 := by
  simp only [hhH, cartEval_cons, cartEval_nil, CartMonoK.cartMonoEval, CartMonoK.powProd,
    algebraMap_qsqrt2_real, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, List.getD_cons_zero,
    List.getD_cons_succ, List.getD_nil]
  push_cast
  ring

end KAM.EffectiveStability.HenonHeiles

end
