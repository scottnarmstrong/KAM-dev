/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Ball

/-!
# Ball arithmetic tests

Kernel evaluations of `Slp.balls` on the jet programs of small expressions (exact rational
backend, `n = 1`): `exp 2`, `exp` of a cosine mode with ball radius `> 1`, and `cos` of a large
action ball all succeed (the count `cexpHalvings` makes the range reduction pass); a quotient by
an action ball containing `0` fails closed. Each of the three successes is paired with
`Slp.val_mem_ball` (every slot ball contains the exact slot value on the certified domain).
-/

public section

namespace KAM.Certificate

/-- The weight used by the tests (`ρ = 1/4`, `e^{π/2} < 5`). -/
def testWeight : CertWeight := ⟨1 / 4, 5⟩

theorem ballTest_weight : checkWeight testWeight 4 12 = true := by decide +kernel

theorem ballTest_exp_const :
    ((HamExpr.exp (.const 2) : HamExpr 1).jet.prog.balls 1 testWeight [0] [1] 8).isSome = true := by
  decide +kernel

/-- The balls of `exp 2` exist and contain the exact slot values. -/
theorem ballTest_exp_const_mem {z : (Fin 1 → ℂ) × (Fin 1 → ℂ)}
    (hz : z ∈ certDomain 1 testWeight.rho [0] [1]) :
    ∃ bs, (HamExpr.exp (.const 2) : HamExpr 1).jet.prog.balls 1 testWeight [0] [1] 8 = some bs ∧
      ∀ i < bs.length, ‖(HamExpr.exp (.const 2) : HamExpr 1).jet.prog.val 1 z i -
        (bs.getD i (⟨0, 0⟩, 0)).1.toC‖ ≤ (bs.getD i (⟨0, 0⟩, 0)).2 := by
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp ballTest_exp_const
  exact ⟨bs, hbs, fun i hi =>
    Slp.val_mem_ball _ (s := 4) (N := 12) ballTest_weight hbs hz i hi⟩

theorem ballTest_exp_cos_mode :
    ((HamExpr.exp (.cosMode [1]) : HamExpr 1).jet.prog.balls 1 testWeight [0] [1] 8).isSome =
      true := by
  decide +kernel

/-- The balls of `exp_cos_mode` exist and contain the exact slot values. -/
theorem ballTest_exp_cos_mode_mem {z : (Fin 1 → ℂ) × (Fin 1 → ℂ)}
    (hz : z ∈ certDomain 1 testWeight.rho [0] [1]) :
    ∃ bs, (HamExpr.exp (.cosMode [1]) : HamExpr 1).jet.prog.balls 1 testWeight [0] [1] 8 = some bs ∧
      ∀ i < bs.length, ‖(HamExpr.exp (.cosMode [1]) : HamExpr 1).jet.prog.val 1 z i -
        (bs.getD i (⟨0, 0⟩, 0)).1.toC‖ ≤ (bs.getD i (⟨0, 0⟩, 0)).2 := by
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp ballTest_exp_cos_mode
  exact ⟨bs, hbs, fun i hi =>
    Slp.val_mem_ball _ (s := 4) (N := 12) ballTest_weight hbs hz i hi⟩

theorem ballTest_cos_large_action :
    ((HamExpr.cos (.action 0) : HamExpr 1).jet.prog.balls 1 testWeight [20] [1 / 10] 8).isSome =
      true := by
  decide +kernel

/-- The balls of `cos_large_action` exist and contain the exact slot values. -/
theorem ballTest_cos_large_action_mem {z : (Fin 1 → ℂ) × (Fin 1 → ℂ)}
    (hz : z ∈ certDomain 1 testWeight.rho [20] [1 / 10]) :
    ∃ bs, (HamExpr.cos (.action 0) : HamExpr 1).jet.prog.balls 1 testWeight [20] [1 / 10] 8 =
        some bs ∧
      ∀ i < bs.length, ‖(HamExpr.cos (.action 0) : HamExpr 1).jet.prog.val 1 z i -
        (bs.getD i (⟨0, 0⟩, 0)).1.toC‖ ≤ (bs.getD i (⟨0, 0⟩, 0)).2 := by
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp ballTest_cos_large_action
  exact ⟨bs, hbs, fun i hi =>
    Slp.val_mem_ball _ (s := 4) (N := 12) ballTest_weight hbs hz i hi⟩

theorem ballTest_div_ok :
    ((HamExpr.div (.const 1) (.action 0) : HamExpr 1).jet.prog.balls 1 testWeight [2] [1] 8).isSome
      = true := by
  decide +kernel

theorem ballTest_div_fails_closed :
    (HamExpr.div (.const 1) (.action 0) : HamExpr 1).jet.prog.balls 1 testWeight [2] [2] 8 =
      none := by
  decide +kernel

end KAM.Certificate
