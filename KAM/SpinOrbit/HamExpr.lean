/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Expr.Basic
public import KAM.SpinOrbit.Hamiltonian

/-!
# The lunar Hamiltonian as an expression (track SO, package SO-HAMX)

`soHamExpr : HamExpr 2` is `𝓗 = J + p²/2 - ε Σ_{m=1}^7 A_m cos (2π (2q - mφ))` in the expression
language, with the exact rational coefficients `soEpsQ`, `soAQ`.

* `soHamExpr_eval`: its evaluation is the complexified lunar Hamiltonian `soHC`.
* `soHamExpr_clock`: the derivative in the clock action direction `J` is `1`.
-/

@[expose] public noncomputable section

namespace KAM.SpinOrbit

open KAM KAM.Certificate

/-- `𝓗` in the expression language: `J + p²/2 + Σ_m (-ε A_m) cos(2π(2q - mφ))`. -/
def soHamExpr : HamExpr 2 :=
  .add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
    ((List.range 7).foldr (fun m acc =>
      .add (.mul (.const (-soEpsQ * soAQ (m + 1))) (.cosMode [2, -((m : ℤ) + 1)])) acc)
      (.const 0)))

/-- The evaluation of the mode sum, term by term. -/
theorem soHamExpr_eval_foldr (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (l : List ℕ) :
    (l.foldr (fun (m : ℕ) (acc : HamExpr 2) =>
      .add (.mul (.const (-soEpsQ * soAQ (m + 1))) (.cosMode [2, -((m : ℤ) + 1)])) acc)
      (.const 0)).eval z =
      (l.map fun m => ((-soEpsQ * soAQ (m + 1) : ℚ) : ℂ) *
        Complex.cos (2 * Real.pi * (2 * z.1 0 - ((m : ℂ) + 1) * z.1 1))).sum := by
  induction l with
  | nil => simp [HamExpr.eval]
  | cons m l ih =>
    simp only [List.foldr_cons, HamExpr.eval, ih, List.map_cons, List.sum_cons]
    congr 2
    simp [modePhase, certKeyFun, Fin.sum_univ_two]
    congr 1
    ring

theorem soHamExpr_list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem soHamExpr_eval (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soHamExpr.eval z = soHC z := by
  have hs : ((List.range 7).map fun m => ((-soEpsQ * soAQ (m + 1) : ℚ) : ℂ) *
        Complex.cos (2 * Real.pi * (2 * z.1 0 - ((m : ℂ) + 1) * z.1 1))).sum =
      soVC (z.1 0) (z.1 1) := by
    have hm : soModes = Finset.image (· + 1) (Finset.range 7) := by decide
    rw [soHamExpr_list_sum_range, soVC, hm,
      Finset.sum_image (by intro a _ b _ h; simpa using h), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [soA_eq_ratCast, soEps_eq_ratCast]
    push_cast
    ring_nf
  simp only [soHamExpr, HamExpr.eval, soHamExpr_eval_foldr, hs, soHC]
  push_cast
  ring

theorem soHamExpr_clock (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ soHamExpr.eval z (phaseBasis (.inr 1)) = 1 := by
  have h : soHamExpr.eval = soHC := funext soHamExpr_eval
  rw [h, fderiv_soHC_apply, phaseBasis_inr]
  simp

end KAM.SpinOrbit

end
