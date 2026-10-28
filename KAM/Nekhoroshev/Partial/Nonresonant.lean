/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.NormalForm.Setting

/-!
# Nonresonant block stability (Part 11, package N11-M1)

`nonresonant` (`bpN:p11:nonresonant`): on a nonresonant block the fast actions of an orbit
that starts at the block centre and keeps its slow pair in the block move by at most `r_B/2`.
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set
open KAM.Weighted KAM.NormalForm

namespace KAM.Nekhoroshev

variable {n k : ℕ}

theorem nonresonant (b : PartialBlock n k) {s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α L p ε {0} h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, ‖fastAction (y u)-b.Ic‖ ≤ b.rB/2 := by
  sorry

end KAM.Nekhoroshev

end
