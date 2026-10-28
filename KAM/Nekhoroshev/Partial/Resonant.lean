/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.NormalForm.Setting

/-!
# Resonant block stability (Part 11, package N11-M2)

`resonant` (`bpN:p11:resonant`): on a resonant block of a fast-convex Hamiltonian the fast
actions of an orbit that starts at the block centre move by at most `r_B/2` (Euclidean).
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set
open KAM.Weighted KAM.NormalForm

namespace KAM.Nekhoroshev

variable {n k : ℕ}

theorem resonant (b : PartialBlock n k) {s K α m M ε : ℝ}
    {Λ : AddSubgroup (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α (Real.sqrt n*M) (9/8) ε (Λ:Set (Fin n → ℤ)) h f)
    (hconv : FastConvex b.Ic b.rB m M h)
    (hne : NearResonance (Λ:Set (Fin n → ℤ)) h b.Ic (m*b.rB/32))
    (hsmall : ε ≤ m*b.rB^2/2^14)
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*m*b.rB/(240*M*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, euclid (fastAction (y u)-b.Ic) ≤ b.rB/2 := by
  sorry

end KAM.Nekhoroshev

end
