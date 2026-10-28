/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Weighted.Projections
public import KAM.Nekhoroshev.NormalForm.Setting

/-!
# STAGING STUB (lane N): signed `nf` only, proof pending
-/

@[expose] public noncomputable section

open Set
open KAM.Weighted KAM.NormalForm

namespace KAM.Nekhoroshev

variable {n k : ℕ}

theorem nf (b : PartialBlock n k) {s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ} (ha : ExtNFHyp b s K α L p ε Λ h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K)) :
    ∃ Ψ : EC n k → EC n k, ∃ g fs : EC n k → ℂ,
      DifferentiableOn ℂ Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
      MapsTo Ψ (Dom n b.base (b.rB/2) (s/6)) (Dom n b.base b.rB s) ∧
      Set.InjOn Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
      ExtCanonical b.c (Dom n b.base (b.rB/2) (s/6)) Ψ ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6), ∀ ℓ : Fin n → ℤ,
        Ψ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Ψ z+((fun i => (ℓ i:ℂ)),0)) ∧
      (∀ z : ER n k, extCx z ∈ Dom n b.base (b.rB/2) (s/6) →
        extCx (extRe (Ψ (extCx z))) = Ψ (extCx z)) ∧
      ext_class b (b.rB/2) (s/6) g ∧ ext_class b (b.rB/2) (s/6) fs ∧
      (∀ J ∈ polyNbhd b.base (b.rB/2), ∀ j : Fin n → ℤ,
        j ∉ Λ ∩ zBall n K → coeff g J j = 0) ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6), liftFast h (Ψ z)+f (Ψ z) = liftFast h z+g z+fs z) ∧
      WBound b.base (b.rB/2) (s/6) (g-projMode Λ (truncate K f))
        (16*(2*conjExp p*K/(α*b.rB))*ε^2) ∧
      WBound b.base (b.rB/2) (s/6) fs (Real.exp (-(2*Real.pi*K*s)/6)*ε) ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6),
        ‖fastAction (Ψ z)-fastAction z‖ ≤ conjExp p*K*ε/α ∧
        ‖(Ψ z).1-z.1‖ ≤ 10*conjExp p*ε/(2*Real.pi*α*b.rB) ∧
        ‖slowPair (Ψ z)-slowPair z‖ ≤ conjExp p*K*ε/(8*α)) := by
  sorry

end KAM.Nekhoroshev

end
