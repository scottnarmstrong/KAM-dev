/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.ExtFlow
public import KAM.Nekhoroshev.Partial.Homological
public import KAM.Weighted.Projections

/-!
# STAGING STUB (lane N): signed `iterative` only, proof pending
-/

@[expose] public noncomputable section

open Set
open KAM.Weighted KAM.NormalForm

namespace KAM.Nekhoroshev

variable {n k : ℕ}

theorem iterative (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ K α p δ : ℝ}
    (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) (Λ : Set (Fin n → ℤ))
    (hR : 0 < ρ) (hR' : 2*ρ < R) (hs : 0 < σ) (hs' : 2*σ < s)
    (hSL : slowLoss b.c ρ σ k) (hc : 0 < b.c) (hα : 0 < α) (hp : 1 < p) (hK : 0 ≤ K)
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/conjExp p))
    (hδ : 0 ≤ δ) (hf : InClass b.base R s f) (hfb : WBound b.base R s f δ)
    (hsmall : δ ≤ 2*Real.pi*α*ρ*σ/(4*conjExp p))
    {N : ℕ} (gj : Fin N → EC n k → ℂ) (Rj sj Uj : Fin N → ℝ)
    (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j) (hUj : ∀ j, 0 ≤ Uj j)
    (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j)) :
    let q := conjExp p
    let φ := homGenerator K Λ h f
    let Φ := extFlow b R s ρ σ φ 1
    let g := fun z => ∑ j, gj j z
    let gp := g+projMode Λ (truncate K f)
    DifferentiableOn ℂ Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) ∧
    MapsTo Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) (Dom n b.base (R-ρ) (s-σ)) ∧
    (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2), ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), extFlow b R s ρ σ φ (-1) (Φ z) = z) ∧
    ∃ fp : EC n k → ℂ,
      InClass b.base (R-2*ρ) (s-2*σ) fp ∧
      (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), liftFast h (Φ z)+g (Φ z)+f (Φ z) = liftFast h z+gp z+fp z) ∧
      WBound b.base (R-2*ρ) (s-2*σ) fp
        ((1-2*q*δ/(2*Real.pi*α*ρ*σ))⁻¹*
          (q/(2*Real.pi*α*ρ*σ)*((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)+
            Real.exp (-2*Real.pi*K*σ))*δ) ∧
      ExtCanonical b.c (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) Φ ∧
      Set.InjOn Φ (Dom n b.base (R-2*ρ) (s-2*σ)) ∧
      WBound b.base (R-2*ρ) (s-2*σ) (gp-g) δ ∧
      (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2),
        ‖(Φ z).1-z.1‖ ≤ q*δ/(2*Real.pi*α*ρ) ∧
        ‖fastAction (Φ z)-fastAction z‖ ≤ q*δ/(Real.exp 1*2*Real.pi*α*σ) ∧
        ‖slowPair (Φ z)-slowPair z‖ ≤ q*δ/(16*k*2*Real.pi*α*σ)) ∧
      ((∀ j, j ∈ Λ ↔ -j ∈ Λ) →
        (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
          (h (KAM.realInclusion n I)).im = 0) →
        extReal (Dom n b.base R s) g → extReal (Dom n b.base R s) f →
        extReal (Dom n b.base R s) φ ∧ extReal (Dom n b.base (R-2*ρ) (s-2*σ)) gp ∧
        extReal (Dom n b.base (R-2*ρ) (s-2*σ)) fp ∧
        ∀ z : ER n k, extCx z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2) →
          extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := by
  sorry

end KAM.Nekhoroshev

end
