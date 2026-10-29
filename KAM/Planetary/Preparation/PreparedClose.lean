/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedResc
public import KAM.Planetary.Preparation.PreparedData

/-!
# Closeness of the normalised frequency (P11A-P8b2, `stepP:p11:pr-c`)

`p11CloseFun C A ε ρ̃` is the complex `J`-holomorphic vector `(∂_J h - ω, ∂_ρ̃ h / ε - Ω/(2π))`
at fixed `ρ̃`, `h = h₀ + g₂`; its real part on real `J` is `ψ - ϖ`.  The partials of order
`≤ μ̄` are `≤ K (1+c) ε ℓ^Q` (the four contributions of step pr-c).
-/

@[expose] public noncomputable section
open Set Metric
open scoped BigOperators
namespace KAM.Planetary

section Close

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- `(∂_J h - ω, ∂_ρ̃ h / ε - Ω/(2π))` at fixed `ρ̃`. -/
def p11CloseFun (C : P11SecularData n) (A : P11SlowData n) (eps : ℝ) (ρt : P11CVec n) :
    P11CVec n → P11CVec (n + n) := fun J =>
  Fin.append
    (fun k => fderiv ℂ (fun I => A.h0 I + A.g2 I) (Fin.append J ρt) (Pi.single (Fin.castAdd n k) 1)
      - C.omega J k)
    (fun k => fderiv ℂ (fun I => A.h0 I + A.g2 I) (Fin.append J ρt)
      (Pi.single (Fin.natAdd n k) 1) / (eps : ℂ) - (2 * Real.pi : ℂ)⁻¹ * C.Omega J k)

theorem p11_partial_sub {N m : ℕ} {U : Set (P11CVec N)} (hU : IsOpen U) {F G : P11CVec N → P11CVec m}
    (hF : DifferentiableOn ℂ F U) (hG : DifferentiableOn ℂ G U) (α : Fin N → ℕ) {x : P11CVec N}
    (hx : x ∈ U) :
    p11PartialVec α (fun y => F y - G y) x = p11PartialVec α F x - p11PartialVec α G x := by
  set T : P11CVec m →L[ℂ] P11CVec m := (-1 : ℂ) • ContinuousLinearMap.id ℂ (P11CVec m) with hT
  have hGn : DifferentiableOn ℂ (fun y => T (G y)) U := by
    have : DifferentiableOn ℂ ((-1 : ℂ) • G) U := hG.const_smul (-1 : ℂ)
    exact this
  have h1 : (fun y => F y - G y) = F + fun y => T (G y) := by
    funext y; simp [hT, sub_eq_add_neg]
  have h2 := p11_partial_clm hU hG T α hx
  rw [h1, p11_partial_add hU hF hGn α hx]
  show p11PartialVec α F x + p11PartialVec α (fun y => T (G y)) x = _
  rw [h2]
  simp [hT, sub_eq_add_neg]

end Close

end KAM.Planetary

end
