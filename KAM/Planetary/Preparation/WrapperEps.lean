/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperTubeMain
public import KAM.Planetary.Preparation.WrapperDatum
public import KAM.Planetary.Preparation.WrapperTransport
public import KAM.Planetary.Preparation.WrapperMeasure
public import KAM.Planetary.Newtonian.AssemblyNodes

/-!
# The wrapper at fixed `ε` (P11A-P10, `stepP:p11:wr-tor`, `wr-meas`)

Given a family of lattice tori of `Ĥ_ε` with displacement at most `1/2`, the image of all of them
under `Ξ_ε` is a Borel set of positive finite measure in the circular tube, through every point of
which passes a physical torus of `H_fix` inside the set.
-/

@[expose] public noncomputable section
open Set MeasureTheory
namespace KAM.Planetary

section Eps

variable {n : ℕ}

theorem p11_phaseCast_cancel {d e : ℕ} (h : d = e) (x : Phase d) :
    KAM.Kepler.phaseCast h.symm (KAM.Kepler.phaseCast h x) = x := by
  subst h; ext i <;> rfl

theorem p11_wr_link {D : P11Physical n} {nu eps c : ℝ} {Q : P11PreparedData n}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) (hspec : P11PreparedFullSpec D nu eps c Q)
    {z : Phase (n+n)} (hz : z ∈ p11WrO D) :
    fixedHamiltonian D.G D.m0 D.m eps (p11WrChain D nu eps z) =
      eps*(Q.N (KAM.realInclusion (n+n) z.2) + Q.P (KAM.realInclusion₂ (n+n) z)).re := by
  obtain ⟨⟨-, hch⟩, -, -, -, -, -, -, -, -, -, -, -, -, hHam⟩ := hspec.1
  rw [← (hch z hz).trans (p11_wr_chain_eq hC hF hS heps hpe hsm hz)]
  exact hHam z hz

end Eps

end KAM.Planetary

end
