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

/-- `Ξ_ε` with codomain reindexed to `Phase (n+n)`, so that Part 1 applies. -/
def p11WrXi (D : P11Physical n) (nu eps : ℝ) (z : Phase (n+n)) : Phase (n+n) :=
  KAM.Kepler.phaseCast (mul_two n) (p11WrChain D nu eps z)

theorem p11_wr_xi {D : P11Physical n} {nu eps : ℝ}
    (hC : P11SecularSpec D (p11SecularData D))
    (hF : P11FastSpec (p11SecularData D) eps (p11FastData D eps))
    (hS : P11SlowSpec D nu eps (p11SlowConstant D nu) (p11SlowData D nu eps))
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 (p11SecularData D) nu eps)
    (hsm : 256*eps < (p11SecularData D).rz^2) :
    IsChart eps (p11WrXi D nu eps) (p11WrO D) ∧
    (∀ z ∈ p11WrO D, ∀ k : Fin (n+n) → ℤ, z + KAM.ODE.angleShift k ∈ p11WrO D ∧
      p11WrXi D nu eps (z + KAM.ODE.angleShift k) = p11WrXi D nu eps z) ∧
    (∀ z ∈ p11WrO D, ∀ z' ∈ p11WrO D, p11WrXi D nu eps z' = p11WrXi D nu eps z →
      ∃ m : Fin (n+n) → ℤ, z' = z + KAM.ODE.angleShift m) := by
  obtain ⟨hAn, hSy, hQ1, hQ2⟩ := p11_wr_chain hC hF hS heps hpe hsm
  have hcast : AnalyticOnNhd ℝ (KAM.Kepler.phaseCast (mul_two n) : Phase (n*2) → Phase (n+n))
      univ := fun x _ => ((KAM.Kepler.phaseCast (mul_two n) :
        Phase (n*2) →L[ℝ] Phase (n+n))).analyticAt x
  refine ⟨⟨hcast.comp hAn (fun _ _ => mem_univ _), ?_⟩, fun z hz k => ?_, fun z hz z' hz' h => ?_⟩
  · have := KAM.Kepler.IsSymplecticOn.comp hSy (KAM.Kepler.phaseCast_symplectic (mul_two n))
      (fun z hz => (hAn z hz).differentiableAt)
      (fun y _ => (KAM.Kepler.phaseCast (mul_two n)).differentiableAt) (fun _ _ => mem_univ _)
    rw [one_mul] at this
    exact this
  · obtain ⟨h1, h2⟩ := hQ1 z hz k
    exact ⟨h1, by unfold p11WrXi; rw [h2]⟩
  · refine hQ2 z hz z' hz' ?_
    unfold p11WrXi at h
    exact (KAM.Kepler.phaseCast (mul_two n)).injective h

end Eps

end KAM.Planetary

end
