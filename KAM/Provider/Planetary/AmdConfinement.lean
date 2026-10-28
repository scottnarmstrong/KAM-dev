/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.AMD.Confinement

/-!
# Provider for the frozen theorem `KAM.Planetary.amdConfinement`

The proof of `KAM.Planetary.amdConfinement` is assembled here as
`KAM.Provider.Planetary.amdConfinement`, from graph predecessors and approved external inputs only.
While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.
-/

@[expose] public section

namespace KAM.Provider.Planetary
open KAM.Planetary

/-- Quarantined provider signature; exact frozen telescope. -/
theorem amdConfinement {n : ℕ} (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible)
    (mu T delta : ℝ) (hmu : 0 < mu) (hT : 0 < T) (hdelta : 0 < delta)
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    (hAMD : B.initialAMD + 2 * (n : ℝ) * delta < B.outerAMD)
    (z0 : Phase (n * 2))
    (hz0 : z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD)
    (hstop : StoppedActionBound B mu T delta z0) :
    ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧ (IsMovingSolutionOn B.mass mu (Set.Icc (-T) T) z ∧
      MovingUniqueOn B.mass mu (Set.Icc (-T) T) z ∧
      IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-T) T)
        (fun t => barycentricPositions 1 B.mass mu (z t).1)
        (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
      ∀ t ∈ (Set.Icc (-T) T),
        z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
        totalMomentum (z t) = totalMomentum (z 0) ∧
        (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
          B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
          planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
        PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
      ∀ t ∈ Set.Icc (-T) T,
        physicalAMD B.mass (z t) ≤ B.initialAMD + (n : ℝ) * delta ∧
        ∀ i, |keplerAction B.mass (z t) i - keplerAction B.mass z0 i| ≤ delta := by
  exact KAM.Planetary.amd hn B hB mu T delta hmu hT hdelta hmargin hAMD z0 hz0 hstop

end KAM.Provider.Planetary

end
