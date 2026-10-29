/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Exponential.Safety

/-!
# Provider for the frozen theorem `KAM.Planetary.planetaryExponentialSafety`

The proof of `KAM.Planetary.planetaryExponentialSafety` is assembled here as
`KAM.Provider.Planetary.planetaryExponentialSafety`, from graph predecessors and approved external
inputs only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other
than the anchor may import it.

Until the signed `KAM.Planetary.expsafe` is proved (it waits for `stopped`, package E11), the
parametric form `planetaryExponentialSafety_of_expsafe` is provided; it takes the signed statement
of `expsafe` (for the given `n` and `hn`) verbatim as its single hypothesis `hexpsafe`. The
provider theorem itself is the one-line assembly
`planetaryExponentialSafety_of_expsafe hn (KAM.Planetary.expsafe hn) B hB`, added once
`expsafe` lands.
-/

@[expose] public noncomputable section

namespace KAM.Provider.Planetary

open KAM.Planetary

/-- The frozen anchor's statement, conditional on the signed `expsafe` statement `hexpsafe`
(verbatim, for the given `n` and `hn`). -/
theorem planetaryExponentialSafety_of_expsafe {n : ℕ} (hn : 2 ≤ n)
    (hexpsafe : ∀ (B : AMDBox n), B.Admissible →
      ∃ muStar c C : ℝ, 0 < muStar ∧ 0 < c ∧ 0 < C ∧
        ∀ mu : ℝ, 0 < mu → mu < muStar →
        ∀ z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD,
        ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧
          (IsMovingSolutionOn B.mass mu (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                    (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧ MovingUniqueOn B.mass mu
                      (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                    (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧
          IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-Real.exp (c * mu ^
            (-planetaryTimeExponent n)))
                    (Real.exp (c * mu ^ (-planetaryTimeExponent n))))
            (fun t => barycentricPositions 1 B.mass mu (z t).1)
            (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
          ∀ t ∈ (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                    (Real.exp (c * mu ^ (-planetaryTimeExponent n)))),
            z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
            totalMomentum (z t) = totalMomentum (z 0) ∧
            (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
              B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
              planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
            PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
          ∀ t : ℝ, |t| ≤ Real.exp (c * mu ^ (-planetaryTimeExponent n)) →
            ∀ i, |keplerAxis B.mass (z t) i - keplerAxis B.mass z0 i| ≤
              C * mu ^ planetaryDriftExponent n)
    (B : AMDBox n) (hB : B.Admissible) :
    ∃ muStar c C : ℝ, 0 < muStar ∧ 0 < c ∧ 0 < C ∧
      ∀ mu : ℝ, 0 < mu → mu < muStar →
      ∀ z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD,
      ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧
        (IsMovingSolutionOn B.mass mu (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧ MovingUniqueOn B.mass mu
                    (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))) z ∧
        IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-Real.exp (c * mu ^
          (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n))))
          (fun t => barycentricPositions 1 B.mass mu (z t).1)
          (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
        ∀ t ∈ (Set.Icc (-Real.exp (c * mu ^ (-planetaryTimeExponent n)))
                  (Real.exp (c * mu ^ (-planetaryTimeExponent n)))),
          z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
          totalMomentum (z t) = totalMomentum (z 0) ∧
          (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
            B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
            planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
          PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
        ∀ t : ℝ, |t| ≤ Real.exp (c * mu ^ (-planetaryTimeExponent n)) →
          ∀ i, |keplerAxis B.mass (z t) i - keplerAxis B.mass z0 i| ≤
            C * mu ^ planetaryDriftExponent n :=
  have _hn := hn
  hexpsafe B hB

end KAM.Provider.Planetary

end
