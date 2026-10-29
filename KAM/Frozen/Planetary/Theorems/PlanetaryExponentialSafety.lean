/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import KAM.Frozen.Planetary.Defs.MovingHamiltonian
public import KAM.Frozen.Planetary.Defs.BarycentricPositions
public import KAM.Frozen.Planetary.Defs.BarycentricVelocities
public import KAM.Frozen.Planetary.Defs.ActualMasses
public import KAM.Frozen.Planetary.Defs.PairBounds
public import KAM.Frozen.Planetary.Defs.NoCollision
public import KAM.Frozen.Planetary.Defs.SecularAverage
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.Slow
public import KAM.Frozen.Planetary.Defs.OscillatorAction
public import KAM.Frozen.Iso.Defs.IsHamiltonianSolutionOn
public import KAM.Frozen.Planetary.Defs.KeplerAxis
public import KAM.Frozen.Planetary.Defs.KeplerEccVector
public import KAM.Frozen.Planetary.Defs.TotalMomentum
public import KAM.Frozen.Planetary.Defs.LowAMDRegion
public import KAM.Frozen.Planetary.Defs.AMDBox
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Frozen.Planetary.Defs.IsMovingSolutionOn
public import KAM.Frozen.Planetary.Defs.IsNewtonSolutionOn
public import KAM.Frozen.Planetary.Defs.MovingUniqueOn
public import KAM.Frozen.Planetary.Defs.PlanetaryTimeExponent
public import KAM.Frozen.Planetary.Defs.PlanetaryDriftExponent
import KAM.Provider.Planetary.PlanetaryExponentialSafety

/-!
# Frozen theorem `KAM.Planetary.planetaryExponentialSafety`

Owner-approved on 2026-10-27 (decision D25). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.planetaryExponentialSafety` when the provider
`KAM.Provider.Planetary.PlanetaryExponentialSafety` is complete (sealing).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

/-- P-EXP-SAFE: planar moving-Sun specialization of Nek77 Thm 12.3, pp. 55--56.
Constants precede μ and every initial datum in the fixed region. The symmetric horizon,
heliocentric-canonical elements and explicit geometric bounds are documented deductions. -/
theorem planetaryExponentialSafety {n : ℕ} (hn : 2 ≤ n)
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
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.planetaryExponentialSafety hn B hB
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary

end
-- FROZEN_ANCHOR_SUFFIX_END
