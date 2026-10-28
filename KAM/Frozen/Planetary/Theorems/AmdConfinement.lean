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
public import KAM.Frozen.Planetary.Defs.KeplerAction
public import KAM.Frozen.Planetary.Defs.KeplerEccVector
public import KAM.Frozen.Planetary.Defs.TotalMomentum
public import KAM.Frozen.Planetary.Defs.PhysicalAMD
public import KAM.Frozen.Planetary.Defs.LowAMDRegion
public import KAM.Frozen.Planetary.Defs.AMDBox
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Frozen.Planetary.Defs.IsMovingSolutionOn
public import KAM.Frozen.Planetary.Defs.IsNewtonSolutionOn
public import KAM.Frozen.Planetary.Defs.MovingUniqueOn
public import KAM.Frozen.Planetary.Defs.StoppedActionBound
import KAM.Provider.Planetary.AmdConfinement

/-!
# Frozen theorem `KAM.Planetary.amdConfinement`

Owner-approved on 2026-10-27 (decision D25). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.amdConfinement` when the provider `KAM.Provider.Planetary.AmdConfinement` is
complete (sealing).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

/-- P-AMD-CONFINEMENT: the stopped analytic input plus exact angular momentum conservation
(derived for the literal moving Hamiltonian) prevents exit and gives continuation.
Round 2 §2 lemmas 1,2,5,6, with the stopped-source correction of round 3. -/
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
        ∀ i, |keplerAction B.mass (z t) i - keplerAction B.mass z0 i| ≤ delta :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.amdConfinement hn B hB mu T delta hmu hT hdelta hmargin hAMD
      z0 hz0 hstop
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary

end
-- FROZEN_ANCHOR_SUFFIX_END
