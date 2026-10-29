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
public import KAM.Frozen.Planetary.Defs.SecularAMD
public import KAM.Frozen.Planetary.Defs.SecularEccVector
public import KAM.Frozen.Planetary.Defs.EllipsePosition
public import KAM.Frozen.Planetary.Defs.EllipsePhase
public import KAM.Frozen.Planetary.Defs.ExactSecularHamiltonian
public import KAM.Frozen.Planetary.Defs.SecularRegular
public import KAM.Frozen.Planetary.Defs.JupiterSaturnWeights
public import KAM.Frozen.Planetary.Defs.SecularInputBox
import KAM.Provider.Planetary.SecularBoxAtCitedMasses

/-!
# Frozen theorem `KAM.Planetary.secularBoxAtCitedMasses`

Owner-approved on 2026-10-27 (decision D25). This file is frozen: it is hashed in
`manifest/frozen-anchors.json`; any change needs an owner-approved versioned successor. Only the
proof body between the markers may change, and only to `by exact
KAM.Provider.Planetary.secularBoxAtCitedMasses` when the provider
`KAM.Provider.Planetary.SecularBoxAtCitedMasses` is complete (sealing).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Planetary

/-- The decimal model masses of Figueras--Haro, arXiv:2403.10152v1 §4 p. 6:
μ=0.0009546 and μ*mS=0.0002856, exactly. This is a model parameter specialization. -/
theorem secularBoxAtCitedMasses (w0 : Phase (2 + 2))
    (hw0 : SecularInputBox (476 / 1591 : ℝ) w0) :
    ∃ w : ℝ → Phase (2 + 2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights (476 / 1591 :
        ℝ)) (4773 / 5000000 : ℝ))
        Set.univ Set.univ w ∧
      (∀ (U : Set ℝ) (v : ℝ → Phase (2 + 2)), IsOpen U → Convex ℝ U → 0 ∈ U →
        v 0 = w0 →
        KAM.Iso.IsHamiltonianSolutionOn
          (exactSecularHamiltonian (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ))
            Set.univ U v →
        (∀ t ∈ U, SecularRegular (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ) (v t))
          →
        ∀ t ∈ U, v t = w t) ∧
      ∀ t : ℝ,
        SecularRegular (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ) (w t) ∧
        fast (w t).2 = fast w0.2 ∧ secularAMD (w t) = secularAMD w0 ∧
        secularAMD (w t) < (16373 / 2500000 : ℝ) ∧
        (∀ i, planeLength (secularEccVector (w t) i) < (3 / 20 : ℝ)) ∧
        ∀ F : Fin 2 → ℝ,
          (∀ i, (1751 / 400 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) i (F i)) ∧
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) i (F i)) ≤
              (4439 / 400 : ℝ)) ∧
          (399 / 200 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) 1 (F 1)) -
            planeLength (ellipsePosition (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) 0 (F 0)) ∧
          PairBounds (399 / 200 : ℝ) (4439 / 200 : ℝ)
            (barycentricPositions 1 (jupiterSaturnWeights (476 / 1591 : ℝ)) (4773 / 5000000 : ℝ)
              (ellipsePhase (jupiterSaturnWeights (476 / 1591 : ℝ)) (w t) F).1) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact KAM.Provider.Planetary.secularBoxAtCitedMasses w0 hw0
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end KAM.Planetary

end
-- FROZEN_ANCHOR_SUFFIX_END
