/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.SecularBox.CitedMasses

/-!
# Provider for the frozen theorem `KAM.Planetary.secularBoxAtCitedMasses`

The proof of `KAM.Planetary.secularBoxAtCitedMasses` is assembled here as
`KAM.Provider.Planetary.secularBoxAtCitedMasses`, from graph predecessors and approved external
inputs only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other
than the anchor may import it.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Provider.Planetary
open KAM.Planetary

/-- Provider; exact frozen telescope. -/
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
  by exact KAM.Planetary.sb_cited w0 hw0

end KAM.Provider.Planetary

end
