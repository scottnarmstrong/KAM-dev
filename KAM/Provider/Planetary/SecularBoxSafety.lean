/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.SecularBox.Safety

/-!
# Provider for the frozen theorem `KAM.Planetary.secularBoxSafety`

The proof of `KAM.Planetary.secularBoxSafety` is assembled here as
`KAM.Provider.Planetary.secularBoxSafety`, from graph predecessors and approved external inputs
only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no module other than the
anchor may import it.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace KAM.Provider.Planetary
open KAM.Planetary

/-- Provider; exact frozen telescope. -/
theorem secularBoxSafety (saturn mu : ℝ)
    (hsaturn : saturn ∈ Set.Icc (29 / 100 : ℝ) (31 / 100 : ℝ)) (hmu : 0 < mu)
    (w0 : Phase (2 + 2)) (hw0 : SecularInputBox saturn w0) :
    ∃ w : ℝ → Phase (2 + 2), w 0 = w0 ∧
      KAM.Iso.IsHamiltonianSolutionOn (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)
        Set.univ Set.univ w ∧
      (∀ (U : Set ℝ) (v : ℝ → Phase (2 + 2)), IsOpen U → Convex ℝ U → 0 ∈ U →
        v 0 = w0 →
        KAM.Iso.IsHamiltonianSolutionOn
          (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) Set.univ U v →
        (∀ t ∈ U, SecularRegular (jupiterSaturnWeights saturn) mu (v t)) →
        ∀ t ∈ U, v t = w t) ∧
      ∀ t : ℝ,
        SecularRegular (jupiterSaturnWeights saturn) mu (w t) ∧
        fast (w t).2 = fast w0.2 ∧ secularAMD (w t) = secularAMD w0 ∧
        secularAMD (w t) < (16373 / 2500000 : ℝ) ∧
        (∀ i, planeLength (secularEccVector (w t) i) < (3 / 20 : ℝ)) ∧
        ∀ F : Fin 2 → ℝ,
          (∀ i, (1751 / 400 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ∧
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) i (F i)) ≤
              (4439 / 400 : ℝ)) ∧
          (399 / 200 : ℝ) ≤
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 1 (F 1)) -
            planeLength (ellipsePosition (jupiterSaturnWeights saturn) (w t) 0 (F 0)) ∧
          PairBounds (399 / 200 : ℝ) (4439 / 200 : ℝ)
            (barycentricPositions 1 (jupiterSaturnWeights saturn) mu
              (ellipsePhase (jupiterSaturnWeights saturn) (w t) F).1) :=
  by exact KAM.Planetary.sb_safety saturn mu hsaturn hmu w0 hw0

end KAM.Provider.Planetary

end
