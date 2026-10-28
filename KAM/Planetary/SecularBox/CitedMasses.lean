/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularBox.Safety
public import KAM.Planetary.SecularBox.Numerics

/-!
# Secular box at the cited decimal masses

`sb_cited` (blueprint `bpP:p14:sb-cited`, step `sb-ci-1`): the ordinary library specialization of
`sb_safety` at the mass ratio `476/1591` and `mu = 4773/5000000`. The decimal model of
Figueras--Haro (arXiv:2403.10152v1 §4 p. 6) has `μ = 0.0009546` and `μ * mS = 0.0002856`; the
exact identity `mu * saturn = 357/1250000` is `sbCited_mass_identity`.
-/

public section

namespace KAM.Planetary

/-- The decimal masses are exact: `mu * saturn = 0.0002856`. -/
theorem sbCited_mass_identity :
    (4773 / 5000000 : ℝ) * (476 / 1591) = 357 / 1250000 := by norm_num

/-- Exact frozen type, ordinary library assembly. -/
theorem sb_cited (w0 : Phase (2 + 2))
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
  sb_safety (476 / 1591) (4773 / 5000000) (by constructor <;> norm_num) (by norm_num) w0 hw0

end KAM.Planetary
