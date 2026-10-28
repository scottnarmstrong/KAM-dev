/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Setting
public import KAM.Planetary.PlanarTorsion.PairCoefficients

/-!
# Planar quartic torsion: the six quartic coefficients (definition)

Blueprint P, Part 11b (`bpP:p11b:quartic-explicit`): `p11c_coeffs p a` is the vector
`(c₁, …, c₆)` of the displayed formulas in the pair coefficients `A, B, p₁, …, p₆`, with
`pref = -G m₁ m₂ / a₂` and the actions `Λ_i = m_i √(κ a_i)`; the declaration is copied verbatim
from the signature file of the P11C design.
-/

@[expose] public noncomputable section
open Real
namespace KAM.Planetary

def p11c_coeffs (p : PlanarData) (a : Fin 2 → ℝ) : Fin 6 → ℝ :=
  let I := p.actions a
  let A := p11c_pairCoeffs (a 0 / a 1)
  let pref := -p.G * p.m 0 * p.m 1 / a 1
  ![pref * (A 2 - A 0 / 4) / (I 0 ^ 2), pref * (A 3 - A 0 / 4) / (I 1 ^ 2),
    pref * A 4 / (I 0 * I 1), pref * A 5 / (I 0 * I 1),
    pref * (A 6 - A 1 / 8) / (I 0 ^ (3 / 2 : ℝ) * I 1 ^ (1 / 2 : ℝ)),
    pref * (A 7 - A 1 / 8) / (I 0 ^ (1 / 2 : ℝ) * I 1 ^ (3 / 2 : ℝ))]

end KAM.Planetary

end
