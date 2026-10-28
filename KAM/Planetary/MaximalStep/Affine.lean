/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Basic

/-!
# Affine generating functions (P11A-C5/C6 shared definition)

The affine-in-action generating function `p11Affine`, shared by `MaximalStep/HomologicalBracket`
(P11A-C5) and `MaximalStep/AffineFlowBasic` (P11A-C6), which both use the signature definition.
-/

@[expose] public noncomputable section

open scoped BigOperators
namespace KAM.Planetary

/-- Affine generating function in the existing Hamiltonian carrier. -/
def p11Affine {n : ℕ} (p0 : P11CVec n → ℂ) (p1 : P11CVec n → P11CVec n)
    (z : P11Phase n) : ℂ := p0 z.1+∑ i, p1 z.1 i*z.2 i

end KAM.Planetary
