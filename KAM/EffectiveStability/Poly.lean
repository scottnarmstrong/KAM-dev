/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Coeff
public import KAM.EffectiveStability.Poly.Basic
public import KAM.EffectiveStability.Poly.Deriv
public import KAM.EffectiveStability.Poly.Bracket
public import KAM.EffectiveStability.Poly.Bound
public import KAM.EffectiveStability.Poly.Lie

/-!
# Cartesian polynomials with exact coefficients (track B, B2-POLY, B3-COEF)

Facade importing `Poly.Coeff` (the coefficient class `CertCoeff` with instances `ℚ` and `QSqrt2`),
`Poly.Basic` (algebra, `cartNormalize`, `cartEqCheck`), `Poly.Deriv` (formal
partial derivatives with analytic meaning), `Poly.Bracket` (Poisson bracket), `Poly.Bound`
(computable sup bounds, drift bound, radius bridge, smoke tests) and `Poly.Lie` (finite Lie sums,
action substitution).
-/

public section
