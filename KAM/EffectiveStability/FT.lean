/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.FT.Basic
public import KAM.EffectiveStability.FT.Deriv
public import KAM.EffectiveStability.FT.Bracket
public import KAM.EffectiveStability.FT.Bound

/-!
# Fourier–Taylor polynomials (track B, B4-FT)

Facade importing `FT.Basic` (algebra, normalizer, identity checker, typing), `FT.Deriv` (formal
derivatives, smoothness, periodicity), `FT.Bracket` (Poisson bracket, `ad` powers, Lie sums) and
`FT.Bound` (computable majorants, angle-drift bound, smoke tests).
-/

public section
