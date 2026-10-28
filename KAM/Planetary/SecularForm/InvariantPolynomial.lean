/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.SecularForm.InvariantPolynomial.TwoVectors

/-!
# Secular form: `O(2)`-invariant polynomials

Facade for package S8-W.  `e_weyl` (`bpP:p8:e-weyl`, `InvariantPolynomial/Weyl`) is the first
fundamental theorem for `O(2)` acting on `n` planar vectors; `InvariantPolynomial/TwoVectors`
derives the quadratic (three) and quartic (six) invariant reductions used by `quadratic_form` and
`quartic`.
-/
