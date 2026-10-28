/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.LocalAnalytic.Unique

/-!
# Secular spectrum: local analytic spectral decomposition

Blueprint P, Part 9 (`bpP:p9:local-analytic`): `local_analytic` gives, near a point of simple
spectrum of an analytic real symmetric family, analytic strictly increasing eigenvalues and an
analytic `SO(n)` eigenframe; `local_analytic_unique` shows the eigenvalues are unique on a
connected open set and the frame is unique up to a constant diagonal sign matrix of determinant
one.  The proof cuts are in `LocalAnalytic.Eigenvalues` (`stepP:p9:la-ev`),
`LocalAnalytic.Projection`/`LocalAnalytic.Analytic` (`stepP:p9:la-adj`), `LocalAnalytic.Frame`
(`stepP:p9:la-vec`), `LocalAnalytic.Existence` and `LocalAnalytic.Unique` (`stepP:p9:la-so`).
-/

@[expose] public noncomputable section

end
