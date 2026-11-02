/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Chart.Symplectic

/-!
# The regular spatial Poincare chart is a local analytic diffeomorphism

Source: `LP:MAIN L17 (571–578)`, track LP, non-frozen. Items 3–5: a symplectic
map has an injective, hence (finite dimension) invertible, derivative. With analyticity this
gives, at every point of (44), an open partial homeomorphism extending `spatialPoincare ν` whose
inverse is analytic, as for the planar chart (`poincare_localDiffeo`).

-/

@[expose] public noncomputable section

open Matrix
open scoped ContDiff

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

variable {ν : ℝ} {w : Phase 3}

end KAM.Planetary.Spatial
