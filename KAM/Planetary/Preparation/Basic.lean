/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Projections
public import KAM.Weighted.Parametric
public import KAM.Planetary.WeakMeasure.Basic
public import KAM.Planetary.Poincare.Product
public import KAM.Frozen.Planetary.Defs.CircularTube
public import KAM.Frozen.Planetary.Defs.SecularAverage
public import KAM.Frozen.Planetary.Defs.IsPhysicalTorus

/-!
# Preparation conventions (P11A-P1, `bpP:p11:sec-conv#data`)

The conventions node of the finite preparation introduces no new definition: it is carried by the
existing `Weighted` domains and norms, the frozen `Phase`, `complexStrip`, `actionNbhd`,
`IsDiophantine`, `IsPhysicalTorus`, `circularTube` and `secularAverage`, and by the weak-measure
carriers `P11Vec`, `P11CVec`, `P11Phase`, `P11Family` of `WeakMeasure.Basic`. This module is the
import facade for the preparation modules (`Working`, `BasePoint`); no alias is introduced.
-/

@[expose] public noncomputable section

end
