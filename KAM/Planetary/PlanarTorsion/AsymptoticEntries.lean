/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Inputs
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Projector
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Coeffs
public import KAM.Planetary.PlanarTorsion.AsymptoticEntries.Entries

/-!
# Planar quartic torsion: asymptotic entries (P11C, package T18)

Blueprint P, Part 11b (`bpP:p11b:asymptotics`, local steps `as-in`, `as-pi`, `as-c`, `as-ent`),
at the hierarchical axes `a = ![α, 1]` as `α → 0⁺`:

* `as_in` (`AsymptoticEntries/Inputs`): the entries of `p11c_Q` and `Δ_Q = Q₁₁ - Q₂₂ < 0`;
* `as_pi` (`AsymptoticEntries/Projector`): the projector entries `π₁₂ = O(α ^ (5/4))`,
  `0 ≤ π₂₂ = O(α ^ (5/2))`, `π₁₁ = 1 - π₂₂`;
* `as_c` (`AsymptoticEntries/Coeffs`): the sizes of the six quartic coefficients;
* `as_ent` (`AsymptoticEntries/Entries`): the entries of `p11c_beta` and their three limits.

This file is the facade of the package; `Pair`, `Calculus`, `Leading`, `CoeffEq` and
`EntryBounds` hold the supporting big-O bookkeeping.  The relative errors are kept in the absolute
form `leading + O(α ^ (leading exponent + 2))`; the determinant (`as-det`) and homogeneity belong
to package T19.
-/

@[expose] public section
end
