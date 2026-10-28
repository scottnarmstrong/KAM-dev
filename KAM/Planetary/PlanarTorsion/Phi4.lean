/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.SpectralAdapter

/-!
# Planar quartic torsion: the nonresonance polynomial `p11c_phi4`

Blueprint P, Part 11b (`bpP:p11b:torsion`, `bpP:p11b:birkhoff-form`): the signed adapter
`p11c_phi4`, the finite product over all modes `0 < |k|₁ ≤ 4` of the mode frequency
`k · σ`.  It is a leaf module so that `Generic` (T20) can state `torsion` without importing the
Birkhoff modules.
-/

@[expose] public noncomputable section

open Set Metric Real
namespace KAM.Planetary
open KAM KAM.Kepler

/-- Simultaneous nonresonance polynomial; Part 9's Phi4 adapter, all modes 0<|k|1<=4. -/
def p11c_phi4 (p : PlanarData) (a : Fin 2 → ℝ) : ℝ :=
  ∏ k ∈ (Finset.univ : Finset (Fin 2 → Fin 9)).filter
    (fun k => 0 < (∑ i, |((k i).val : ℤ) - 4|) ∧ (∑ i, |((k i).val : ℤ) - 4|) ≤ 4),
    ∑ i, (((k i).val : ℝ) - 4) * p11c_sigma p a i

end KAM.Planetary

end
