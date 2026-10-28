/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.AMDBox
public import KAM.Frozen.Planetary.Defs.BodyVector
public import KAM.Frozen.Planetary.Defs.KeplerAction
public import KAM.Frozen.Planetary.Defs.LowAMDRegion
public import KAM.Frozen.Planetary.Defs.PhysicalAMD
public import KAM.Frozen.Planetary.Defs.PlaneLength

/-!
# AMD confinement: region definitions

Blueprint `bpP:p14:conv#data`: the outer and inner low-AMD regions (literal wrappers around the frozen
`LowAMDRegion`), the collar region, and the compact geometric region of an `AMDBox`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

variable {n : ℕ}

def amdOuter (B : AMDBox n) := LowAMDRegion B.mass B.lower B.upper B.outerAMD
def amdInner (B : AMDBox n) := LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD
def amdCollar (B : AMDBox n) (delta : ℝ) : Set (Phase (n * 2)) :=
  {z ∈ amdOuter B | (∀ i, B.lower i + delta ≤ keplerAction B.mass z i ∧
    keplerAction B.mass z i ≤ B.upper i - delta) ∧
    physicalAMD B.mass z ≤ B.initialAMD + (n : ℝ) * delta}
def amdCompact (B : AMDBox n) : Set (Phase (n * 2)) :=
  {z | (∀ i, B.distance ≤ planeLength (bodyVector z.1 i) ∧
    planeLength (bodyVector z.1 i) ≤ B.radius ∧
    planeLength (bodyVector z.2 i) ≤ B.mass i * Real.sqrt (2 / B.distance)) ∧
    ∀ i j, i ≠ j → B.distance ≤ planeLength (bodyVector z.1 i - bodyVector z.1 j)}

end KAM.Planetary

end
