/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Characters.Defs
public import KAM.Planetary.PlanarTorsion.Characters.Basic
public import KAM.Planetary.PlanarTorsion.Characters.CharPoly
public import KAM.Planetary.PlanarTorsion.Characters.Average
public import KAM.Planetary.PlanarTorsion.Characters.Bracket

/-!
# Planar quartic torsion: characters (facade)

Blueprint P, Part 11b (`bpP:p11b:sec-bnf#data`, `bpP:p11b:char`).  Definitions in `Characters/Defs`
(`QuarticFamily`, `p11c_rotation`, `p11c_character`, `p11c_average`, `p11c_NR4`, `p11c_n0`,
`p11c_bracket`); `char` in `Characters/Basic`; `character_polynomial` in `Characters/CharPoly`;
`average_action_polynomial` in `Characters/Average`; `character_bracket` in `Characters/Bracket`.
The one-plane trigonometric machinery is in `Characters/Trig`, `Characters/Factor`,
    `Characters/Poly`.
-/
