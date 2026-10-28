/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.PlanarTorsion.PairCoefficients
public import KAM.Planetary.PlanarTorsion.Setting

/-!
# Planar quartic torsion: the actual pair average and its jet (definitions)

Blueprint P, Part 11b (`bpP:p11b:pair-jet`): `p11c_pairAverage` is the double radian mean of the
inverse distance of the two planets (the first one scaled by `a = a₁/a₂`), and `p11c_pairJet` the
displayed degree-four jet, copied verbatim from the signature file of the P11C design.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary

def p11c_pairAverage (a : ℝ) (z : Phase 2) : ℝ :=
  (2 * π) ^ (-2 : ℤ) * ∫ l : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)),
    ‖(a : ℂ) * p11c_orbit (l 0) ![z.1 0, z.2 0] - p11c_orbit (l 1) ![z.1 1, z.2 1]‖⁻¹

def p11c_pairJet (a : ℝ) (z : Phase 2) : ℝ :=
  p11c_laplace (1 / 2) 0 a + p11c_pairCoeffs a 0 * (p11c_slowLength z) ^ 2 +
    p11c_pairCoeffs a 1 * p11c_pairDot z + p11c_quartic (fun i => p11c_pairCoeffs a (i.castAdd 2 + 2)) z

end KAM.Planetary

end
