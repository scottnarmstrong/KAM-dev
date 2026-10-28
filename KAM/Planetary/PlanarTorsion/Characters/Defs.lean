/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Setting
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Planetary.Defs.OscillatorAction

/-!
# Planar quartic torsion: quartic families, rotations and characters (definitions)

Blueprint P, Part 11b (`bpP:p11b:sec-bnf#data`, `bpP:p11b:char`): the finite quartic families
`QuarticFamily`, the rotation action `p11c_rotation`, the character `p11c_character` and the
average `p11c_average`, the non-resonance predicate `p11c_NR4`, the oscillator part `p11c_n0` and
the bracket `p11c_bracket`.  The declarations are copied verbatim from the signature file.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler

def p11c_monomial (a : Fin 4 → ℕ) (z : Phase 2) : ℝ :=
  z.1 0 ^ a 0 * z.2 0 ^ a 1 * z.1 1 ^ a 2 * z.2 1 ^ a 3

structure QuarticFamily (O : Set (Fin 2 → ℝ)) where
  coeff : (Fin 4 → ℕ) → (Fin 2 → ℝ) → ℝ
  analytic : ∀ a, AnalyticOnNhd ℝ (coeff a) O

def QuarticFamily.eval {O : Set (Fin 2 → ℝ)} (F : QuarticFamily O) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  ∑ a ∈ (Finset.univ : Finset (Fin 4 → Fin 5)).filter (fun a => ∑ i, (a i).val = 4),
    F.coeff (fun i => (a i).val) I * p11c_monomial (fun i => (a i).val) z

def p11c_rotation (theta : Fin 2 → ℝ) (z : Phase 2) : Phase 2 :=
  (fun j => cos (theta j) * z.1 j + sin (theta j) * z.2 j,
   fun j => -sin (theta j) * z.1 j + cos (theta j) * z.2 j)
def p11c_character (F : (Fin 2 → ℝ) → Phase 2 → ℝ) (k : Fin 2 → ℤ) (I : Fin 2 → ℝ) (z : Phase 2) : ℂ :=
  (2 * π : ℂ) ^ (-2 : ℤ) * ∫ theta : Fin 2 → ℝ in Set.pi univ (fun _ => Icc (0 : ℝ) (2 * π)),
    Complex.exp (-Complex.I * (∑ j, (k j : ℂ) * theta j)) * (F I (p11c_rotation theta z) : ℂ)
def p11c_average (F : (Fin 2 → ℝ) → Phase 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  (p11c_character F 0 I z).re

def p11c_NR4 (O : Set (Fin 2 → ℝ)) (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ I ∈ O, ∀ k : Fin 2 → ℤ, k ≠ 0 → (∑ i, |(k i : ℝ)|) ≤ 4 → ∑ i, (k i : ℝ) * freq I i ≠ 0

def p11c_n0 (freq : (Fin 2 → ℝ) → Fin 2 → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  ∑ j, freq I j * oscillatorAction z.2 z.1 j

def p11c_bracket (F G : Phase 2 → ℝ) (z : Phase 2) : ℝ :=
  fderiv ℝ F z (hamiltonianVectorField G z)

end KAM.Planetary

end
