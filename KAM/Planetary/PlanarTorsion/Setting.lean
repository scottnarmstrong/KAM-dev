/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Frozen.Planetary.Defs.SecularAverage

/-!
# Planar quartic torsion: the setting

Blueprint P, Part 11b (`bpP:p11b:sec-set#data`): the physical data `PlanarData` of the planar
three-body problem, the action/axis dictionary, the two physical perturbations pulled back by the
Poincaré product chart (`p11c_hatFix`, `p11c_hatMov`), their secular averages in the frozen
`(φ, q; I, p)` coordinates, and the slow-length and quartic adapters on `Phase 2`.  The generic
homogeneous-part helper `p11c_homogeneousPart` is placed here (design audit N2).
-/

@[expose] public noncomputable section

open Set Metric Real Function

namespace KAM.Planetary

open KAM KAM.Kepler

/-- Physical data of the planar problem: gravitational constant, central mass, planet masses. -/
structure PlanarData where
  G : ℝ
  m0 : ℝ
  m : Fin 2 → ℝ

def PlanarData.Valid (p : PlanarData) : Prop := 0 < p.G ∧ 0 < p.m0 ∧ ∀ i, 0 < p.m i
def PlanarData.kappa (p : PlanarData) : ℝ := p.G * p.m0
def p11c_axes : Set (Fin 2 → ℝ) := {a | 0 < a 0 ∧ a 0 < a 1}
def PlanarData.actions (p : PlanarData) (a : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => p.m i * sqrt (p.kappa * a i)
def PlanarData.axes (p : PlanarData) (I : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => I i ^ 2 / (p.m i ^ 2 * p.kappa)

def p11c_hatFix (p : PlanarData) : Phase (2 + 2) → ℝ := fFix p.G p.m ∘ poincareProd p.m p.kappa
def p11c_hatMov (p : PlanarData) : Phase (2 + 2) → ℝ :=
  fMov p.G p.m0 p.m ∘ poincareProd p.m p.kappa

def p11c_secular (P : Phase (2 + 2) → ℝ) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  secularAverage (fun _ => P) 0 I z.2 z.1

def p11c_slowLength (z : Phase 2) : ℝ := sqrt (∑ i, (z.1 i ^ 2 + z.2 i ^ 2))
def p11c_pairDot (z : Phase 2) : ℝ := z.1 0 * z.1 1 + z.2 0 * z.2 1
def p11c_quartic (c : Fin 6 → ℝ) (z : Phase 2) : ℝ :=
  let A := z.1 0 ^ 2 + z.2 0 ^ 2
  let B := z.1 1 ^ 2 + z.2 1 ^ 2
  let D := p11c_pairDot z
  c 0 * A ^ 2 + c 1 * B ^ 2 + c 2 * A * B + c 3 * D ^ 2 + c 4 * A * D + c 5 * B * D

def p11c_homogeneousPart (j : ℕ) (f : Phase 2 → ℝ) (z : Phase 2) : ℝ :=
  iteratedFDeriv ℝ j f 0 (fun _ => z) / (j.factorial : ℝ)

end KAM.Planetary
