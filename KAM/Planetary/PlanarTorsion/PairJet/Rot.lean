/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Jet
public import KAM.Planetary.PlanarTorsion.PairJet.Terms

/-!
# Planar quartic torsion: the rotated jet of the pair integrand

Blueprint P, Part 11b (`stepP:p11b:pj-bin`): in the variables `η = ζ e^{-iλ}`, `η̄ = ζ̄ e^{iλ}` the
    jet of
the unit-axis orbit has constant rational coefficients, so the jet of `|α z₁ - z₂|²` is a
    polynomial in
`η₁, η̄₁, η₂, η̄₂` and `r = e^{i(λ₁-λ₂)}`.  Its coefficients `N_m` and the pieces of the binomial
expansion of `N^{-1/2}` are defined here.
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM.Planetary.OrbitJet

/-- The rotated Taylor coefficient `j₁`. -/
def p11cPJj1 (e eb : ℂ) : ℂ := eb / 2 - 3 * e / 2

/-- The rotated Taylor coefficient `j₂`. -/
def p11cPJj2 (e eb : ℂ) : ℂ := 3 * eb ^ 2 / 8 - e * eb / 2 + e ^ 2 / 8

/-- The rotated Taylor coefficient `j₃`. -/
def p11cPJj3 (e eb : ℂ) : ℂ := eb ^ 3 / 3 - 3 * e * eb ^ 2 / 8 + e ^ 3 / 24

/-- The rotated Taylor coefficient `j₄`. -/
def p11cPJj4 (e eb : ℂ) : ℂ :=
  125 * eb ^ 4 / 384 - 3 * e * eb ^ 3 / 8 - e ^ 2 * eb ^ 2 / 64 + e ^ 3 * eb / 24 +
    3 * e ^ 4 / 128

/-- The jet of the unit-axis orbit divided by `e^{iλ}`, in the rotated variables
`η = ζ e^{-iλ}`, `η̄ = ζ̄ e^{iλ}`. -/
def p11cPJv (e eb : ℂ) : Jet5 := ⟨1, p11cPJj1 e eb, p11cPJj2 e eb, p11cPJj3 e eb, p11cPJj4 e eb⟩

/-- The jet of `|α z₁ - z₂|² / |e^{iλ₂}|²` in the rotated variables, with `r = e^{i(λ₁-λ₂)}`,
`rb = e^{-i(λ₁-λ₂)}`. -/
def p11cPJN (α e1 eb1 e2 eb2 r rb : ℂ) : Jet5 :=
  Jet5.add
    (Jet5.add (Jet5.smul (α ^ 2) (Jet5.mul (p11cPJv e1 eb1) (p11cPJv eb1 e1)))
      (Jet5.mul (p11cPJv e2 eb2) (p11cPJv eb2 e2)))
    (Jet5.neg (Jet5.smul α
      (Jet5.add (Jet5.smul r (Jet5.mul (p11cPJv e1 eb1) (p11cPJv eb2 e2)))
        (Jet5.smul rb (Jet5.mul (p11cPJv eb1 e1) (p11cPJv e2 eb2))))))

/-- A piece of the jet of the integrand. -/
def p11cPJq22a (α e1 eb1 e2 eb2 r rb S : ℂ) : ℂ :=
  S ^ 3 * (p11cPJN α e1 eb1 e2 eb2 r rb).a2

/-- A piece of the jet of the integrand. -/
def p11cPJq22b (α e1 eb1 e2 eb2 r rb S : ℂ) : ℂ :=
  S ^ 5 * (p11cPJN α e1 eb1 e2 eb2 r rb).a1 ^ 2

/-- A piece of the jet of the integrand. -/
def p11cPJq44a (α e1 eb1 e2 eb2 r rb S : ℂ) : ℂ :=
  S ^ 3 * (p11cPJN α e1 eb1 e2 eb2 r rb).a4

/-- A piece of the jet of the integrand. -/
def p11cPJq413 (α e1 eb1 e2 eb2 r rb S : ℂ) : ℂ :=
  S ^ 5 * ((p11cPJN α e1 eb1 e2 eb2 r rb).a1 * (p11cPJN α e1 eb1 e2 eb2 r rb).a3)

/-- A piece of the jet of the integrand. -/
def p11cPJq422 (α e1 eb1 e2 eb2 r rb S : ℂ) : ℂ :=
  S ^ 5 * (p11cPJN α e1 eb1 e2 eb2 r rb).a2 ^ 2

/-- A piece of the jet of the integrand. -/
def p11cPJq4112 (α e1 eb1 e2 eb2 r rb S : ℂ) : ℂ :=
  S ^ 7 * ((p11cPJN α e1 eb1 e2 eb2 r rb).a1 ^ 2 * (p11cPJN α e1 eb1 e2 eb2 r rb).a2)

/-- A piece of the jet of the integrand. -/
def p11cPJq4114 (α e1 eb1 e2 eb2 r rb S : ℂ) : ℂ :=
  S ^ 9 * (p11cPJN α e1 eb1 e2 eb2 r rb).a1 ^ 4


end KAM.Planetary

end
