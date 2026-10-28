/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.OrbitJet.Jet

/-!
# Planar quartic torsion: the jet algebra of the unit-axis orbit

The exact polynomial identities behind `orbit`, on `Jet5` (truncated polynomials in the scale `t` of
the eccentricity vector `v = t w`, with `ζ = w₀ + i w₁`, `ζ̄ = w₀ - i w₁`, `X = e^{iλ}` and
`Xi`):

* `kepJet_aJet`: the degree-four solution `aJet` of the Kepler fixed-point equation
  `y = t (A e^y - B e^{-y}) / 2` is a fixed point of the jet map;
* `oJet_eq_refJet`: the assembled jet of the orbit `k e^{iF} - z + (d / (1 + k)) z` is the displayed
  jet `p11c_orbitJet` of the design.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.OrbitJet

open Jet5

/-- The degree-four jet of the solution of `y = t (A e^y - B e^{-y}) / 2`. -/
def aJet (A B : ℂ) : Jet5 :=
  ⟨0, (A - B) / 2, (A - B) * (A + B) / 4, (A - B) * (3 * A ^ 2 + 2 * A * B + 3 * B ^ 2) / 16,
    (A - B) * (A + B) * (2 * A ^ 2 - A * B + 2 * B ^ 2) / 12⟩

/-- The jet of the right-hand side `t (A e^y - B e^{-y}) / 2` for a given jet of `y`. -/
def kepJet (A B : ℂ) (a : Jet5) : Jet5 :=
  smul (1 / 2) (mul var (add (smul A (exp a)) (neg (smul B (exp (neg a))))))

theorem kepJet_aJet (A B : ℂ) : kepJet A B (aJet A B) = aJet A B := by
  ext <;> simp [kepJet, aJet, Jet5.exp, Jet5.smul, Jet5.mul, Jet5.add, Jet5.neg, Jet5.var,
    Jet5.const] <;> ring

/-- The jet of `sqrt (1 - t² c)`. -/
def kJet (c : ℂ) : Jet5 := ⟨1, 0, -c / 2, 0, -c ^ 2 / 8⟩

/-- The jet of `1 / (1 + sqrt (1 - t² c))`. -/
def wJet (c : ℂ) : Jet5 := ⟨1 / 2, 0, c / 8, 0, c ^ 2 / 16⟩

/-- The jet of the orbit, assembled from the jets of its factors. -/
def oJet (ζ ζb X Xi : ℂ) : Jet5 :=
  add (add (mul (kJet (ζ * ζb)) (smul X (exp (aJet (ζb * X) (ζ * Xi)))))
      (neg (smul ζ var)))
    (mul (mul (smul (1 / 2) (mul var (add (smul (ζb * X) (exp (aJet (ζb * X) (ζ * Xi))))
      (smul (ζ * Xi) (exp (neg (aJet (ζb * X) (ζ * Xi))))))))
      (wJet (ζ * ζb))) (smul ζ var))

/-- The displayed jet of the design, at `v = t w`. -/
def refJet (ζ ζb X Xi : ℂ) : Jet5 :=
  ⟨X, X ^ 2 * ζb / 2 - 3 * ζ / 2, 3 * X ^ 3 * ζb ^ 2 / 8 - X * ζ * ζb / 2 + Xi * ζ ^ 2 / 8,
    X ^ 4 * ζb ^ 3 / 3 - 3 * X ^ 2 * ζ * ζb ^ 2 / 8 + Xi ^ 2 * ζ ^ 3 / 24,
    125 * X ^ 5 * ζb ^ 4 / 384 - 3 * X ^ 3 * ζ * ζb ^ 3 / 8 - X * ζ ^ 2 * ζb ^ 2 / 64 +
      Xi * ζ ^ 3 * ζb / 24 + 3 * Xi ^ 3 * ζ ^ 4 / 128⟩

theorem oJet_eq_refJet (ζ ζb X Xi : ℂ) (h : X * Xi = 1) :
    oJet ζ ζb X Xi = refJet ζ ζb X Xi := by
  ext <;> simp [oJet, refJet, kJet, wJet, aJet, Jet5.exp, Jet5.smul, Jet5.mul, Jet5.add,
    Jet5.neg, Jet5.var, Jet5.const]
  · linear_combination (-ζ / 2) * h
  · linear_combination (-ζ / 8 * (2 * X * ζb + Xi * ζ)) * h
  · linear_combination (-ζ * (3 * X ^ 2 * ζb ^ 2 + Xi ^ 2 * ζ ^ 2) / 12) * h
  · linear_combination (-ζ * (108 * X ^ 3 * ζb ^ 3 - 6 * X ^ 2 * Xi * ζb ^ 2 * ζ -
      4 * X * Xi ^ 2 * ζb * ζ ^ 2 - 18 * X * ζb ^ 2 * ζ + 27 * Xi ^ 3 * ζ ^ 3 +
      8 * Xi * ζb * ζ ^ 2) / 384) * h

end KAM.Planetary.OrbitJet

end
