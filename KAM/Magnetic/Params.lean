/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs
public import KAM.Certificate.Arith.Fixed

/-!
# Magnetic barrier: backend and certificate parameters

`MagBackend = CertFixed 128` and the package `magParams err disp` of the `ε = 3/2500` magnetic torus
(plan-magnetic-barrier §3.3: `s₀ = 500001/500000`, `γ = (1/10)/s₀`, `τ = 1`, `ρ = 3/1000`,
`ρ∞ = ρ/1000`, `μ = 1/500`, `σω = 2`, `νRay = 10⁻⁶`; the majorants `M`, `σK`, `σB`, `σT` are the
values the sofx mirror passes with margin, `scripts/magnetic/sofx_mag.py` `PKG`).
-/

@[expose] public section

namespace KAM.Magnetic

open KAM KAM.Certificate

/-- The fixed-point precision of the magnetic certificate. -/
def magPrecision : ℕ := 128

/-- The backend `CertFixed 128`. -/
abbrev MagBackend : Type := CertFixed magPrecision

/-- The ray scalar `s₀ = 1 + 2·10⁻⁶`. -/
def magScalar : ℚ := 500001 / 500000

/-- `κ = 1/s₀`: `ω* = (α, 1)/s₀`. -/
def magKappa : ℚ := 1 / magScalar

/-- The parameters for a residual budget `err` and a displacement bound `disp`. -/
def magParams (err disp : ℚ) : CertParams where
  tau := 1
  rho := 3 / 1000
  rhoInf := 3 / 1000000
  M := 85
  σK := 9 / 5
  σB := 27 / 10
  σT := 11 / 5
  μ := 1 / 500
  γbar := magKappa / 10
  σω := 2
  nuRay := 1 / 10 ^ 6
  γ := magKappa / 10
  s := magScalar
  err := err
  E0 := 0
  disp := disp

/-- The `ℚ(√5)` coefficients of `ω* = ((7913 - √5)/13618, 1)/s₀` (for `checkAlgBox`). -/
def magCoeffs : List (List ℚ) :=
  [[7913 * magKappa / 13618, -magKappa / 13618], [magKappa]]

end KAM.Magnetic

end
