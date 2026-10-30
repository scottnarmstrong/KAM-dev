/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs

/-!
# The lunar parameters R1

In the rotated frame `q - φ`: `ρ' = 1/70`, `ρ∞ = ρ'/1000`, `μ = 1/160`, ray
scalar `s = 1 + 10⁻⁶`, `ν = 10⁻⁶`, `σω = 2`, time scale `c = 237/125`, one majorant
`σK = σB = σT = 1987/1000` (measured on the lunar certificates; binding `σB`, the weighted-ℓ¹
Gram inverse bound 1.97994), `M = 203/100` (above the `checkHamBounds` D²H sum, 2.0205 on both
tori), `γ = γ̄ = c/(42 s)`, `τ = 1`, `E₀ = 0`. The residual budget `err` and the displacement
`disp` of each torus are parameters (filled by the certificate data).
-/

@[expose] public section

namespace KAM.SpinOrbit

open KAM.Certificate

def lunarR1TimeScale : ℚ := 237 / 125

def lunarR1Scalar : ℚ := 1 + 1 / 10 ^ 6

/-- `κ = c/s`: the reference vectors are `lunarRotFreq ν± κ`. -/
def lunarR1Kappa : ℚ := lunarR1TimeScale / lunarR1Scalar

/-- The R1 parameters for a residual budget `err` and a displacement bound `disp`. -/
def lunarR1 (err disp : ℚ) : CertParams where
  tau := 1
  rho := 1 / 70
  rhoInf := 1 / 70000
  -- `M` must exceed the D²H sum of `checkHamBounds`, 2.0205 on both R1 tori.
  M := 203 / 100
  σK := 1987 / 1000
  σB := 1987 / 1000
  σT := 1987 / 1000
  μ := 1 / 160
  γbar := lunarR1Kappa / 42
  σω := 2
  nuRay := 1 / 10 ^ 6
  γ := lunarR1Kappa / 42
  s := lunarR1Scalar
  err := err
  E0 := 0
  disp := disp

theorem lunarR1Kappa_div : lunarR1Kappa / 42 = 316000 / 7000007 := by
  decide +kernel

/-! ### Kernel pre-checks (helpers; the certificates themselves are separate data) -/

/-- The parameter-only conjuncts of `checkStatic` except `0 ≤ err` (shapes, weights, the `π`
enclosure and the box are certificate data). -/
def lunarR1StaticCore (p : CertParams) : Bool :=
  decide (2 ≤ p.tau + 1) && decide (0 < p.rhoInf) && decide (p.rhoInf < p.rho) &&
    decide (0 < p.M) && decide (0 < p.σK) && decide (0 < p.σB) && decide (0 < p.σT) &&
    decide (0 < p.μ) && decide (0 < p.γbar) && decide (1 < p.σω) && decide (0 < p.nuRay) &&
    decide (1 < p.s) && decide (p.s < p.σω) && decide (0 < p.γ) && decide (p.γ ≤ p.γbar)

theorem lunarR1_staticCore_zero : lunarR1StaticCore (lunarR1 0 0) = true := by
  decide +kernel

/-- The parameter part of `checkStatic` holds for `lunarR1 err disp` at every `0 ≤ err`. -/
theorem lunarR1_staticCore (err disp : ℚ) :
    lunarR1StaticCore (lunarR1 err disp) = true :=
  lunarR1_staticCore_zero

theorem lunarR1_err_nonneg {err : ℚ} (disp : ℚ) (h : 0 ≤ err) :
    decide (0 ≤ (lunarR1 err disp).err) = true :=
  decide_eq_true h

/-- At the measured residual budgets (`4.03e-78`, `7.84e-78`; literal rationals just above). -/
theorem lunarR1_staticCore_gen2 :
    (lunarR1StaticCore (lunarR1 (41 / 10 ^ 79) 0) &&
      decide (0 ≤ (lunarR1 (41 / 10 ^ 79) 0).err)) = true ∧
    (lunarR1StaticCore (lunarR1 (79 / 10 ^ 79) 0) &&
      decide (0 ≤ (lunarR1 (79 / 10 ^ 79) 0).err)) = true := by
  decide +kernel

/-- The `C₁` smallness inequality of `checkSmallness` for R1 at `err = 9 · 10⁻⁷⁶` (the R1
threshold is about `9.772 · 10⁻⁷⁶ = 10^{-75.010}`). -/
theorem lunarR1_smallness_C1 :
    let p := lunarR1 (9 / 10 ^ 76) 0
    decide (isoC1Q 2 p.tau p.rho p.rhoInf p.M p.σK p.σB p.σT p.μ p.nuRay p.γbar * p.err <
      p.γ ^ 4 * p.rho ^ (4 * p.tau)) = true := by
  decide +kernel

/-- The threshold is sharp to a factor `1.03`: the inequality fails at `err = 10⁻⁷⁵`. -/
theorem lunarR1_smallness_C1_fails :
    let p := lunarR1 (1 / 10 ^ 75) 0
    decide (isoC1Q 2 p.tau p.rho p.rhoInf p.M p.σK p.σB p.σT p.μ p.nuRay p.γbar * p.err <
      p.γ ^ 4 * p.rho ^ (4 * p.tau)) = false := by
  decide +kernel

/-- The `C₂` displacement inequality at `err = 9 · 10⁻⁷⁶` with `disp = 10⁻³⁹`
(`isoC2Q / (γ² ρ²) ≈ 1.709 · 10³⁵ = 10^{35.233}`). -/
theorem lunarR1_smallness_C2 :
    let p := lunarR1 (9 / 10 ^ 76) (1 / 10 ^ 39)
    decide (isoC2Q 2 p.tau p.rho p.rhoInf p.M p.σK p.σB p.σT * p.err ≤
      p.disp * (p.γ ^ 2 * p.rho ^ (2 * p.tau))) = true := by
  decide +kernel

/-- A rational box around `lunarRotFreq ν κ` with `ν = (a + b √5)/3118`, `√5 ∈ [2236067,
2236069]/10⁶`: coordinate `0` is `κ (ν - 1)`, coordinate `1` is `κ` exactly. -/
def lunarR1Box (a b : ℚ) : FreqBox :=
  [(lunarR1Kappa * ((a + b * 2236068 / 10 ^ 6) / 3118 - 1), lunarR1Kappa * |b| / 3118 / 10 ^ 6),
    (lunarR1Kappa, 0)]

/-- The ray margins `ν ≤ (s - 1) L`, `ν ≤ (σω - s) L` with `L = freqNormLo` of the boxes around
`lunarRotFreq ν± κ` (`ν₋ = (3039 + √5)/3118`, `ν₊ = (3197 - √5)/3118`); here `L = κ ≈ 1.896`. -/
theorem lunarR1_rayMargins :
    let p := lunarR1 0 0
    (decide (0 < freqNormLo (lunarR1Box 3039 1)) &&
      decide (p.nuRay ≤ (p.s - 1) * freqNormLo (lunarR1Box 3039 1)) &&
      decide (p.nuRay ≤ (p.σω - p.s) * freqNormLo (lunarR1Box 3039 1)) &&
      decide (0 < freqNormLo (lunarR1Box 3197 (-1))) &&
      decide (p.nuRay ≤ (p.s - 1) * freqNormLo (lunarR1Box 3197 (-1))) &&
      decide (p.nuRay ≤ (p.σω - p.s) * freqNormLo (lunarR1Box 3197 (-1)))) = true := by
  decide +kernel

theorem lunarR1Box_normLo (a b : ℚ) (h : |lunarR1Kappa * ((a + b * 2236068 / 10 ^ 6) / 3118 - 1)| -
    lunarR1Kappa * |b| / 3118 / 10 ^ 6 ≤ lunarR1Kappa) :
    freqNormLo (lunarR1Box a b) = lunarR1Kappa := by
  simp only [freqNormLo, lunarR1Box, List.foldr_cons, List.foldr_nil, sub_zero]
  rw [max_eq_left (by decide +kernel : (0 : ℚ) ≤ |lunarR1Kappa|),
    abs_of_pos (by decide +kernel : (0 : ℚ) < lunarR1Kappa)]
  exact max_eq_right h

end KAM.SpinOrbit
