/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.LunarParams
public import KAM.SpinOrbit.RotFreqN
public import KAM.CertificateSharp.Sharp

/-!
# The lunar parameters R2 (barrier index `N = 65`, sharp certifier)

SO-GEN3's package R2, in the rotated frame `q - φ`: time scale `c = 2`, ray scalar
`s = 1 + 10⁻⁶`, `κ = c/s`, `ρ = 1/140`, `ρ∞ = ρ/1000`, `M = 54/25` (above the `checkHamBounds`
D²H sum 2.1191), `σK = 1873/1000` (DK rows 1.86485 plus `μ`), `σB = 2689/500` (the `checkGram`
ℓ¹ bound 5.36057), `σT = 13/25` (`checkTorsion` ‖S‖ = 0.50406), `μ = 1/160`, `ν = 10⁻⁶`,
`σω = 2`, `γ = γ̄ = κ/67` (the `N = 65` Diophantine constant `κ/(N + 2)`), `τ = 1`, `E₀ = 0`.
The residual budget `err` and the displacement `disp` are parameters (filled by the data).

Kernel pre-checks: the parameter core of `checkStatic`; both inequalities of `sharpTest` just
above SO-GEN3's budgets; the threshold `≈ 1.4883 · 10⁻³² = 10^{-31.827}` (pass at `1.48 · 10⁻³²`,
fail at `1.49 · 10⁻³²`); the ray margins for the `N = 65` boxes; `γ ≤ κ/67`.
-/

@[expose] public section

namespace KAM.SpinOrbit

open KAM KAM.Certificate KAM.CertificateSharp

def lunarR2TimeScale : ℚ := 2

def lunarR2Scalar : ℚ := 1 + 1 / 10 ^ 6

/-- `κ = c/s`: the reference vectors are `lunarRotFreq ν± κ`. -/
def lunarR2Kappa : ℚ := lunarR2TimeScale / lunarR2Scalar

/-- The R2 parameters for a residual budget `err` and a displacement bound `disp`. -/
def lunarR2 (err disp : ℚ) : CertParams where
  tau := 1
  rho := 1 / 140
  rhoInf := 1 / 140000
  -- `M` must exceed the D²H sum of `checkHamBounds`, 2.1191 on both R2 tori.
  M := 54 / 25
  σK := 1873 / 1000
  σB := 2689 / 500
  σT := 13 / 25
  μ := 1 / 160
  γbar := lunarR2Kappa / 67
  σω := 2
  nuRay := 1 / 10 ^ 6
  γ := lunarR2Kappa / 67
  s := lunarR2Scalar
  err := err
  E0 := 0
  disp := disp

theorem lunarR2Kappa_eq : lunarR2Kappa = 2000000 / 1000001 := by
  decide +kernel

theorem lunarR2Kappa_pos : 0 < lunarR2Kappa := by
  decide +kernel

theorem lunarR2TimeScale_pos : 0 < lunarR2TimeScale := by
  decide +kernel

/-- The SO-DION bound: `γ ≤ κ · (1/67)`, the form `lunar_barriers_of_sharp` consumes. -/
theorem lunarR2_gamma_le (err disp : ℚ) : (lunarR2 err disp).γ ≤ lunarR2Kappa * (1 / 67) :=
  le_of_eq (by simp only [lunarR2]; ring)

/-! ### Kernel pre-checks (helpers; the certificates themselves are separate data) -/

theorem lunarR2_staticCore_zero : lunarR1StaticCore (lunarR2 0 0) = true := by
  decide +kernel

/-- The parameter part of `checkStatic` (`lunarR1StaticCore`, which is parameter-generic) holds
for `lunarR2 err disp` at every `err`, `disp`. -/
theorem lunarR2_staticCore (err disp : ℚ) : lunarR1StaticCore (lunarR2 err disp) = true :=
  lunarR2_staticCore_zero

theorem lunarR2_err_nonneg {err : ℚ} (disp : ℚ) (h : 0 ≤ err) :
    decide (0 ≤ (lunarR2 err disp).err) = true :=
  decide_eq_true h

/-- The body of `sharpTest` at `n = 2` as a function of the parameters alone. -/
def lunarR2SharpCore (p : CertParams) : Bool :=
  decide (sharpIsoC1Q 2 p.tau (cRRQ 2 p.tau) p.M p.σK p.σB p.σT p.γbar p.μ p.nuRay p.rho p.rhoInf *
      p.err < p.γ ^ 4 * p.rho ^ (4 * p.tau)) &&
    decide (max (sharpIsoC2Q 2 p.tau (cRRQ 2 p.tau) p.M p.σK p.σB p.σT p.γbar p.rho p.rhoInf)
      (sharpIsoC3Q 2 p.tau (cRRQ 2 p.tau) p.M p.σK p.σB p.σT p.γbar p.rho p.rhoInf) * p.err ≤
        p.disp * (p.γ ^ 2 * p.rho ^ (2 * p.tau)))

/-- `sharpTest` of a certificate is `lunarR2SharpCore` of its parameters. -/
theorem sharpTest_eq_lunarR2SharpCore {α : Type} [CertArith α] (c : TorusCertificate 2 α) :
    sharpTest c = lunarR2SharpCore c.params :=
  rfl

/-- The sharp test passes for `lunarR2 err disp` whenever its core does. -/
theorem sharpTest_of_lunarR2SharpCore {α : Type} [CertArith α] {c : TorusCertificate 2 α}
    {err disp : ℚ} (hp : c.params = lunarR2 err disp)
    (h : lunarR2SharpCore (lunarR2 err disp) = true) : sharpTest c = true := by
  rw [sharpTest_eq_lunarR2SharpCore, hp]
  exact h

/-- Both `sharpTest` inequalities just above SO-GEN3's budgets: lower torus `err = 6.9 · 10⁻³⁵`
(budget `6.8e-35`), `disp = 2.7 · 10⁻¹⁹` (needed `2.643e-19`); upper torus `err = 8.2 · 10⁻³⁵`
(budget `8.17e-35`), `disp = 3.2 · 10⁻¹⁹` (needed `3.141e-19`). The disp coefficient is
`max (C₂♯, C₃♯)/(γ² ρ²) ≈ 3.830 · 10¹⁵ = 10^{15.583}`. -/
theorem lunarR2_sharpCore_budgets :
    lunarR2SharpCore (lunarR2 (69 / 10 ^ 36) (27 / 10 ^ 20)) = true ∧
      lunarR2SharpCore (lunarR2 (82 / 10 ^ 36) (32 / 10 ^ 20)) = true := by
  decide +kernel

/-- The `C₁♯` inequality of `sharpTest` for R2 at `err = 1.48 · 10⁻³²`, just below the R2
threshold `≈ 1.48831 · 10⁻³² = 10^{-31.827}`. -/
theorem lunarR2_sharp_C1 :
    let p := lunarR2 (148 / 10 ^ 34) 0
    decide (sharpIsoC1Q 2 p.tau (cRRQ 2 p.tau) p.M p.σK p.σB p.σT p.γbar p.μ p.nuRay p.rho
      p.rhoInf * p.err < p.γ ^ 4 * p.rho ^ (4 * p.tau)) = true := by
  decide +kernel

/-- Non-vacuity: the threshold is sharp to a factor `1.007`; the `C₁♯` inequality fails at
`err = 1.49 · 10⁻³²`. -/
theorem lunarR2_sharp_C1_fails :
    let p := lunarR2 (149 / 10 ^ 34) 0
    decide (sharpIsoC1Q 2 p.tau (cRRQ 2 p.tau) p.M p.σK p.σB p.σT p.γbar p.μ p.nuRay p.rho
      p.rhoInf * p.err < p.γ ^ 4 * p.rho ^ (4 * p.tau)) = false := by
  decide +kernel

/-! ### The `N = 65` frequency boxes -/

/-- The rational enclosure `√5 ∈ [2236067, 2236069]/10⁶`. -/
def lunarR2SqrtFiveLo : ℚ := 2236067 / 10 ^ 6

def lunarR2SqrtFiveHi : ℚ := 2236069 / 10 ^ 6

theorem lunarR2_sqrtFive_mem :
    ((lunarR2SqrtFiveLo : ℚ) : ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ ((lunarR2SqrtFiveHi : ℚ) : ℝ) := by
  constructor
  · rw [Real.le_sqrt (by norm_num [lunarR2SqrtFiveLo]) (by norm_num)]
    norm_num [lunarR2SqrtFiveLo]
  · rw [Real.sqrt_le_left (by norm_num [lunarR2SqrtFiveHi])]
    norm_num [lunarR2SqrtFiveHi]

/-- The `ℚ(√5)` coefficients of `lunarRotFreq (lunarNuMinusN 65) lunarR2Kappa`
(`lunarRotFreqMinusN_eq`). -/
def lunarR2MinusCoeffs : List (List ℚ) :=
  [[-(2 * ((65 : ℕ) : ℚ) - 1) * lunarR2Kappa / (2 * (((65 : ℕ) : ℚ) ^ 2 - ((65 : ℕ) : ℚ) - 1)),
      lunarR2Kappa / (2 * (((65 : ℕ) : ℚ) ^ 2 - ((65 : ℕ) : ℚ) - 1))], [lunarR2Kappa]]

/-- The `ℚ(√5)` coefficients of `lunarRotFreq (lunarNuPlusN 65) lunarR2Kappa`
(`lunarRotFreqPlusN_eq`). -/
def lunarR2PlusCoeffs : List (List ℚ) :=
  [[(2 * ((65 : ℕ) : ℚ) - 1) * lunarR2Kappa / (2 * (((65 : ℕ) : ℚ) ^ 2 - ((65 : ℕ) : ℚ) - 1)),
      -lunarR2Kappa / (2 * (((65 : ℕ) : ℚ) ^ 2 - ((65 : ℕ) : ℚ) - 1))], [lunarR2Kappa]]

/-- The box `(centre, radius)` of the interval evaluation of `coeffs` at `√5 ∈ [lo, hi]`. -/
def lunarR2Box (coeffs : List (List ℚ)) : FreqBox :=
  coeffs.map fun row =>
    ((algRowLo row lunarR2SqrtFiveLo lunarR2SqrtFiveHi +
        algRowHi row lunarR2SqrtFiveLo lunarR2SqrtFiveHi) / 2,
      (algRowHi row lunarR2SqrtFiveLo lunarR2SqrtFiveHi -
        algRowLo row lunarR2SqrtFiveLo lunarR2SqrtFiveHi) / 2)

theorem lunarR2_checkAlgBox :
    checkAlgBox 2 lunarR2MinusCoeffs lunarR2SqrtFiveLo lunarR2SqrtFiveHi
        (lunarR2Box lunarR2MinusCoeffs) = true ∧
      checkAlgBox 2 lunarR2PlusCoeffs lunarR2SqrtFiveLo lunarR2SqrtFiveHi
        (lunarR2Box lunarR2PlusCoeffs) = true := by
  decide +kernel

theorem lunarR2Box_minus_encloses :
    FreqEncloses 2 (lunarR2Box lunarR2MinusCoeffs)
      (lunarRotFreq (lunarNuMinusN 65) lunarR2Kappa) := by
  rw [lunarRotFreqMinusN_eq]
  exact algFreq_encloses lunarR2_sqrtFive_mem lunarR2_checkAlgBox.1

theorem lunarR2Box_plus_encloses :
    FreqEncloses 2 (lunarR2Box lunarR2PlusCoeffs)
      (lunarRotFreq (lunarNuPlusN 65) lunarR2Kappa) := by
  rw [lunarRotFreqPlusN_eq]
  exact algFreq_encloses lunarR2_sqrtFive_mem lunarR2_checkAlgBox.2

/-- The ray margins `ν ≤ (s - 1) L`, `ν ≤ (σω - s) L` with `L = freqNormLo` of the `N = 65`
boxes; here `L = κ ≈ 1.99999` (coordinate `1`), so the margins are `≈ 2 · 10⁻⁶` and `≈ 2`
against `ν = 10⁻⁶`. -/
theorem lunarR2_rayMargins :
    let p := lunarR2 0 0
    (decide (0 < freqNormLo (lunarR2Box lunarR2MinusCoeffs)) &&
      decide (p.nuRay ≤ (p.s - 1) * freqNormLo (lunarR2Box lunarR2MinusCoeffs)) &&
      decide (p.nuRay ≤ (p.σω - p.s) * freqNormLo (lunarR2Box lunarR2MinusCoeffs)) &&
      decide (0 < freqNormLo (lunarR2Box lunarR2PlusCoeffs)) &&
      decide (p.nuRay ≤ (p.s - 1) * freqNormLo (lunarR2Box lunarR2PlusCoeffs)) &&
      decide (p.nuRay ≤ (p.σω - p.s) * freqNormLo (lunarR2Box lunarR2PlusCoeffs))) = true := by
  decide +kernel

theorem lunarR2Box_normLo :
    freqNormLo (lunarR2Box lunarR2MinusCoeffs) = lunarR2Kappa ∧
      freqNormLo (lunarR2Box lunarR2PlusCoeffs) = lunarR2Kappa := by
  decide +kernel

end KAM.SpinOrbit
