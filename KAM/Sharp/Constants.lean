/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The constants of the sharp fixed-frequency theorem

Definition `bp:p2s:constants` (`blueprint/parts/p2s-sharp.tex`), transcribed from
`docs/campaign/design/APOST-SHARP-SIGNATURES.lean.txt`; the exact mirror is
`scripts/apost_sharp/thresholds.py`. The exponent is `a = 2κ`.

`delta0s ρ ρinf = min 1 ((ρ - ρinf) / (2 * 3))` is `KAM.Sharp.Engine.delta0 3 ρ ρinf`, unfolded: the
engine (package SHARP-A1) is not an import of this file.
-/

@[expose] public noncomputable section

namespace KAM.Sharp

/-- `ϑ = 1/8`. -/
def vth : ℝ := 1 / 8
/-- `ϑ̂ = (1 - ϑ)⁻¹ = 8/7`. -/
def vthh : ℝ := 8 / 7

variable (n : ℕ) (κ cR M σK σB σT γb μ : ℝ)

def cOm : ℝ := 2 * n * (n + 1) * cR * σK
def cSym : ℝ := max 1 (σB ^ 2) * cOm n cR σK
def cRed : ℝ := 2 * n * σK * max (n * σB) (n + σB)
def cT0 : ℝ := 4 * n * M * σK ^ 2 * σB ^ 2
def cT1 : ℝ := 2 * (n : ℝ) ^ 2 * σK * σB ^ 2
def wT : ℝ := 4 * n * M * σK ^ 2 + 2 * n * (n + 1) * σK
def cT2 : ℝ := (2 : ℝ) ^ (κ + 1) * σB ^ 3 * wT n M σK * cOm n cR σK
def hT : ℝ := cT0 n M σK σB + 1
def cXi0 : ℝ := 2 * n * σK * σT * (σB * γb + cR * hT n M σK σB)
def cXiN : ℝ := cXi0 n cR M σK σB σT γb + 2 * n * cR * σK
def cG : ℝ := hT n M σK σB * cXiN n cR M σK σB σT γb + 2 * n * σK * σB * γb
def cDXi : ℝ := max (cG n cR M σK σB σT γb) (2 * n * σK * γb)
def cXi : ℝ := max (cR * cG n cR M σK σB σT γb) (γb * cXiN n cR M σK σB σT γb)
def cDK : ℝ := σK * (cR * cG n cR M σK σB σT γb + σB * γb * cXiN n cR M σK σB σT γb)
def cLin : ℝ := cRed n σK σB * cXi n cR M σK σB σT γb + cSym n cR σK σB * cDXi n cR M σK σB σT γb
def cE : ℝ := 2 * σK * (1 + σB) * γb ^ 2 * cLin n cR M σK σB σT γb +
  M / 2 * cDK n cR M σK σB σT γb ^ 2
def cGram : ℝ := 2 * n * σK * (n * (1 + vth) + 1)
def cB : ℝ := vthh * σB ^ 2 * cGram n σK
def cDab : ℝ := 4 * vthh ^ 4 * n * M * σK ^ 2 * σB ^ 2 *
  (2 * cB n σK σB / σB + (n + 1) / σK + 1)
def cDc : ℝ := 2 * n * vthh ^ 5 * σK * σB ^ 3 * wT n M σK * (n + vthh)
def cDT : ℝ := (cDab n M σK σB + cDc n M σK σB) * cDK n cR M σK σB σT γb +
  (1 + vthh ^ 3) * cT1 n σK σB * γb ^ 2 + (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * γb
def rateD : ℝ := n * cDK n cR M σK σB σT γb
def rateB : ℝ := cB n σK σB * cDK n cR M σK σB σT γb
def rateT : ℝ := vthh * σT ^ 2 * cDT n cR M σK σB σT γb
def cStep : ℝ := max (γb ^ 4 * (1 + cT1 n σK σB) + γb ^ 3 * cT2 n κ cR M σK σB)
  (max (2 * γb ^ 3 * cSym n cR σK σB)
    (max (γb ^ 2 * rateD n cR M σK σB σT γb / (vth * σK))
      (max (γb ^ 2 * σB * cGram n σK * cDK n cR M σK σB σT γb / vth)
        (max (γb ^ 2 * σT * cDT n cR M σK σB σT γb / vth) (cE n cR M σK σB σT γb)))))
def cSum : ℝ := 4 * γb ^ 2 * max (2 * cDK n cR M σK σB σT γb)
  (max (rateD n cR M σK σB σT γb) (max (rateB n cR M σK σB σT γb) (rateT n cR M σK σB σT γb)))
def cStar : ℝ := max ((2 : ℝ) ^ (2 * (2 * κ)) * cE n cR M σK σB σT γb)
  (max (cStep n κ cR M σK σB σT γb) (cSum n cR M σK σB σT γb / μ))
/-- `δ₀ = min {1, (ρ - ρ∞)/6}` (loss `3δ` per step). -/
def delta0s (ρ ρinf : ℝ) : ℝ := min 1 ((ρ - ρinf) / (2 * 3))
/-- The bound of the torsion change in `bp:p2s:perturbation`(d). -/
def twistD (γ ε δ d : ℝ) : ℝ := (cDab n M σK σB + cDc n M σK σB) * d / δ +
  (1 + vthh ^ 3) * cT1 n σK σB * ε / δ +
  (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * ε / (γ * δ ^ (κ + 1))

/-- `C₁^♯ = ρ^{4τ} max {γ̄⁴, 𝔠_* δ₀^{-2a}}`, `a = 2κ`. -/
def sharpC1 (τ ρ ρinf : ℝ) : ℝ :=
  ρ ^ (4 * τ) * max (γb ^ 4) (cStar n κ cR M σK σB σT γb μ * delta0s ρ ρinf ^ (-(2 * (2 * κ))))
/-- `C₂^♯ = 2 C_ΔK ρ^{2τ} δ₀^{-a}`. -/
def sharpC2 (τ ρ ρinf : ℝ) : ℝ :=
  2 * cDK n cR M σK σB σT γb * ρ ^ (2 * τ) * delta0s ρ ρinf ^ (-(2 * κ))

end KAM.Sharp

end
