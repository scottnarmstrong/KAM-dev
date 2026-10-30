/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.Constants

/-!
# The constants of the sharp isoenergetic theorem

Definition `bpI:p2s:constants` (`blueprint-I/parts/p2s-iso-sharp.tex`), transcribed from
`docs/campaign/design/APOST-SHARP-SIGNATURES.lean.txt`; the exact mirror is the `iso` branch of
`scripts/apost_sharp/thresholds.py`. The fixed-frequency constants `KAM.Sharp.*` are reused.
-/

@[expose] public noncomputable section

namespace KAM.Iso.Sharp

open KAM.Sharp

variable (n : ℕ) (κ cR M σK σB σT γb μ ν : ℝ)

/-- `Θ = 2nσ_Kσ_B(M + 1)` (`bp:p2:frequency` with `ε ≤ 1`). -/
def thetaS : ℝ := 2 * n * σK * σB * (M + 1)
def iCS : ℝ := σT * max (2 * n * σK * σB * γb + 2 * n * cR * σK * hT n M σK σB)
  (γb + 2 * n * cR * M * σK ^ 2 * σB)
def iCXiN : ℝ := iCS n cR M σK σB σT γb + 2 * n * cR * σK
def iCG : ℝ := hT n M σK σB * iCXiN n cR M σK σB σT γb + thetaS n M σK σB * iCS n cR M σK σB σT γb +
  2 * n * σK * σB * γb
def iCDXi : ℝ := max (iCG n cR M σK σB σT γb) (2 * n * σK * γb)
def iCXi : ℝ := max (cR * iCG n cR M σK σB σT γb) (γb * iCXiN n cR M σK σB σT γb)
def iCDK : ℝ := σK * (cR * iCG n cR M σK σB σT γb + σB * γb * iCXiN n cR M σK σB σT γb)
def iCDw : ℝ := thetaS n M σK σB * γb * iCS n cR M σK σB σT γb
def iCP : ℝ := (M * σK + n) * (1 + σB) + 2 * n * σK ^ 2 * σB ^ 2 * (2 * M * σK + n + 1)
def iCdK : ℝ := iCP n M σK σB * iCXi n cR M σK σB σT γb +
  σK * (1 + σB) * γb * iCDXi n cR M σK σB σT γb
def iCLin : ℝ := cRed n σK σB * iCXi n cR M σK σB σT γb +
  cSym n cR σK σB * iCDXi n cR M σK σB σT γb +
  thetaS n M σK σB * cOm n cR σK * iCS n cR M σK σB σT γb
def iCE1 : ℝ := 2 * σK * (1 + σB) * γb ^ 2 * iCLin n cR M σK σB σT γb +
  M / 2 * iCDK n cR M σK σB σT γb ^ 2 + γb * iCS n cR M σK σB σT γb * iCdK n cR M σK σB σT γb
def iCE2 : ℝ := γb * n * (2 * n * σK * γb + thetaS n M σK σB * cOm n cR σK) * cR *
  iCG n cR M σK σB σT γb + M / 2 * iCDK n cR M σK σB σT γb ^ 2
def iCE : ℝ := max (iCE1 n cR M σK σB σT γb) (iCE2 n cR M σK σB σT γb)
def iCDT : ℝ := (cDab n M σK σB + cDc n M σK σB) * iCDK n cR M σK σB σT γb +
  (1 + vthh ^ 3) * cT1 n σK σB * γb ^ 2 + (1 + vthh ^ 5) * σB ^ 3 * wT n M σK * cOm n cR σK * γb
def iCDTb : ℝ := max (iCDT n cR M σK σB σT γb + iCDw n cR M σK σB σT γb)
  (n * iCDw n cR M σK σB σT γb + 2 * (n : ℝ) ^ 2 * (1 + vthh ^ 2) * σK * σB * γb ^ 2)
def iRateD : ℝ := n * iCDK n cR M σK σB σT γb
def iRateB : ℝ := cB n σK σB * iCDK n cR M σK σB σT γb
def iRateT : ℝ := vthh * σT ^ 2 * iCDTb n cR M σK σB σT γb
def iCStep : ℝ := max (γb ^ 4 * (1 + cT1 n σK σB) + γb ^ 3 * cT2 n κ cR M σK σB)
  (max (2 * γb ^ 3 * cSym n cR σK σB)
    (max (γb ^ 2 * iRateD n cR M σK σB σT γb / (vth * σK))
      (max (γb ^ 2 * σB * cGram n σK * iCDK n cR M σK σB σT γb / vth)
        (max (γb ^ 2 * σT * iCDTb n cR M σK σB σT γb / vth) (iCE n cR M σK σB σT γb)))))
def iCSum : ℝ := 4 * γb ^ 2 * max (2 * iCDK n cR M σK σB σT γb)
  (max (iRateD n cR M σK σB σT γb) (max (iRateB n cR M σK σB σT γb) (iRateT n cR M σK σB σT γb)))
def iCStar : ℝ := max ((2 : ℝ) ^ (2 * (2 * κ)) * iCE n cR M σK σB σT γb)
  (max (iCStep n κ cR M σK σB σT γb)
    (max (iCSum n cR M σK σB σT γb / μ) (4 * γb ^ 2 * iCDw n cR M σK σB σT γb / ν)))
/-- `C₁^♯`. -/
def sharpIsoC1 (τ ρ ρinf : ℝ) : ℝ := ρ ^ (4 * τ) *
  max (γb ^ 4) (iCStar n κ cR M σK σB σT γb μ ν * delta0s ρ ρinf ^ (-(2 * (2 * κ))))
/-- `C₂^♯`. -/
def sharpIsoC2 (τ ρ ρinf : ℝ) : ℝ :=
  2 * iCDK n cR M σK σB σT γb * ρ ^ (2 * τ) * delta0s ρ ρinf ^ (-(2 * κ))
/-- `C₃^♯`. -/
def sharpIsoC3 (τ ρ ρinf : ℝ) : ℝ :=
  2 * iCDw n cR M σK σB σT γb * ρ ^ (2 * τ) * delta0s ρ ρinf ^ (-(2 * κ))

variable {n κ cR M σK σB σT γb μ ν}

end KAM.Iso.Sharp

end
