/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Constants
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The rational mirrors and their comparison lemmas

Mirrors (suffix `Q`) of the constants of `KAM/Sharp/Constants.lean` and
`KAM/Iso/Sharp/Constants.lean` at `κ = τ ∈ ℕ`, with `c_R` an arbitrary rational `cR` (to be
instantiated at `cRRQ n τ`). `DomA`, `DomB`, `DomC` record, for the three layers of the chain, that
each real constant (at the casts of the rational data and a real `cR ≤ cR`-mirror) is positive and
at most its mirror.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Sharp KAM.Iso.Sharp

section Mirrors

variable (n τ : ℕ) (cR M σK σB σT γb μ ν : ℚ)

def thetaSQ : ℚ := 2 * n * σK * σB * (M + 1)
def cOmQ : ℚ := 2 * n * (n + 1) * cR * σK
def cSymQ : ℚ := max 1 (σB ^ 2) * cOmQ n cR σK
def cRedQ : ℚ := 2 * n * σK * max (n * σB) (n + σB)
def cT0Q : ℚ := 4 * n * M * σK ^ 2 * σB ^ 2
def cT1Q : ℚ := 2 * (n : ℚ) ^ 2 * σK * σB ^ 2
def wTQ : ℚ := 4 * n * M * σK ^ 2 + 2 * n * (n + 1) * σK
def cT2Q : ℚ := (2 : ℚ) ^ (τ + 1) * σB ^ 3 * wTQ n M σK * cOmQ n cR σK
def hTQ : ℚ := cT0Q n M σK σB + 1
def cGramQ : ℚ := 2 * n * σK * (n * (1 + 1 / 8) + 1)
def cBQ : ℚ := 8 / 7 * σB ^ 2 * cGramQ n σK
def cDabQ : ℚ := 4 * (8 / 7) ^ 4 * n * M * σK ^ 2 * σB ^ 2 *
  (2 * cBQ n σK σB / σB + (n + 1) / σK + 1)
def cDcQ : ℚ := 2 * n * (8 / 7) ^ 5 * σK * σB ^ 3 * wTQ n M σK * (n + 8 / 7)

def iCSQ : ℚ := σT * max (2 * n * σK * σB * γb + 2 * n * cR * σK * hTQ n M σK σB)
  (γb + 2 * n * cR * M * σK ^ 2 * σB)
def iCXiNQ : ℚ := iCSQ n cR M σK σB σT γb + 2 * n * cR * σK
def iCGQ : ℚ := hTQ n M σK σB * iCXiNQ n cR M σK σB σT γb +
  thetaSQ n M σK σB * iCSQ n cR M σK σB σT γb + 2 * n * σK * σB * γb
def iCDXiQ : ℚ := max (iCGQ n cR M σK σB σT γb) (2 * n * σK * γb)
def iCXiQ : ℚ := max (cR * iCGQ n cR M σK σB σT γb) (γb * iCXiNQ n cR M σK σB σT γb)
def iCDKQ : ℚ := σK * (cR * iCGQ n cR M σK σB σT γb + σB * γb * iCXiNQ n cR M σK σB σT γb)
def iCDwQ : ℚ := thetaSQ n M σK σB * γb * iCSQ n cR M σK σB σT γb
def iCPQ : ℚ := (M * σK + n) * (1 + σB) + 2 * n * σK ^ 2 * σB ^ 2 * (2 * M * σK + n + 1)
def iCdKQ : ℚ := iCPQ n M σK σB * iCXiQ n cR M σK σB σT γb +
  σK * (1 + σB) * γb * iCDXiQ n cR M σK σB σT γb
def iCLinQ : ℚ := cRedQ n σK σB * iCXiQ n cR M σK σB σT γb +
  cSymQ n cR σK σB * iCDXiQ n cR M σK σB σT γb +
  thetaSQ n M σK σB * cOmQ n cR σK * iCSQ n cR M σK σB σT γb
def iCE1Q : ℚ := 2 * σK * (1 + σB) * γb ^ 2 * iCLinQ n cR M σK σB σT γb +
  M / 2 * iCDKQ n cR M σK σB σT γb ^ 2 + γb * iCSQ n cR M σK σB σT γb * iCdKQ n cR M σK σB σT γb
def iCE2Q : ℚ := γb * n * (2 * n * σK * γb + thetaSQ n M σK σB * cOmQ n cR σK) * cR *
  iCGQ n cR M σK σB σT γb + M / 2 * iCDKQ n cR M σK σB σT γb ^ 2
def iCEQ : ℚ := max (iCE1Q n cR M σK σB σT γb) (iCE2Q n cR M σK σB σT γb)
def iCDTQ : ℚ := (cDabQ n M σK σB + cDcQ n M σK σB) * iCDKQ n cR M σK σB σT γb +
  (1 + (8 / 7) ^ 3) * cT1Q n σK σB * γb ^ 2 +
  (1 + (8 / 7) ^ 5) * σB ^ 3 * wTQ n M σK * cOmQ n cR σK * γb
def iCDTbQ : ℚ := max (iCDTQ n cR M σK σB σT γb + iCDwQ n cR M σK σB σT γb)
  (n * iCDwQ n cR M σK σB σT γb + 2 * (n : ℚ) ^ 2 * (1 + (8 / 7) ^ 2) * σK * σB * γb ^ 2)
def iRateDQ : ℚ := n * iCDKQ n cR M σK σB σT γb
def iRateBQ : ℚ := cBQ n σK σB * iCDKQ n cR M σK σB σT γb
def iRateTQ : ℚ := 8 / 7 * σT ^ 2 * iCDTbQ n cR M σK σB σT γb
def iCStepQ : ℚ := max (γb ^ 4 * (1 + cT1Q n σK σB) + γb ^ 3 * cT2Q n τ cR M σK σB)
  (max (2 * γb ^ 3 * cSymQ n cR σK σB)
    (max (γb ^ 2 * iRateDQ n cR M σK σB σT γb / (1 / 8 * σK))
      (max (γb ^ 2 * σB * cGramQ n σK * iCDKQ n cR M σK σB σT γb / (1 / 8))
        (max (γb ^ 2 * σT * iCDTbQ n cR M σK σB σT γb / (1 / 8)) (iCEQ n cR M σK σB σT γb)))))
def iCSumQ : ℚ := 4 * γb ^ 2 * max (2 * iCDKQ n cR M σK σB σT γb)
  (max (iRateDQ n cR M σK σB σT γb) (max (iRateBQ n cR M σK σB σT γb)
    (iRateTQ n cR M σK σB σT γb)))
def iCStarQ : ℚ := max ((2 : ℚ) ^ (2 * (2 * τ)) * iCEQ n cR M σK σB σT γb)
  (max (iCStepQ n τ cR M σK σB σT γb)
    (max (iCSumQ n cR M σK σB σT γb / μ) (4 * γb ^ 2 * iCDwQ n cR M σK σB σT γb / ν)))

/-- `δ₀ = min {1, (ρ - ρ∞)/6}`. -/
def delta0sQ (ρ ρinf : ℚ) : ℚ := min 1 ((ρ - ρinf) / (2 * 3))

/-- Mirror of `sharpIsoC1` (`κ = τ`). -/
def sharpIsoC1Q (ρ ρinf : ℚ) : ℚ := ρ ^ (4 * τ) *
  max (γb ^ 4) (iCStarQ n τ cR M σK σB σT γb μ ν * (delta0sQ ρ ρinf ^ (2 * (2 * τ)))⁻¹)
/-- Mirror of `sharpIsoC2`. -/
def sharpIsoC2Q (ρ ρinf : ℚ) : ℚ :=
  2 * iCDKQ n cR M σK σB σT γb * ρ ^ (2 * τ) * (delta0sQ ρ ρinf ^ (2 * τ))⁻¹
/-- Mirror of `sharpIsoC3`. -/
def sharpIsoC3Q (ρ ρinf : ℚ) : ℚ :=
  2 * iCDwQ n cR M σK σB σT γb * ρ ^ (2 * τ) * (delta0sQ ρ ρinf ^ (2 * τ))⁻¹

end Mirrors

end KAM.CertificateSharp
