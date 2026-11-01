/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyC2Data
public import KAM.SpinOrbit.RotFreqN
public import KAM.Certificate.Freq

/-!
# The reference frequency of the forced toy `TinyC2`

`ω* = κ (ν₋(8) - 1, 1) = lunarRotFreq (lunarNuMinusN 8) κ`, `κ = (2000000 / 1000001)`: the box of
`TinyC2.cert` encloses it (`freq`: a root enclosure of `√5` and `checkAlgBox` at the exact `ℚ(√5)`
description `lunarRotFreqMinusN_eq`), and it is `(κ / 10, 1)`-Diophantine
(`lunarRotFreqMinusN_isDiophantine`), which is the certificate's `(γ, τ)` (`dio`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.TinyC2

open KAM KAM.Certificate KAM.SpinOrbit

/-- The scale `κ = c / s` of the reference vector. -/
def κ : ℚ := (2000000 / 1000001)

/-- The reference vector `κ (ν₋(8) - 1, 1)`. -/
noncomputable def ωstar : Fin 2 → ℝ := lunarRotFreq (lunarNuMinusN 8) κ

/-- The lower end of the enclosure of `√5`. -/
def rootLo : ℚ :=
  (11180339887498948482045868343656381177203 / 5000000000000000000000000000000000000000)

/-- The upper end of the enclosure of `√5`. -/
def rootHi : ℚ :=
  (22360679774997896964091736687312762354407 / 10000000000000000000000000000000000000000)

theorem freq : FreqEncloses 2 cert.freqBox ωstar := by
  have hx := sqrt_mem_of_checkRootEnclosure
    (show checkRootEnclosure 2 5 rootLo rootHi = true by decide +kernel)
  rw [Nat.cast_ofNat] at hx
  rw [ωstar, lunarRotFreqMinusN_eq]
  exact algFreq_encloses hx (by decide +kernel)

theorem dio : IsDiophantine ((cert.params.γ : ℚ) : ℝ) ((cert.params.tau : ℕ) : ℝ) ωstar := by
  have h := lunarRotFreqMinusN_isDiophantine 8 (by norm_num) (κ := κ) (by norm_num [κ])
  have hγ : ((cert.params.γ : ℚ) : ℝ) = (κ : ℝ) / ((8 : ℕ) + 2) := by
    rw [show cert.params.γ = κ / 10 by decide +kernel]
    push_cast
    norm_num
  have hτ : ((cert.params.tau : ℕ) : ℝ) = 1 := by
    rw [show cert.params.tau = 1 by decide +kernel]
    norm_num
  rw [hγ, hτ]
  exact h

end KAM.CertificateSharp.V2.Forced.TinyC2

end
