/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Sharp
public import KAM.Certificate.Tests.Toy2
public import KAM.Certificate.Tests.Toy3

/-!
# The old and the sharp certifier on the toy certificates

For the toys T2 and T3 (`Tests/Toy2`, `Tests/Toy3`, read-only) both smallness tests are evaluated
by `decide +kernel`, and the margins (threshold divided by the error term) are certified:

| toy | `γ⁴ρ^{4τ}/(C₁ e)` old | sharp | `disp γ²ρ^{2τ}/(C₂ e)` old | sharp `max{C₂,C₃}` |
|---|---|---|---|---|
| T2 | `> 10^4` | `> 10^19` | `≥ 1` | `> 10^5` |
| T3 | `> 10^4` | `> 10^27` | `≥ 1` | `> 10^9` |

The sharp certifier passes every sub-check of the old one (`checkTorusCertificateSharp_of_old`)
and its own test `sharpTest`. The exact numbers are the kernel-checked inequalities below.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM.Certificate

theorem toyCert2_sharpTest : sharpTest toyCert2 = true := by decide +kernel
theorem toyCert3_sharpTest : sharpTest toyCert3 = true := by decide +kernel

theorem toyCert2_sharp_passes : checkTorusCertificateSharp toyCert2 = true :=
  checkTorusCertificateSharp_of_old toyCert2_passes toyCert2_sharpTest

theorem toyCert3_sharp_passes : checkTorusCertificateSharp toyCert3 = true :=
  checkTorusCertificateSharp_of_old toyCert3_passes toyCert3_sharpTest

/-- T2, smallness margin: old `> 10^4`, sharp `> 10^19`. -/
theorem toyCert2_margin_old :
    10 ^ 4 * (isoC1Q 2 1 toyCert2.params.rho toyCert2.params.rhoInf toyCert2.params.M
      toyCert2.params.σK toyCert2.params.σB toyCert2.params.σT toyCert2.params.μ
      toyCert2.params.nuRay toyCert2.params.γbar * toyCert2.params.err) <
      toyCert2.params.γ ^ 4 * toyCert2.params.rho ^ (4 * 1) := by decide +kernel

theorem toyCert2_margin_sharp :
    10 ^ 19 * (sharpIsoC1Q 2 1 (cRRQ 2 1) toyCert2.params.M toyCert2.params.σK
      toyCert2.params.σB toyCert2.params.σT toyCert2.params.γbar toyCert2.params.μ
      toyCert2.params.nuRay toyCert2.params.rho toyCert2.params.rhoInf * toyCert2.params.err) <
      toyCert2.params.γ ^ 4 * toyCert2.params.rho ^ (4 * 1) := by decide +kernel

/-- T2, displacement margin: the sharp displacement bound is `10^5` below the claimed `disp`. -/
theorem toyCert2_disp_sharp :
    10 ^ 5 * (max (sharpIsoC2Q 2 1 (cRRQ 2 1) toyCert2.params.M toyCert2.params.σK
      toyCert2.params.σB toyCert2.params.σT toyCert2.params.γbar toyCert2.params.rho
      toyCert2.params.rhoInf) (sharpIsoC3Q 2 1 (cRRQ 2 1) toyCert2.params.M toyCert2.params.σK
      toyCert2.params.σB toyCert2.params.σT toyCert2.params.γbar toyCert2.params.rho
      toyCert2.params.rhoInf) * toyCert2.params.err) ≤
      toyCert2.params.disp * (toyCert2.params.γ ^ 2 * toyCert2.params.rho ^ (2 * 1)) := by
  decide +kernel

/-- T3, smallness margin: old `> 10^4`, sharp `> 10^27`. -/
theorem toyCert3_margin_old :
    10 ^ 4 * (isoC1Q 3 2 toyCert3.params.rho toyCert3.params.rhoInf toyCert3.params.M
      toyCert3.params.σK toyCert3.params.σB toyCert3.params.σT toyCert3.params.μ
      toyCert3.params.nuRay toyCert3.params.γbar * toyCert3.params.err) <
      toyCert3.params.γ ^ 4 * toyCert3.params.rho ^ (4 * 2) := by decide +kernel

theorem toyCert3_margin_sharp :
    10 ^ 27 * (sharpIsoC1Q 3 2 (cRRQ 3 2) toyCert3.params.M toyCert3.params.σK
      toyCert3.params.σB toyCert3.params.σT toyCert3.params.γbar toyCert3.params.μ
      toyCert3.params.nuRay toyCert3.params.rho toyCert3.params.rhoInf * toyCert3.params.err) <
      toyCert3.params.γ ^ 4 * toyCert3.params.rho ^ (4 * 2) := by decide +kernel

theorem toyCert3_disp_sharp :
    10 ^ 9 * (max (sharpIsoC2Q 3 2 (cRRQ 3 2) toyCert3.params.M toyCert3.params.σK
      toyCert3.params.σB toyCert3.params.σT toyCert3.params.γbar toyCert3.params.rho
      toyCert3.params.rhoInf) (sharpIsoC3Q 3 2 (cRRQ 3 2) toyCert3.params.M toyCert3.params.σK
      toyCert3.params.σB toyCert3.params.σT toyCert3.params.γbar toyCert3.params.rho
      toyCert3.params.rhoInf) * toyCert3.params.err) ≤
      toyCert3.params.disp * (toyCert3.params.γ ^ 2 * toyCert3.params.rho ^ (2 * 2)) := by
  decide +kernel

end KAM.CertificateSharp
