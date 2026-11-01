/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyL1Claim
public import KAM.CertificateSharp.Kernel.StageHyb

/-!
# The step checks of the hybrid restart on the forced toy `Tiny`

The model checks of `Hybrid.hybStepOk` at the Newton step `hybDK` (`TinyL1HybData`), each by its
own kernel run: the step norms `(S1)–(S4)` (`hyb_poly`) and `(S5)`, `ℓ_H` (`hyb_comp`): the
linearised error `Ẽ = E + DX_H ΔK − DΔK · s₁ω*` and the energy, from the three compositions of the
landed checks, memoized (`msF_eq` of `TinyL1Claim`, `msT_eq`, `mvF_eq`; `hybCompOk_eq_of`).

Rejection: `hyb_zeroStep_rejects`. Without the step (`ΔK̂ = 0`) the linearised error is the base
error `4.1·10⁻¹²`, far above the claim `ℓ_E = 5.36·10⁻¹⁵`: the Newton cancellation on the
coefficients is what the restart certifies; `hyb_lE_tight`, the claim `ℓ_E` lowered by `10⁻³`
(the claim is the mirror's value rounded up by at most `3·10⁻⁴`: the port of `linModel` and the
kernel agree, from both sides). `‖Ω‖` (`(S6)`, `(S7)`) is in `TinyHybOmega`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The low-stage composition (first and second derivatives along `K`, `checkTorsion`'s). -/
theorem msT_eq : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgLow
    cert.piEnc (torsionSlots 2 cert.ham.jet) = some ms :=
  eq_of_optModelsBeq (by decide +kernel)

/-- The energy composition (`checkEnergy`'s). -/
theorem mvF_eq : Slp.compose 2 cert.ham.jet.prog cert.emb cert.wit cert.weight cert.cfgFull
    cert.piEnc [cert.ham.jet.v0] = some mvF :=
  eq_of_optModelsBeq (by decide +kernel)

theorem hyb_poly : Hybrid.hybPolyOk (n := 2) hybWit.step cert.piEnc = true := by decide +kernel

/-- `(S5)` and `ℓ_H`: the linearised error and energy from the memoized compositions. -/
theorem hyb_comp : Hybrid.hybCompOk cert hybWit.step = true := by
  rw [Hybrid.hybCompOk_eq_of msF_eq msT_eq mvF_eq]
  decide +kernel

/-- Rejected: the claims of the step without the step (`ΔK̂ = 0`). -/
theorem hyb_zeroStep_rejects : Hybrid.hybCompOk cert
    { hybWit.step with dK := ⟨[-1, 0], [⟨0, []⟩, ⟨0, []⟩], [0, 0], [⟨0, []⟩, ⟨0, []⟩]⟩ } =
      false := by
  rw [Hybrid.hybCompOk_eq_of msF_eq msT_eq mvF_eq]
  decide +kernel

/-- Rejected: the claim `ℓ_E` lowered by `10⁻³`. -/
theorem hyb_lE_tight : Hybrid.hybCompOk cert
    { hybWit.step with cl := { hybWit.step.cl with lE := hybWit.step.cl.lE * 999 / 1000 } } =
      false := by
  rw [Hybrid.hybCompOk_eq_of msF_eq msT_eq mvF_eq]
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
