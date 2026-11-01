/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyL1HybData
public import KAM.CertificateSharp.V2.RouteAL1

/-!
# Route A with the ℓ¹ entry on the forced toy `Tiny`: the numerical core and its rejections

The rational parts of `L1.l1Core` at the witness `l1Wit` (`TinyL1HybData`), each by its own kernel
run: the run on the strip `ρ' = 1/10` is well formed (`l1_wf`), passes (J0)–(J3) with the ℓ¹ entry
at `X⋆ = 1830` (`l1_ok`), its classical tail (`l1_tail`), the entry record against the ℓ¹ claim
and the fibered `Γ_∞` tests (`l1_entry`) and the final comparisons (`l1_final`). The certified
sites and the assembled `l1Core` are in the opt-in
`kernel-tests/CertificateSharp/V2/ForcedL1Hybrid.lean` (the sites take about 10 s).

Rejections (each decides that the rejecting conjunct is `false`):
* `mut_l1Xs`: the run at `10 X⋆` (the caps (J3) fail);
* `mut_l1aN`: the entry record with `a_N` halved (the Wiener product `|Lᵀ Ω₀|₁ |E|₁ ≤ a_N e` fails);
* `mut_l1G0`: the claim `Γ_∞(sω*, δ₀') ≤ G₀/2` (the fibered test fails);
* `mut_l1err`: the error `e* = X⋆ γ⁴ δ₀'⁴` itself, at the strip of the run (strict smallness).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The rational numbers of the run on the strip `ρ'`. -/
def l1Q : NumQ := l1Wit.num 2 cert.params cert.freqBox

theorem l1_Xs : 0 < l1Wit.base.core.Xs := by decide +kernel

theorem l1_wf : l1Q.wfOk = true := by decide +kernel

theorem l1_ok : L1.okL1 l1Q l1Wit.E (capQ l1Q cert.params.μ cert.params.nuRay)
    (initQ l1Wit.base.R.bL l1Wit.base.R.bN l1Wit.base.R.bNt l1Wit.base.R.bT cert.params.σK
      cert.params.σB cert.params.σT cert.params.μ) l1Wit.base.core.Xs = true := by decide +kernel

theorem l1_tail : classicalOk 2 cert.params.tau l1Wit.base.core.J (l1Q.δ l1Wit.base.core.kp)
    l1Q.ctail = true := by decide +kernel

theorem l1_entry : L1.entryOk 2 l1Q cert.params cert.freqBox l1Wit = true := by decide +kernel

theorem l1_final : L1.finalL1 l1Q l1Wit.E cert.params cert.freqBox l1Wit.base.core.Xs = true := by
  decide +kernel

/-- Rejected: the run at `10 X⋆` (the caps of (J3)). -/
theorem mut_l1Xs : L1.okL1 l1Q l1Wit.E (capQ l1Q cert.params.μ cert.params.nuRay)
    (initQ l1Wit.base.R.bL l1Wit.base.R.bN l1Wit.base.R.bNt l1Wit.base.R.bT cert.params.σK
      cert.params.σB cert.params.σT cert.params.μ) (10 * l1Wit.base.core.Xs) = false := by
  decide +kernel

/-- Rejected: `a_N` halved (the Wiener product of the entry). -/
theorem mut_l1aN : L1.entryOk 2 l1Q cert.params cert.freqBox
    { l1Wit with E := { l1Wit.E with aN := l1Wit.E.aN / 2 } } = false := by decide +kernel

/-- Rejected: the claim `Γ_∞(sω*, δ₀') ≤ G₀ / 2` (the fibered test). -/
theorem mut_l1G0 : L1.entryOk 2 l1Q cert.params cert.freqBox
    { l1Wit with E := { l1Wit.E with G0 := l1Wit.E.G0 / 2 } } = false := by decide +kernel

/-- Rejected: the error at the threshold `e* = X⋆ γ⁴ δ₀'⁴` of the run (strict smallness). -/
theorem mut_l1err : L1.finalL1 l1Q l1Wit.E
    { cert.params with err := l1Wit.base.core.Xs * cert.params.γ ^ 4 * l1Q.δ0 ^ 4 } cert.freqBox
    l1Wit.base.core.Xs = false := by decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
