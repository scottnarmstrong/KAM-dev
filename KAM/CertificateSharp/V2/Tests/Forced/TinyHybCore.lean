/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyL1HybData
public import KAM.CertificateSharp.Kernel.StageHyb

/-!
# The hybrid restart on the forced toy `Tiny`: the rational checks and their rejections

The rational parts of `Hybrid.checkHybrid` at the witness `hybWit` (`TinyL1HybData`), each by its
own kernel run: the transfer checks H0–H4 (`hyb_transfer`), the weights and strips
(`hyb_weights`), the Cauchy bound of `DE` (`hyb_cauchy`), the frequency shift (`hyb_dw`) and the
route-A′ core at the restart numbers without its sites (`hyb_wf`, `hyb_okR`, `hyb_budget`,
`hyb_tail`, `hyb_final`; the restart error is `e₁ = 5.36·10⁻¹⁵` against the base `4.1·10⁻¹²`). The
model checks of the step, the sites and the assembled route are in `TinyHybStep` and the opt-in
`kernel-tests/CertificateSharp/V2/ForcedL1Hybrid.lean`.

Rejections:
* `mut_hybErr1`: a restart error below the step's bound `e₁ = ℓ_E + (M₂/2) d₀²` (H2);
* `mut_hybRay`: a restart ray budget twice the base's (`ν₁ ≤ ν - d_ω`);
* `mut_hybDisp`: the restart's closeness budget equal to the outer displacement (H4);
* `mut_hybCauchy`: a claim `‖DE‖ ≤ dE₀/2` below the Cauchy bound `n e/(ρ - ρT)`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The rational numbers of the restarted run. -/
def hybQ : NumQ := hybWit.w1.base.num 2 hybWit.p1 cert.freqBox

theorem hyb_transfer : Hybrid.transferOk 2 cert.params cert.freqBox hybWit = true := by
  decide +kernel

theorem hyb_weights : Hybrid.hybWeightsOk cert hybWit.step hybWit.p1.rho hybWit.p1.rhoInf
    (hybWit.ρT 2 cert.freqBox) = true := by decide +kernel

theorem hyb_cauchy : Hybrid.hybCauchyOk cert hybWit.step (hybWit.ρT 2 cert.freqBox) = true := by
  decide +kernel

theorem hyb_dw : decide (|hybWit.step.s1 - cert.params.s| * boxNormUp cert.freqBox ≤
    hybWit.step.dw) = true := by decide +kernel

theorem hyb_Xs : 0 < hybWit.w1.base.core.Xs := by decide +kernel

theorem hyb_wf : hybQ.wfOk = true := by decide +kernel

theorem hyb_okR : hybQ.okR hybWit.w1.bF (capRQ hybQ hybWit.p1.μ hybWit.p1.nuRay hybWit.w1.bT)
    (initRQ hybWit.w1.base.R.bL hybWit.w1.base.R.bN hybWit.w1.base.R.bNt hybWit.p1.σK
      hybWit.p1.σB hybWit.p1.μ) hybWit.w1.base.core.Xs = true := by decide +kernel

theorem hyb_budget : hybQ.budgetOk (hybWit.p1.σT - hybWit.p1.μ) hybWit.w1.base.R.bT hybWit.w1.bF
    hybWit.w1.bT = true := by decide +kernel

theorem hyb_tail : classicalOk 2 hybWit.p1.tau hybWit.w1.base.core.J
    (hybQ.δ hybWit.w1.base.core.kp) hybQ.ctail = true := by decide +kernel

theorem hyb_final : finalOkA hybQ hybWit.p1 cert.freqBox hybWit.w1.base.core.Xs = true := by
  decide +kernel

/-- Rejected: a restart error below the step's bound `e₁` (H2). -/
theorem mut_hybErr1 : Hybrid.transferOk 2 cert.params cert.freqBox
    { hybWit with p1 := { hybWit.p1 with err := hybWit.step.cl.lE / 2 } } = false := by
  decide +kernel

/-- Rejected: a restart ray budget above `ν - d_ω`. -/
theorem mut_hybRay : Hybrid.transferOk 2 cert.params cert.freqBox
    { hybWit with p1 := { hybWit.p1 with nuRay := 2 * cert.params.nuRay } } = false := by
  decide +kernel

/-- Rejected: the restart's closeness budget equal to the outer displacement (H4). -/
theorem mut_hybDisp : Hybrid.transferOk 2 cert.params cert.freqBox
    { hybWit with p1 := { hybWit.p1 with disp := cert.params.disp } } = false := by
  decide +kernel

/-- Rejected: a claim `‖DE‖ ≤ dE₀/2`, below the Cauchy bound. -/
theorem mut_hybCauchy : Hybrid.hybCauchyOk cert
    { hybWit.step with cl := { hybWit.step.cl with dE0 := hybWit.step.cl.dE0 / 2 } }
    (hybWit.ρT 2 cert.freqBox) = false := by decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
