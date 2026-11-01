/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroPackedData

/-!
# The refined claim and the refined core of `MicroP.wit`

`hamClaim_ok`: the landed disc pass (`checkHamClaim`) at the claim `MicroP.wit.R`;
`refined_core`: the numerical test of route A refined (`refinedCore`: the schedule, the caps from
the claimed frame bounds, classical sites, the final clause). One kernel run each.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroP

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem hamClaim_ok : checkHamClaim cert wit.R = true := by decide +kernel

theorem refined_core : refinedCore 2 cert.params cert.freqBox wit = true := by decide +kernel

end KAM.CertificateSharp.V2.Forced.MicroP

end
