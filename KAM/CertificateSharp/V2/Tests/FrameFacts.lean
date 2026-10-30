/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.TrigFacts
import KAM.CertificateSharp.V2.RouteARefinedEngine

/-!
# The frame majorants of C4 on the toy T2, behind a private import

`FrameFacts` by `frameFacts_of`. The import is private, as in `Tests/TrigFacts.lean`.
-/

public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The frame bounds of T2, by the majorants of C4. -/
theorem toyCert2_frameFacts {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 toyCert2.freqBox ωstar)
    (B : BaseFacts toyCert2 ωstar) : FrameFacts toyCert2 toyTrigClaim ωstar := by
  have h : KAM.CertificateSharp.checkFrameMajorants toyCert2
      (toyTrigClaim.frame toyCert2.freqBox) = true := by decide +kernel
  exact frameFacts_of B h hω

end KAM.CertificateSharp.V2

end
