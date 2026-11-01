/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyC2Data
public import KAM.CertificateSharp.V2.Engine

/-!
# The direct landed sub-checks of the forced toy `TinyC2`

`checkStatic`, `checkHamBounds`, `checkEmbedding`, `checkInvariance`, `checkEnergy` on
`TinyC2.cert`, one `decide +kernel` each. The Gram and torsion checks are in `TinyC2Base`
(memoized stages).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.TinyC2

open KAM.Certificate

theorem static_ok : checkStatic cert = true := by decide +kernel

theorem hamBounds_ok : checkHamBounds cert = true := by decide +kernel

theorem embedding_ok : checkEmbedding cert = true := by decide +kernel

theorem invariance_ok : checkInvariance cert = true := by decide +kernel

theorem energy_ok : checkEnergy cert = true := by decide +kernel

end KAM.CertificateSharp.V2.Forced.TinyC2

end
