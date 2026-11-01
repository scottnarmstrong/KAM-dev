/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyData
public import KAM.CertificateSharp.V2.Engine

/-!
# The direct landed sub-checks of the forced toy `Tiny`

`checkStatic`, `checkHamBounds`, `checkEmbedding`, `checkInvariance`, `checkEnergy` on `Tiny.cert`,
one `decide +kernel` each. The Gram and torsion checks are in `TinyBase` (memoized stages).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate

theorem static_ok : checkStatic cert = true := by decide +kernel

theorem hamBounds_ok : checkHamBounds cert = true := by decide +kernel

theorem embedding_ok : checkEmbedding cert = true := by decide +kernel

theorem invariance_ok : checkInvariance cert = true := by decide +kernel

theorem energy_ok : checkEnergy cert = true := by decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
