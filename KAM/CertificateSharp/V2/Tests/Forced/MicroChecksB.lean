/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroData
public import KAM.CertificateSharp.V2.Engine

/-!
# Landed sub-checks of the forced toy `Micro` (part B)

`invariance_ok`, `energy_ok`, one `decide +kernel` each.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Micro

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem invariance_ok : checkInvariance cert = true := by decide +kernel

theorem energy_ok : checkEnergy cert = true := by decide +kernel

end KAM.CertificateSharp.V2.Forced.Micro

end
