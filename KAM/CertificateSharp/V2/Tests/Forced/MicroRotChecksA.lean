/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroRotData
public import KAM.CertificateSharp.V2.Engine

/-!
# Landed sub-checks of the forced toy `MicroRot` (part A)

`static_ok`, `hamBounds_ok`, `embedding_ok`, one `decide +kernel` each.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroRot

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

theorem static_ok : checkStatic cert = true := by decide +kernel

theorem hamBounds_ok : checkHamBounds cert = true := by decide +kernel

theorem embedding_ok : checkEmbedding cert = true := by decide +kernel

end KAM.CertificateSharp.V2.Forced.MicroRot

end
