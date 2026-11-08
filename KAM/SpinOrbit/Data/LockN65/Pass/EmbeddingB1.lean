/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Witness
public import KAM.SpinOrbit.LunarAssemblyV2

/-!
# The N = 65 lock: embedding check, the action row 1

One kernel run (`decide +kernel`); `checkEmbedding` splits index by index (the monolithic check was
OOM-killed at 10 GB).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_embeddingB1 :
    ble ((actionShiftModel 2 base.emb base.weight base.piEnc (base.centre.getD 1 0) 1).supBound
      base.weight) (ofRatDown (base.radius.getD 1 0 - base.params.μ)) = true := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
