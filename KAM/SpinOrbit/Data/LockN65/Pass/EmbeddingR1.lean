/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Witness
public import KAM.SpinOrbit.LunarAssemblyV2
public import KAM.SpinOrbit.Data.LockN65.DK.Mat

/-!
# The N = 65 lock: embedding check, the `DK` row sum 1

One kernel run (`decide +kernel`) on the `DK` literals (`DK/Mat`); `checkEmbedding` splits index by
index (the monolithic check was OOM-killed at 10 GB).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_embeddingR1 :
    ble (dkRowUp 2 base.emb base.weight base.piEnc 1)
      (ofRatDown (base.params.σK - base.params.μ)) = true := by
  unfold dkRowUp
  rw [lock_dkMat]
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
