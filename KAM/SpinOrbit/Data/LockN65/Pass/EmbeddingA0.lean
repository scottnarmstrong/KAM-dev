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
# The N = 65 lock: embedding check, the angle row 0

One kernel run (`decide +kernel`); `checkEmbedding` splits index by index (the monolithic check was
OOM-killed at 10 GB).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_embeddingA0 :
    angleImOk 2 base.emb base.weight base.piEnc base.params.rho
      (base.weightH.rho - base.params.rho - base.params.μ) 0 = true := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
