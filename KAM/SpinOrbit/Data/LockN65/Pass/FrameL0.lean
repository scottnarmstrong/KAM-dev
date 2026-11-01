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
# The N = 65 lock: frame majorant L, column 0

One kernel run (`decide +kernel`): the joint corner bound of column 0 of `DK` (`checkFrameL` splits by
column; the monolithic check was OOM-killed at 8 GB).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_frameL0 :
    rowCornerLeq base.weight (wloOf base.weight base.expOrder) 2
      ((List.finRange (2 + 2)).map fun r =>
        modelMatrixEntry (dkModels 2 base.emb base.weight base.piEnc) r.val 0)
      (ofRatDown refinedWit.R.bL) = true := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
