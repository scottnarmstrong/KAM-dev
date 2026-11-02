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
# The N = 65 lock: frame majorant L, column 1

The joint corner bound of column 1 of `DK`: the `DK` matrix is rewritten to its kernel-checked
literals (`DK/Mat`), then one kernel run on the literals (computing the four `DK` models inline
peaked at 9.4-10.3e9 B).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_frameL1 :
    rowCornerLeq base.weight (wloOf base.weight base.expOrder) 2
      ((List.finRange (2 + 2)).map fun r =>
        modelMatrixEntry (dkModels 2 base.emb base.weight base.piEnc) r.val 1)
      (ofRatDown refinedWit.R.bL) = true := by
  rw [lock_dkMat]
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
