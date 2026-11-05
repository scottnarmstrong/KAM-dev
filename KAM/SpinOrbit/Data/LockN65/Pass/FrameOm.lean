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
# The N = 65 lock: frame majorant Ω

One kernel run (`decide +kernel`), as for the band data in
`KAM/SpinOrbit/Data/Upper/Pass/Core.lean`.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_frameOm :
    checkFrameOmega base (refinedWit.R.frame base.freqBox).bOm = true := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
