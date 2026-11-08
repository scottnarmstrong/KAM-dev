/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Witness
public import KAM.SpinOrbit.LunarAssemblyV2
public import KAM.SpinOrbit.Data.LockN65.JetEq
public import KAM.SpinOrbit.Data.LockN65.HamBalls
public import KAM.SpinOrbit.Data.LockN65.HamOk
public import KAM.SpinOrbit.Data.LockN65.HamBridge

/-!
# The N = 65 lock: Hamiltonian bounds

From the kernel-checked pieces: the jet bridge `lock_jet` (JetEq), the segmented disc pass
`lock_balls` (HamBalls) and `lock_hamBoundsOk` (HamOk). The monolithic `decide +kernel` (the band
data's form) was OOM-killed at 8 GB.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_hamBounds :
    checkHamBounds base = true :=
  checkHamBounds_of_parts (c := base) lock_jet lock_balls lock_hamBoundsOk

end KAM.SpinOrbit.Data.LockN65
