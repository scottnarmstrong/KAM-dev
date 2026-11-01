/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Witness
public import KAM.SpinOrbit.LunarAssemblyV2
public import KAM.SpinOrbit.Data.LockN65.Pass.FrameL0
public import KAM.SpinOrbit.Data.LockN65.Pass.FrameL1

/-!
# The N = 65 lock: frame majorant L

`checkFrameL` from its two columns (`Pass/FrameL0`, `Pass/FrameL1`, one kernel run each).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_frameL :
    checkFrameL base refinedWit.R.bL = true := by
  unfold checkFrameL
  rewrite [List.all_eq_true]
  intro j _
  fin_cases j
  · exact lock_frameL0
  · exact lock_frameL1

end KAM.SpinOrbit.Data.LockN65
