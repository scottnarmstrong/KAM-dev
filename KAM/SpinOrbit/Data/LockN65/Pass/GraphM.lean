/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.Cert
public import KAM.SpinOrbit.Data.LockN65.Witness
public import KAM.SpinOrbit.LunarAssemblyV2
public import KAM.SpinOrbit.Data.LockN65.GraphK

/-!
# The N = 65 lock: graph mono SOS (key [7, 0])

One kernel run (`decide +kernel`): the mono SOS square has no advice under its key `[7, 0]`, so it
is formed by the direct product (as before, under `[7]`).
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open SoGraph
open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_graphM :
    checkRealLowerBoundK cert.graph.base.weight cert.graph.base.cfgLow [7, 0]
      (soGraphMonoModel cert.graph) cert.graph.mono₀ cert.graph.mono cert.graph.sosMono = true := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
