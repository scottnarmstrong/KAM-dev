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
# The N = 65 lock: graph lower SOS (monolithic)

One kernel run (`decide +kernel`), as for the band data in
`KAM/SpinOrbit/Data/Upper/Pass/GraphL.lean`.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open SoGraph
open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

theorem lock_graphL :
    checkRealLowerBound cert.graph.base.weight cert.graph.base.cfgLow
      (soGraphActionModel cert.graph)
      cert.graph.pLo₀ cert.graph.pLo cert.graph.sosLo = true := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
