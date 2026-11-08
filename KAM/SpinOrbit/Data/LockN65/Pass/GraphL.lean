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
public import KAM.SpinOrbit.Data.LockN65.RealLowerKSq
public import KAM.SpinOrbit.Data.LockN65.GraphK.A
public import KAM.SpinOrbit.Data.LockN65.GraphK.LGG
public import KAM.SpinOrbit.Data.LockN65.GraphK.LG
public import KAM.SpinOrbit.Data.LockN65.GraphK.LHc
public import KAM.SpinOrbit.Data.LockN65.GraphK.OutL
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2016
public import KAM.SpinOrbit.Data.LockN65.SegSupport

/-!
# The N = 65 lock: graph pLo SOS (key [7, 1], packed square)

The pLo check with its SOS square `g g*` under its own key `[7, 1]` (`checkRealLowerBoundK`,
SOS option (a)) by `checkRealLowerBoundK_of_parts`: the square is the memoized packed product
`lockM2016`; the square's model, the scaled square and the action model are proved in `GraphK/`, and
the bound by key-range chunks (`GraphK/LHc`, GraphChunk.lean): no kernel run over the whole
~26k-term model.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open SoGraph
open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

/-- The square `g g*` of the pLo check: the cfgLow product under `[7, 1]`
(memoized packed: `lockM2016`; the appended `.direct` entry is never reached: the key has its
advice in the cfgLow book). -/
theorem lock_graphLSq :
    CertModel.polyProduct cert.graph.base.weight
      { cert.graph.base.cfgLow with
        advice := cert.graph.base.cfgLow.advice ++ [([7, 1], ProductAdvice.direct)] }
      [7, 1] cert.graph.sosLo cert.graph.sosLo.conjSorted =
      CertModel.polyProduct base.weight base.cfgLow [7, 1] sosLoPoly sosLoPoly.conjSorted :=
  polyProduct_append_of_isSome _ _ _ _ _ _ (by decide +kernel)

theorem lock_graphL :
    checkRealLowerBoundK cert.graph.base.weight cert.graph.base.cfgLow [7, 1]
      (soGraphActionModel cert.graph) cert.graph.pLo₀ cert.graph.pLo cert.graph.sosLo = true :=
  checkRealLowerBoundK_of_parts (lock_graphLSq.trans lock_gkLOut) lock_gkLGG lock_gkLG
    lock_gkA rfl lock_gkLHc

end KAM.SpinOrbit.Data.LockN65
