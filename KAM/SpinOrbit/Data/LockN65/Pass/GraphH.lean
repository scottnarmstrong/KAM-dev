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
public import KAM.SpinOrbit.Data.LockN65.GraphK.HGG
public import KAM.SpinOrbit.Data.LockN65.GraphK.HG
public import KAM.SpinOrbit.Data.LockN65.GraphK.HHc
public import KAM.SpinOrbit.Data.LockN65.GraphK.OutH
public import KAM.SpinOrbit.Data.LockN65.Seg.Prod.M2017
public import KAM.SpinOrbit.Data.LockN65.SegSupport

/-!
# The N = 65 lock: graph pHi SOS (key [7, 2], packed square)

The pHi check with its SOS square `g g*` under its own key `[7, 2]` (`checkRealLowerBoundK`,
SOS option (a)) by `checkRealLowerBoundK_of_parts`: the square is the memoized packed product
`lockM2017`; the square's model, the scaled square and the action model are proved in `GraphK/`, and
the bound by key-range chunks (`GraphK/HHc`, GraphChunk.lean): no kernel run over the whole
~26k-term model.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open SoGraph
open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 KAM.SpinOrbit CertArith

/-- The square `g g*` of the pHi check: the cfgLow product under `[7, 2]`
(memoized packed: `lockM2017`; the appended `.direct` entry is never reached: the key has its
advice in the cfgLow book). -/
theorem lock_graphHSq :
    CertModel.polyProduct cert.graph.base.weight
      { cert.graph.base.cfgLow with
        advice := cert.graph.base.cfgLow.advice ++ [([7, 2], ProductAdvice.direct)] }
      [7, 2] cert.graph.sosHi cert.graph.sosHi.conjSorted =
      CertModel.polyProduct base.weight base.cfgLow [7, 2] sosHiPoly sosHiPoly.conjSorted :=
  polyProduct_append_of_isSome _ _ _ _ _ _ (by decide +kernel)

theorem lock_graphH :
    checkRealLowerBoundK cert.graph.base.weight cert.graph.base.cfgLow [7, 2]
      (soGraphActionModel cert.graph).negM (-cert.graph.pHi₀) (-cert.graph.pHi)
      cert.graph.sosHi = true :=
  checkRealLowerBoundK_of_parts (lock_graphHSq.trans lock_gkHOut) lock_gkHGG lock_gkHG
    (congrArg CertModel.negM lock_gkA) rfl lock_gkHHc

end KAM.SpinOrbit.Data.LockN65
