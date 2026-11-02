/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetConsLift

/-!
# The v2 certifier on the packed route with lifted constants, from its two parts

`checkV2With_jetBaseLPackedJL_of`: the certifier with `jetBaseL` and `routeARefinedPackedJL` passes
when the base check and the engine's test do. Stated for any certificate, so that a generated
assembly cites its two parts without unfolding the certificate's data.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.CertificateSharp.V2

/-- **The certifier from its parts.** -/
theorem checkV2With_jetBaseLPackedJL_of {n : ℕ} {α : Type} [CertArith α] {bk : PGramBook}
    {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jl : JetData} {ib : PIBook}
    {jf : JetData} {c : TorusCertificate n α} {w : RefinedWit}
    (hb : (jetBaseL bk mm rb tm rm jl ib jf).check c = true)
    (he : refinedTestPackedJL bk mm rb tm rm jl c w = true) :
    checkV2With (jetBaseL bk mm rb tm rm jl ib jf) (routeARefinedPackedJL bk mm rb tm rm jl) c w =
      true := by
  simp only [checkV2With, hb, Bool.true_and]
  exact he

end KAM.CertificateSharp.Packed
