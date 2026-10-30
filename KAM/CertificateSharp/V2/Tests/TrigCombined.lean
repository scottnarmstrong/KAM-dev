/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.FrameFacts
public import KAM.CertificateSharp.V2.RouteARefined

/-!
# The cosh pass and the frame majorants together

`Corner.SupBound` and `Ham.TrigBound` both define `KAM.CertificateSharp.expLoQ`, so no module can
import both closures. This module combines their results all the same: each side is proved in a
module that imports its checks privately (`Tests/TrigFacts.lean`, `Tests/FrameFacts.lean`), and
`refinedCore_sound` reads only `HamFacts`, `FrameFacts`. `toyCert2_cosh_torus` is the pattern for a
certificate that wants C3's cosh bounds at stage 2.
-/

public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The refined witness of T2 with the claim of `Tests/TrigFacts.lean`. -/
@[expose] def toyTrigWit : RefinedWit where
  core :=
    { Xs := 1 / 10 ^ 30
      kp := 2
      th := 1 / 8
      c := [1 / 5000, 3 / 500]
      cbar := [1 / 5000, 1 / 5000]
      ctail := 111 / 1000
      sB := 3
      sT := 3
      sLt := 11 / 10
      sN := 11 / 10
      sNt := 11 / 10
      t := 11 / 10
      J := 2 }
  R := toyTrigClaim
  κ := 1 / 2
  sites :=
    [(some ⟨1 / 100000, 3, 16, 12 / 100000⟩, some ⟨1 / 100000, 3, 16, 12 / 100000⟩),
     (some ⟨1 / 100, 3, 12, 45 / 100⟩, some ⟨1 / 100000, 3, 16, 12 / 100000⟩)]

theorem toyCert2_trig_core :
    refinedCore 2 toyCert2.params toyCert2.freqBox toyTrigWit = true := by decide +kernel

/-- **The toy torus, with the cosh pass and the frame majorants.** -/
theorem toyCert2_cosh_torus {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 toyCert2.freqBox ωstar)
    (hdio : IsDiophantine (toyCert2.params.γ : ℝ) (toyCert2.params.tau : ℝ) ωstar)
    (B : BaseFacts toyCert2 ωstar) : CertifiedTorus toyCert2 ωstar :=
  refinedCore_sound toyCert2 toyTrigWit hω hdio B toyCert2_hamFacts_trig
    (toyCert2_frameFacts hω B) toyCert2_trig_core

end KAM.CertificateSharp.V2

end
