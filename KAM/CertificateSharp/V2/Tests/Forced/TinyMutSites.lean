/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: small-divisor separation: a box reaching
the resonance fibers, a site bound halved

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The box with radius `1/20` in coordinate 0. -/
def boxWide : FreqBox :=
  [((cert.freqBox.getD 0 (0, 0)).1, 1 / 20), cert.freqBox.getD 1 (0, 0)]

/-- Rejected: the frequency box widened to radius `1/20`: the fibers reach the resonance, the sites
fail (denominator separation). -/
theorem mut_boxFiber : sitesOk (refinedWit.num 2 cert.params boxWide) refinedWit.core.J boxWide
    refinedWit.κ cert.params.γ refinedWit.sites = false := by
  decide +kernel

/-- Rejected: the first site with its bound `B` halved (denominator separation). -/
theorem mut_siteBound : siteOk 2 1 refinedWit.core.J cert.freqBox refinedWit.κ cert.params.γ
    ((refinedWit.num 2 cert.params cert.freqBox).δ 0) (refinedWit.core.c.getD 0 0) (some ⟨(773227 /
    1000000), 6, 8, (4522 / 25)⟩) = false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
