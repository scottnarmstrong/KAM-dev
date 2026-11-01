/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: the energy level `E0`; a missing advice
key of each stage

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- Rejected: the energy level `E0` moved by `2 err` (residual claims). -/
theorem mut_E0 : checkEnergy { cert with params := { cert.params with E0 := cert.params.E0 + 2 *
    cert.params.err } } = false := by
  decide +kernel

/-- Rejected: the first full-stage advice key removed: the crude enclosure of `p²` breaks the energy
row (advice). -/
theorem mut_adviceFull : checkEnergy { cert with cfgFull := { cert.cfgFull with advice :=
    cert.cfgFull.advice.tail } } = false := by
  decide +kernel

/-- Rejected: the first low-stage advice key removed (crude Gram entry) (advice). -/
theorem mut_adviceLow : checkGram { cert with cfgLow := { cert.cfgLow with advice :=
    cert.cfgLow.advice.tail } } = false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
