/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: ray room and schedules on the route
cores: `disp = 1`, `θ = 1`, `10 X⋆`, route B `a = 1`

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- Rejected: `disp = 1`, above the room `(σω - s)|ω*|` of the ray: the final clause of route A
rejects (ray room). -/
theorem mut_dispRoom : finalOkA (refinedWit.num 2 { cert.params with disp := 1 } cert.freqBox)
    { cert.params with disp := 1 } cert.freqBox refinedWit.core.Xs = false := by
  decide +kernel

/-- Rejected: route A with `θ = 1` (schedules). -/
theorem mut_theta : refinedCore 2 cert.params cert.freqBox { refinedWit with core := {
    refinedWit.core with th := 1 } } = false := by
  decide +kernel

/-- Rejected: route A with ten times the passing `X⋆` (schedules). -/
theorem mut_Xs : refinedCore 2 cert.params cert.freqBox { refinedWit with core := { refinedWit.core
    with Xs := refinedWit.core.Xs * 10 } } = false := by
  decide +kernel

/-- Rejected: route B with the schedule ratio `a = 1` (schedules). -/
theorem mut_scheduleB : refinedBCore 2 cert.params cert.freqBox { refinedBWit with core := {
    refinedBWit.core with a := 1 } } = false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
