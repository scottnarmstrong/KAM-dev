/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: a coefficient of the character witness;
the residual claim `err`

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- the witness with its largest coefficient times `1 + 10⁻³` -/
def E1TermsMut : List (CertKey × CC FB) :=
  [ft (-1) (-1) 10139351452291653532324 0, ft (-1) 0 294215801146370861942477 0,
  ft 0 0 79307390675683632578281157694 0, ft 1 0 (-294215801146370861942477) 0,
  ft 1 1 (-10139351452291653532324) 0]

/-- Rejected: the largest coefficient of the character witness times `1 + 10⁻³` (coefficients). -/
theorem mut_witnessCoef : checkInvariance { cert with wit := ⟨[], [], [([1, 0], ⟨⟨E1TermsMut⟩, 0,
    30⟩)], []⟩ } = false := by
  decide +kernel

/-- Rejected: the residual claim `err` halved (residual claims). -/
theorem mut_err : checkInvariance { cert with params := { cert.params with err := cert.params.err /
    2 } } = false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
