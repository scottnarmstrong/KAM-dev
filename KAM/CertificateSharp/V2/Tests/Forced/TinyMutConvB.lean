/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: conventions: the time scale of `H`, the
order of the actions

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- Rejected: the Hamiltonian doubled without rescaling the box (conventions). -/
theorem mut_timeScale : checkInvariance { cert with ham := .mul (.const 2) ham } = false := by
  decide +kernel

/-- Rejected: the actions `(p, J)` emitted in the order `(J, p)` (conventions). -/
theorem mut_swapActions : checkInvariance { cert with emb := ⟨[-1, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [J,
    p]⟩ } = false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
