/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: conventions: the angle degree of `u`,
the ray scalar `s`

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- Rejected: `u = 2πU` read at angle degree `0` (as `U`) (conventions). -/
theorem mut_angleDeg : checkInvariance { cert with emb := ⟨[0, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [p, J]⟩
    } = false := by
  decide +kernel

/-- Rejected: the ray scalar `s = 1 + 10⁻³` against the box of `c / s` (conventions). -/
theorem mut_rayScalar : checkInvariance { cert with params := { cert.params with s := 1001 / 1000 }
    } = false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
