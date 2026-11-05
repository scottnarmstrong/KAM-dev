/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: a square-root operand reaching `Re ≤ 0`,
and its separated control

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- Rejected: a term `10⁻⁹ √(p - p_c)` whose operand reaches `Re ≤ 0` on the domain (square-root
domains). -/
theorem mut_sqrtDomain : checkHamBounds { cert with ham := .add ham (.mul (.const (1 / 10 ^ 9))
    (.sqrt (.add (.action 0) (.const (63791325795 / 549755813888))))) } = false := by
  decide +kernel

/-- Control: the same term with the operand `p + 1` passes. -/
theorem ctl_sqrtDomain : checkHamBounds { cert with ham := .add ham (.mul (.const (1 / 10 ^ 9))
    (.sqrt (.add (.action 0) (.const 1)))) } = true := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
