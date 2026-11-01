/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: coefficients: a forcing amplitude and a
Fourier coefficient of the torus

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- `ham` with the amplitude of `[1, 0]` times `1 + 10⁻³`. -/
def hamCoef : HamExpr 2 :=
  (.mul (.const (1)) (.add (.action 1) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2)) (.add
    (.mul (.const (1001 / 10000000000)) (.cosMode [1, 0])) (.add (.mul (.const (1 / 5000000))
    (.cosMode [1, 1])) (.const (0)))))))

/-- Rejected: the amplitude of the mode `[1, 0]` times `1 + 10⁻³` (coefficients). -/
theorem mut_hamCoef : checkInvariance { cert with ham := hamCoef } = false := by
  decide +kernel

/-- `uHalf` with its largest coefficient times `1 + 10⁻⁴` -/
def uHalfMut : List (CertKey × CC FB) :=
  [ft 0 1 0 28914612542022504, ft 1 0 0 294245222726485499028671, ft 1 1 0 10139351452291653532324,
  ft 2 0 0 (-273144469394377101), ft 2 1 0 (-50750936587771487)]

/-- Rejected: the largest Fourier coefficient of `u` times `1 + 10⁻⁴` (coefficients). -/
theorem mut_torusCoef : checkInvariance { cert with emb := ⟨[-1, 0], [⟨⟨0⟩, uHalfMut⟩, ⟨⟨0⟩, []⟩],
    [0, 0], [p, J]⟩ } = false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
