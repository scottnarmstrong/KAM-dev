/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyRouteA

/-!
# Mutations of the forced toy `Tiny` that must be rejected (composition)

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it, alone in the kernel. The families and the producer's mirror verdicts
are listed in `scripts/certifier/forced/forced_mutations.py` and
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

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

/-- Rejected: `u = 2πU` read at angle degree `0` (as `U`) (conventions). -/
theorem mut_angleDeg : checkInvariance { cert with emb := ⟨[0, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [p, J]⟩
    } = false := by
  decide +kernel

/-- Rejected: the ray scalar `s = 1 + 10⁻³` against the box of `c / s` (conventions). -/
theorem mut_rayScalar : checkInvariance { cert with params := { cert.params with s := 1001 / 1000 }
    } = false := by
  decide +kernel

/-- Rejected: the Hamiltonian doubled without rescaling the box (conventions). -/
theorem mut_timeScale : checkInvariance { cert with ham := .mul (.const 2) ham } = false := by
  decide +kernel

/-- Rejected: the actions `(p, J)` emitted in the order `(J, p)` (conventions). -/
theorem mut_swapActions : checkInvariance { cert with emb := ⟨[-1, 0], [u, ⟨⟨0⟩, []⟩], [0, 0], [J,
    p]⟩ } = false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
