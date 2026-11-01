/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.Tests.Forced.TinyGram

/-!
# Mutations of the forced toy `Tiny` that must be rejected: frame bounds and ray room: `bL`, `bN`
below the measured rows, the claim `dx`, `nuRay`

Each theorem changes one input of the passing certificate or witness and decides the single
check that must reject it (`scripts/certifier/forced/forced_mutations.py`, the mirror verdicts in
`scripts/certifier/fixtures/forced-toy/Tiny_mutations.json`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- Rejected: the frame bound `bL` times `0.99` (frame bounds). -/
theorem mut_frameL : checkFrameL cert (Rclaim.bL * 99 / 100) = false := by
  decide +kernel

/-- Rejected: the frame bound `bN` times `0.99` (frame bounds). -/
theorem mut_frameN : checkFrameN cert (Rclaim.bN * 99 / 100) Rclaim.bNt = false := by
  rw [checkFrameN_eq_of gram_eq eps_eq (frameNModels_eq_of_stage 2 cert.emb cert.gramInv eps
    cert.weight cert.cfgLow cert.piEnc L_eq Gi_eq N0_eq)]
  decide +kernel

/-- Rejected: the Hamiltonian claim `dx` times `0.99` (frame bounds). -/
theorem mut_hamClaim : checkHamClaim cert { Rclaim with dx := Rclaim.dx * 99 / 100 } = false := by
  decide +kernel

/-- Rejected: `nuRay = 10⁻⁵`, above `(s - 1)|ω*| ≈ 10⁻⁶` (ray room). -/
theorem mut_nuRay : checkStatic { cert with params := { cert.params with nuRay := 1 / 10 ^ 5 } } =
    false := by
  decide +kernel

end KAM.CertificateSharp.V2.Forced.Tiny

end
