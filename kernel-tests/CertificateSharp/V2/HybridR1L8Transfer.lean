/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.RestartQ
public import KAM.CertificateSharp.V2.Tests.Frozen
public import KAM.CertificateSharp.V2.Tests.HybridR1L8Data

/-!
# The hybrid test on R1's L = 8 candidate: the transfer checks H0–H4 (package C8c)

**Not built** (`kernel-tests/` is outside the library). It imports
`KAM.CertificateSharp.V2.Tests.HybridR1L8Data` (C8d, generated from
`docs/campaign/design/hybrid/hybrid-R1-L8.json`) by module path: place `HybridR1L8Data.lean` back
under `KAM/CertificateSharp/V2/Tests/` to compile, as `kernel-tests/README.md` says.

`r1Hyb_transfer` is C8c's `transferOk` (format v1 §5, H0–H4) on the producer's data: the base
parameters (design package R1 at the file's `err`, `disp`), the base claim (`r1Claim` of
`RefinedR1`, written out here so as not to import that 10 GB module), the step claims
`r1HybClaims`, `r1HybParams1` and the transferred claim `r1HybClaim`. Check H5 is C8d's
`HybridR1L8Core`.

Not covered: the step checks `hybStepOk` (`(S1)–(S7)` on `r1HybStep`, `ℓ_H`, `d_ω`) need R1's
`TorusCertificate` (Hamiltonian expression, model configurations, the witnesses), which is not yet
in Lean (format.md §7, open item). The producer's three weights `step.weights` fail `checkWeight`
at the toy's `expHalvings = 8`, `expOrder = 24` (they sit below `ratExpUp (2 piUpQ ρ)`); they must
be rounded up to the certifier's bound before the step checks can run.

Kernel cost (measured on a copy with the data inlined, one niced process): `r1Hyb_transfer` under
3 s, peak RSS 1.87 GB (the imports).
-/

@[expose] public section

namespace KAM.CertificateSharp.HybridR1Test

open KAM.Certificate KAM.CertificateSharp.V2 KAM.CertificateSharp.Hybrid

/-- The base claim of `hybrid-R1-L8.json` (`base.claim`; `r1Claim` of `RefinedR1`). -/
def r1BaseClaim : RefClaim where
  dh := 95697 / 50000
  dx := 147 / 80
  d2x := 108591 / 100000
  d2h := 384783 / 200000
  bL := 69657 / 50000
  bN := 14217 / 10000
  bNt := 289527 / 200000
  bT := 69573 / 20000

/-- The base parameters of `hybrid-R1-L8.json` (`base.params`). -/
def r1BaseParams : CertParams := r1Params (4319408739771 / 10 ^ 18) (80535055907 / (5 * 10 ^ 17))

/-- The step claims `(S1)–(S7)`, from `r1HybClaims`. -/
def r1HybCl : StepNumQ :=
  ⟨r1HybClaims.getD 0 0, r1HybClaims.getD 1 0, r1HybClaims.getD 2 0, r1HybClaims.getD 3 0,
    r1HybClaims.getD 4 0, r1HybClaims.getD 5 0, r1HybClaims.getD 6 0, r1HybClaims.getD 7 0,
    r1HybClaims.getD 8 0, r1HybClaims.getD 9 0, r1HybClaims.getD 10 0, r1HybClaims.getD 11 0,
    r1HybClaims.getD 12 0, r1HybClaims.getD 13 0⟩

/-- The step of `hybrid-R1-L8.json` (the weights as the producer gives them). -/
def r1HybStepH : HybStep where
  dK := r1HybStep
  s1 := r1HybParams1.s
  W1 := ⟨1 / 70, 546955746057597 / 500000000000000⟩
  Winf := ⟨1 / 70000, 62505610239141 / 62500000000000⟩
  WT := ⟨1667 / 140000, 538842267979699 / 500000000000000⟩
  cl := r1HybCl
  lH := r1HybClaims.getD 14 0
  dw := r1HybClaims.getD 15 0

/-- The hybrid witness of R1, for given sites of the restarted run (`witness1` is C8d's
`r1HybWitR sites`). -/
def r1HybWitH (sites : List (Option BiteWit × Option BiteWit)) : HybWit where
  R0 := r1BaseClaim
  step := r1HybStepH
  p1 := r1HybParams1
  w1 := { base := { core := r1HybCore, R := r1HybClaim, κ := r1Kappa, sites := sites }
          bF := 1177 / 5000000, bT := 99089 / 1250000 }

/-- **H0–H4 on R1.** -/
theorem r1Hyb_transfer : transferOk 2 r1BaseParams r1Box (r1HybWitH []) = true := by
  decide +kernel

end KAM.CertificateSharp.HybridR1Test

end
