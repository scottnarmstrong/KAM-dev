/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Claims
public import KAM.CertificateSharp.Hybrid.RestartQ
public import KAM.CertificateSharp.V2.Tests.Frozen
public import KAM.CertificateSharp.V2.Tests.HybridR1L8Data

/-!
# The hybrid test on R1's L = 8 candidate with the aligned data (package C8dfix)

**Not built** (`kernel-tests/` is outside the library). It imports
`KAM.CertificateSharp.V2.Tests.HybridR1L8Data` by module path: place `HybridR1L8Data.lean` back
under `KAM/CertificateSharp/V2/Tests/` to compile, as `kernel-tests/README.md` says.

The data are `docs/campaign/design/hybrid/hybrid-R1-L8.json`, format v2 (SHARP2-C8DFIX): the
weights pass `checkWeight` at `(8, 24)` and at `(12, 30)`, the polynomial claims are the checker's
own sup bounds at the worst-case `π` enclosure, `dE0 = dE0R` is the Cauchy bound of `hybCauchyOk`,
and the restart numbers come from the exact port of `TransferQ`. Every number is read from the
generated data module (`r1HybBaseParams`, `r1HybBaseClaim`, `r1HybW1`, `r1HybWinf`, `r1HybWT`,
`r1HybClaims`, `r1HybParams1`, `r1HybCore`, `r1HybClaim`), so a regeneration cannot leave stale
copies here.

* `r1HybA_transfer`: the transfer checks H0–H4 (`transferOk`).
* `r1HybA_poly`: `hybPolyOk`, the step claims `(S1)–(S4)` on the nonzero step `r1HybStep`. It reads
  only the Machin parameters of the `π` enclosure; `r1HybPi` gives the toy's `(4, 4)` (the claims
  hold for any parameters: they are computed at `(0, 0)`).

Not covered: `hybWeightsOk`, `hybCauchyOk`, the `d_ω` check, `hybOmegaOk` and `hybCompOk` read R1's
`TorusCertificate`, which is not in Lean (format.md §7). The first three are cross-checked against
the Lean definitions by `scripts/apost_sharp/hybrid_xlang.py` (`#eval` on a certificate stub).

This file supersedes the hard-coded copies in `HybridR1L8Transfer.lean` (C8c): its `r1BaseParams`
and weights are those of the format-v1 file, and with the regenerated data module its
`r1Hyb_transfer` fails at `disp` (`max dinf dω + disp₁ = 1.6143·10⁻⁷` against `1.6107·10⁻⁷`).

Kernel cost (one niced process, measured on copies with the data inlined): see the handoff
`docs/campaign/handoffs/SHARP2-C8DFIX.md`.
-/

@[expose] public section

namespace KAM.CertificateSharp.HybridR1Test

open KAM.Certificate KAM.CertificateSharp.V2 KAM.CertificateSharp.Hybrid

/-- The step claims `(S1)–(S7)`, from `r1HybClaims`. -/
def r1HybClA : StepNumQ :=
  ⟨r1HybClaims.getD 0 0, r1HybClaims.getD 1 0, r1HybClaims.getD 2 0, r1HybClaims.getD 3 0,
    r1HybClaims.getD 4 0, r1HybClaims.getD 5 0, r1HybClaims.getD 6 0, r1HybClaims.getD 7 0,
    r1HybClaims.getD 8 0, r1HybClaims.getD 9 0, r1HybClaims.getD 10 0, r1HybClaims.getD 11 0,
    r1HybClaims.getD 12 0, r1HybClaims.getD 13 0⟩

/-- The step of `hybrid-R1-L8.json`. -/
def r1HybStepA : HybStep where
  dK := r1HybStep
  s1 := r1HybParams1.s
  W1 := r1HybW1
  Winf := r1HybWinf
  WT := r1HybWT
  cl := r1HybClA
  lH := r1HybClaims.getD 14 0
  dw := r1HybClaims.getD 15 0

/-- The hybrid witness of R1, for given sites of the restarted run. -/
def r1HybWitA (sites : List (Option BiteWit × Option BiteWit)) : HybWit where
  R0 := r1HybBaseClaim
  step := r1HybStepA
  p1 := r1HybParams1
  w1 := { base := { core := r1HybCore, R := r1HybClaim, κ := r1Kappa, sites := sites }
          bF := 1177 / 5000000, bT := 99089 / 1250000 }

/-- **H0–H4 on R1**, at the generated base parameters. -/
theorem r1HybA_transfer : transferOk 2 r1HybBaseParams r1Box (r1HybWitA []) = true := by
  decide +kernel

/-- A `π` enclosure with the toy's Machin parameters (`hybPolyOk` reads only those). -/
def r1HybPi : PiEnclosure ℚ := ⟨3141592653589793 / 10 ^ 15, 1 / 10 ^ 14, 4, 4⟩

/-- **`(S1)–(S4)` on the nonzero step of R1.** -/
theorem r1HybA_poly : hybPolyOk (n := 2) r1HybStepA r1HybPi = true := by
  decide +kernel

end KAM.CertificateSharp.HybridR1Test

end
