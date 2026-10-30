/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Tests.RatData

/-!
# The checker-only toy TR (SO design §8)

`H = J + p²/2`, the exact rational `ν = 1/2`, `K(θ) = (θ, (1/2, -1/8))`, zero error, reference
box `{(1/4, 1/2)}`. No Diophantine premise exists (the vector `(1/4, 1/2)` is resonant), so this
toy exercises the checker only: `toyRatCert_passes` (`decide +kernel`) and no `*_torus`.
-/

@[expose] public section

namespace KAM.Certificate

/-- Checker-only toy TR (data in `Tests/RatData`). -/
def toyRatCert : TorusCertificate 2 ℚ := toyTRCert

theorem toyRatCert_passes : checkTorusCertificate toyRatCert = true := by decide +kernel

end KAM.Certificate
