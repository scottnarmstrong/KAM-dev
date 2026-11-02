/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.HamClaim

/-!
# The Hamiltonian checks depend only on the Hamiltonian and its domain

`checkHamBounds` and the disc pass `checkHamClaim` read a certificate only through its Hamiltonian,
the weight and centre and radius of its domain, its exponential order (and, for the bounds,
`params.M`). So two certificates that agree on these fields pass them together: a copy of a
certificate that drops data these checks do not read (the packed route's copy has no advice and no
witnesses) inherits them from the original's proofs instead of re-proving them.

* `checkHamBounds_congr`, `checkHamClaim_congr`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.CertificateSharp.V2

variable {n : ℕ} {α : Type} [CertArith α]

/-- `checkHamBounds` reads only the Hamiltonian, the domain, the order and `M`. -/
theorem checkHamBounds_congr {c c' : TorusCertificate n α} (hham : c.ham = c'.ham)
    (hw : c.weightH = c'.weightH) (hce : c.centre = c'.centre) (hr : c.radius = c'.radius)
    (he : c.expOrder = c'.expOrder) (hM : c.params.M = c'.params.M) :
    checkHamBounds c = checkHamBounds c' := by
  unfold checkHamBounds
  rw [hham, hw, hce, hr, he, hM]

omit [CertArith α] in
/-- The disc pass reads only the Hamiltonian, the domain and the order. -/
theorem checkHamClaim_congr {c c' : TorusCertificate n α} {R R' : RefClaim}
    (hham : c.ham = c'.ham) (hw : c.weightH = c'.weightH) (hce : c.centre = c'.centre)
    (hr : c.radius = c'.radius) (he : c.expOrder = c'.expOrder) (hR : R = R') :
    checkHamClaim c R = checkHamClaim c' R' := by
  unfold checkHamClaim
  rw [hham, hw, hce, hr, he, hR]

end KAM.CertificateSharp.Packed

end
