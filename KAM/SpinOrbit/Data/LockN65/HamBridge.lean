/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs
public import KAM.CertificateSharp.V2.HamClaim

/-!
# The disc pass from its pieces

`checkHamBounds` and `checkHamClaim` from three separately checked facts: the jet of the
Hamiltonian, the ball pass of its program, and the bounds over those balls. Stated over an abstract
certificate, so instantiating them evaluates nothing.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 CertArith

variable {n : ℕ} {α : Type} [CertArith α]

/-- `checkHamBounds` from the jet, the ball pass and `hamBoundsOk`. -/
theorem checkHamBounds_of_parts (c : TorusCertificate n α) {J : HamJet} {bs : List (CC ℚ × ℚ)}
    (hJ : c.ham.jet = J)
    (hb : J.prog.balls n c.weightH c.centre c.radius c.expOrder = some bs)
    (h : hamBoundsOk (n + n) J bs c.params.M = true) : checkHamBounds c = true := by
  unfold checkHamBounds
  rw [hJ, hb]
  exact h

/-- `checkHamClaim` from the jet, the ball pass and `hamClaimOk`. -/
theorem checkHamClaim_of_parts (c : TorusCertificate n α) (R : RefClaim) {J : HamJet}
    {bs : List (CC ℚ × ℚ)} (hJ : c.ham.jet = J)
    (hb : J.prog.balls n c.weightH c.centre c.radius c.expOrder = some bs)
    (h : hamClaimOk (n + n) J bs R = true) : checkHamClaim c R = true := by
  unfold checkHamClaim
  rw [hJ, hb]
  exact h

end KAM.SpinOrbit.Data.LockN65
