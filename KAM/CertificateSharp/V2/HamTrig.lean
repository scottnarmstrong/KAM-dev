/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RefinedFacts
public import KAM.CertificateSharp.Ham.SplitBounds

/-!
# The refined bounds on `H`, by the cosh pass

`hamFacts_of_trigSplit` reads `HamFacts` off C3's `checkHamBoundsTrigSplit`. This module cannot be
imported with the frame majorants (see `V2/HamClaim.lean`), so a certificate using the cosh pass
proves `HamFacts` here, in a module of its own, and feeds it to `refinedCore_sound`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- The split bounds of C3 as `HamFacts`. -/
theorem hamFacts_of_trigSplit {c : TorusCertificate n α} {S : HamSplit} {R : RefClaim}
    (hs : checkStatic c = true) (h : checkHamBoundsTrigSplit c S = true) (h1 : S.dh ≤ R.dh)
    (h2 : S.dx ≤ R.dx) (h3 : S.d2x ≤ R.d2x) (h4 : S.d2h ≤ R.d2h) : HamFacts c R := by
  have H := (checkHamBoundsTrigSplit_sound hs h).2
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · exact (H z hz).1.trans (by exact_mod_cast h1)
  · exact (H z hz).2.2.1.trans (by exact_mod_cast h2)
  · exact (H z hz).2.2.2.1.trans (by exact_mod_cast h3)
  · exact (H z hz).2.2.2.2.trans (by exact_mod_cast h4)

end KAM.CertificateSharp.V2

end
