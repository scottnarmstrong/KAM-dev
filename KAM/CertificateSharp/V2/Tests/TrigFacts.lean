/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RefinedFacts
public import KAM.Certificate.Tests.Toy2
import KAM.CertificateSharp.V2.HamTrig

/-!
# The cosh pass of C3 on the toy T2, behind a private import

`HamFacts` by `hamFacts_of_trigSplit`. The import of `V2/HamTrig.lean` is private: the statement
exported here mentions only `V2/RefinedFacts.lean`, so `Tests/TrigCombined.lean` can use it next to
the frame majorants, whose import closure clashes with the one of the cosh pass on `expLoQ`.
-/

public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The claim of the cosh test. -/
@[expose] def toyTrigClaim : RefClaim :=
  { dh := 2, dx := 101 / 100, d2x := 1 / 100, d2h := 101 / 100
    bL := 101 / 100, bN := 101 / 100, bNt := 101 / 100, bT := 101 / 100 }

/-- The split bounds of T2, by the cosh pass. -/
theorem toyCert2_hamFacts_trig : HamFacts toyCert2 toyTrigClaim := by
  have hs : checkStatic toyCert2 = true := by decide +kernel
  have h : checkHamBoundsTrigSplit toyCert2 ⟨2, 2, 101 / 100, 1 / 100, 101 / 100⟩ = true := by
    decide +kernel
  exact hamFacts_of_trigSplit hs h le_rfl le_rfl le_rfl le_rfl

end KAM.CertificateSharp.V2

end
