/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteBG
public import KAM.CertificateSharp.V2.Tests.RouteBToy

/-!
# Route B with general sites, on the toy B

Route B asks `ρ ≤ 1`, so the three-frequency toy T3 (`ρ = 9`) does not exercise it. The toy B of
`V2/Tests/RouteBToy.lean` (`n = 2`, lunar bites) passes `routeBRefinedG` through the image of its
refined witness (`checkTorusCertificateV2_routeBRefinedG_ofRefined`, no recomputation), and the
soundness theorem of the new engine gives its torus.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

theorem toyB_refinedBG_passes :
    checkTorusCertificateV2 routeBRefinedG toyB (RefinedBWitG.ofRefined toyRefinedBWit) = true := by
  rw [checkTorusCertificateV2_routeBRefinedG_ofRefined]
  exact toyB_refinedB_passes

theorem toyB_refinedBG_torus : CertifiedTorus toyB ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeBRefinedG toyB_refinedBG_passes toyB_freq toyB_dio

end KAM.CertificateSharp.V2

end
