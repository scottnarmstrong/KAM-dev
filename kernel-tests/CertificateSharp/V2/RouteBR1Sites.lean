/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.RefinedR1
public import KAM.CertificateSharp.V2.Tests.RouteBR1

/-!
# The prefix sites of route B on the design package R1 (opt-in, not part of the library)

Not built by anything, and **not runnable on lemma.farm as it stands**: it imports
`KAM.CertificateSharp.V2.Tests.RefinedR1` (`RefinedR1.lean` here, 10.4 GB to build) and
`KAM.CertificateSharp.V2.Tests.RouteBR1` (`RouteBR1.lean` here). This file re-checks no bite: at
`a = 2` the bites `δ_s` and the full bites `min r_s 1` of route B are those of route A, and the
split bite `δ_s/2` is `δ_{s+1}`, so the kernel checks `r1_site_*` of SHARP2-C6 serve, through
rational equalities of the bites. With them, `r1B_refinedCore` is `refinedBCore` on R1 at
`e = 2.6·10⁻¹³`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

theorem r1B_site_d0 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.δ 0)
    (r1BQ.c.getD 0 r1BQ.ctail) (r1BWit.sites.getD 0 (none, none, none)).1 = true := by
  rw [show r1BQ.δ 0 = r1Q.δ 0 by decide +kernel]; exact r1_site_d0

theorem r1B_site_d1 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.δ 1)
    (r1BQ.c.getD 1 r1BQ.ctail) (r1BWit.sites.getD 1 (none, none, none)).1 = true := by
  rw [show r1BQ.δ 1 = r1Q.δ 1 by decide +kernel]; exact r1_site_d1

theorem r1B_site_d2 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.δ 2)
    (r1BQ.c.getD 2 r1BQ.ctail) (r1BWit.sites.getD 2 (none, none, none)).1 = true := by
  rw [show r1BQ.δ 2 = r1Q.δ 2 by decide +kernel]; exact r1_site_d2

theorem r1B_site_s0 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.split * r1BQ.δ 0)
    (r1BQ.c'.getD 0 r1BQ.ctail) (r1BWit.sites.getD 0 (none, none, none)).2.1 = true := by
  rw [show r1BQ.split * r1BQ.δ 0 = r1Q.δ 1 by decide +kernel]; exact r1_site_d1

theorem r1B_site_s1 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.split * r1BQ.δ 1)
    (r1BQ.c'.getD 1 r1BQ.ctail) (r1BWit.sites.getD 1 (none, none, none)).2.1 = true := by
  rw [show r1BQ.split * r1BQ.δ 1 = r1Q.δ 2 by decide +kernel]; exact r1_site_d2

theorem r1B_site_b0 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.bfull 0)
    (r1BQ.cbar.getD 0 r1BQ.cbtail) (r1BWit.sites.getD 0 (none, none, none)).2.2 = true := by
  rw [show r1BQ.bfull 0 = r1Q.b 0 by decide +kernel]; exact r1_site_b0

theorem r1B_site_b1 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.bfull 1)
    (r1BQ.cbar.getD 1 r1BQ.cbtail) (r1BWit.sites.getD 1 (none, none, none)).2.2 = true := by
  rw [show r1BQ.bfull 1 = r1Q.b 1 by decide +kernel]; exact r1_site_b1

theorem r1B_site_b2 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.bfull 2)
    (r1BQ.cbar.getD 2 r1BQ.cbtail) (r1BWit.sites.getD 2 (none, none, none)).2.2 = true := by
  rw [show r1BQ.bfull 2 = r1Q.b 2 by decide +kernel]; exact r1_site_b2

theorem r1B_sites : r1BQ.sitesOk 2 4 r1Box r1Kappa r1PassB.γ r1BWit.sites = true :=
  NumBQ.sitesOk_of fun s hs => by
    have hk : s < 3 := hs
    interval_cases s
    · exact ⟨r1B_site_d0, r1B_site_s0, r1B_site_b0⟩
    · exact ⟨r1B_site_d1, r1B_site_s1, r1B_site_b1⟩
    · exact ⟨r1B_site_d2, r1B_site_s2, r1B_site_b2⟩

/-- **`refinedBCore` on R1**, at `e = 2.6·10⁻¹³`. -/
theorem r1B_refinedCore : refinedBCore 2 r1PassB r1Box r1BWit = true :=
  r1B_refinedCore_of_sites r1B_sites

end KAM.CertificateSharp.V2

end
