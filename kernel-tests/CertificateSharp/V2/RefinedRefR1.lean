/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefinedRef
public import KAM.CertificateSharp.V2.Tests.RefinedR1

/-!
# The numerical part of stage 2 with lever L8′ on the design package R1, in the kernel

`refinedCoreR` passes at `e = 1.55·10⁻¹¹`, that is `10^(-10.81)`, with a prefix of 5 stages, and
fails at `e = 1.56·10⁻¹¹` with the same witness. The design's value is `-10.95`, and the certified
value without the lever is `-11.33` at a prefix of 3.

L8′ needs the longer prefix. At a prefix of 3 it gains nothing, since `J2` binds with the classical
`ctail`. So this module certifies two more stages: `δ₃` at `l = 12`, `b₃` at `l = 10`, `δ₄` at
`l = 13`, `b₄` at `l = 11`. The first three stages are the sites of `Tests/RefinedR1.lean`.

What this does and does not show is as in `Tests/RefinedR1.lean`: the small-divisor constants are
certified, one `decide +kernel` per bite, for the box `r1Box`; the claim `r1Claim` is the design's
data (sampled sups × 1.05), **not** a checked bound.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The refined witness of R1 with lever L8′. -/
def r1RefinedWitR : RefinedWitR where
  base :=
    { core :=
        { Xs := 161000
          kp := 5
          th := 1 / 200
          c := [2978 / 10 ^ 6, 2912 / 10 ^ 6, 2900 / 10 ^ 6, 2938 / 10 ^ 6, 2939 / 10 ^ 6]
          cbar := [6745 / 10 ^ 6, 4018 / 10 ^ 6, 3122 / 10 ^ 6, 2938 / 10 ^ 6, 2906 / 10 ^ 6]
          ctail := 4071 / 50000
          sB := 19294169 / 10000000
          sT := 65 / 100
          sLt := 13937561 / 10000000
          sN := 1428831 / 1000000
          sNt := 7277337 / 5000000
          t := 356 / 100
          J := 4 }
      R := r1Claim
      κ := r1Kappa
      sites := r1RefinedWit.sites ++
        [(some ⟨498137 / 500000, 12, 8, 1699320⟩, some ⟨977669 / 1000000, 10, 8, 46455⟩),
         (some ⟨124767 / 125000, 13, 8, 6798600⟩, some ⟨247171 / 250000, 11, 8, 178853⟩)] }
  bF := 1177 / 5000000
  bT := 99089 / 1250000

/-- The parameters of the test. -/
def r1PassR : CertParams := r1Params (155 / 10 ^ 13) (1 / 300)

/-- The numbers of the run. -/
def r1QR : NumQ := r1RefinedWitR.base.num 2 r1PassR r1Box

theorem r1R_site_d3 : siteOk r1QR.n r1QR.τ 4 r1Box r1Kappa r1PassR.γ (r1QR.δ 3) (r1QR.c.getD 3 0)
    (r1RefinedWitR.base.sites.getD 3 (none, none)).1 = true := by decide +kernel

theorem r1R_site_b3 : siteOk r1QR.n r1QR.τ 4 r1Box r1Kappa r1PassR.γ (r1QR.b 3)
    (r1QR.cbar.getD 3 0) (r1RefinedWitR.base.sites.getD 3 (none, none)).2 = true := by
  decide +kernel

theorem r1R_site_d4 : siteOk r1QR.n r1QR.τ 4 r1Box r1Kappa r1PassR.γ (r1QR.δ 4) (r1QR.c.getD 4 0)
    (r1RefinedWitR.base.sites.getD 4 (none, none)).1 = true := by decide +kernel

theorem r1R_site_b4 : siteOk r1QR.n r1QR.τ 4 r1Box r1Kappa r1PassR.γ (r1QR.b 4)
    (r1QR.cbar.getD 4 0) (r1RefinedWitR.base.sites.getD 4 (none, none)).2 = true := by
  decide +kernel

theorem r1R_sites : sitesOk r1QR 4 r1Box r1Kappa r1PassR.γ r1RefinedWitR.base.sites = true :=
  sitesOk_of fun s hs => by
    have hk : s < 5 := hs
    interval_cases s
    · exact ⟨r1_site_d0, r1_site_b0⟩
    · exact ⟨r1_site_d1, r1_site_b1⟩
    · exact ⟨r1_site_d2, r1_site_b2⟩
    · exact ⟨r1R_site_d3, r1R_site_b3⟩
    · exact ⟨r1R_site_d4, r1R_site_b4⟩

theorem r1R_wf : r1QR.wfOk = true := by decide +kernel

theorem r1R_ok : r1QR.okR r1RefinedWitR.bF (capRQ r1QR r1PassR.μ r1PassR.nuRay r1RefinedWitR.bT)
    (initRQ r1Claim.bL r1Claim.bN r1Claim.bNt r1PassR.σK r1PassR.σB r1PassR.μ) 161000 = true := by
  decide +kernel

theorem r1R_budget : r1QR.budgetOk (r1PassR.σT - r1PassR.μ) r1Claim.bT r1RefinedWitR.bF
    r1RefinedWitR.bT = true := by decide +kernel

theorem r1R_tail : classicalOk 2 1 4 (r1QR.δ 5) r1QR.ctail = true := by decide +kernel

theorem r1R_final : finalOkA r1QR r1PassR r1Box 161000 = true := by decide +kernel

/-- **`refinedCoreR` on R1**, at `e = 1.55·10⁻¹¹`. -/
theorem r1_refinedCoreR : refinedCoreR 2 r1PassR r1Box r1RefinedWitR = true :=
  refinedCoreR_of (by norm_num [r1RefinedWitR]) r1R_wf r1R_ok r1R_budget r1R_sites r1R_tail
    r1R_final

/-- The same witness fails at `e = 1.56·10⁻¹¹`: the smallness is the binding comparison. -/
theorem r1R_final_rejects :
    finalOkA r1QR (r1Params (156 / 10 ^ 13) (1 / 300)) r1Box 161000 = false := by decide +kernel

end KAM.CertificateSharp.V2

end
