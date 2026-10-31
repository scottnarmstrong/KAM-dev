/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefined
public import KAM.CertificateSharp.V2.Tests.Frozen

/-!
# The numerical part of stage 2 on the design package R1, in the kernel

`refinedCore` passes at `e = 4.7·10⁻¹²`, that is `10^(-11.33)`, with a prefix of 3 stages, and
fails at `e = 4.8·10⁻¹²` with the same witness.

What this does and does not show:

* the small-divisor constants are certified here, one `decide +kernel` per bite: the bounds of
  `S((ω', 1), b)` for the box `r1Box` are `balBound`s;
* the claim `r1Claim` is the design's data (sampled sups of `r1_norms.py` × 1.05), **not** a checked
  bound: the bounds on `H` and the frame come from the lunar models, which are not run here.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The claim of the design package: sampled sups × 1.05. -/
def r1Claim : RefClaim where
  dh := 105 / 100 * (18228 / 10000)
  dx := 105 / 100 * (175 / 100)
  d2x := 105 / 100 * (10342 / 10000)
  d2h := 105 / 100 * (18323 / 10000)
  bL := 105 / 100 * (13268 / 10000)
  bN := 105 / 100 * (13540 / 10000)
  bNt := 105 / 100 * (13787 / 10000)
  bT := 105 / 100 * (33130 / 10000)

/-- The refined witness of R1. -/
def r1RefinedWit : RefinedWit where
  core :=
    { Xs := 49000
      kp := 3
      th := 1 / 8
      c := [2978 / 10 ^ 6, 2912 / 10 ^ 6, 2900 / 10 ^ 6]
      cbar := [6745 / 10 ^ 6, 4018 / 10 ^ 6, 3122 / 10 ^ 6]
      ctail := 1629 / 20000
      sB := 192597 / 100000
      sT := 127829 / 200000
      sLt := 348323 / 250000
      sN := 284731 / 200000
      sNt := 362441 / 250000
      t := 1767111 / 500000
      J := 4 }
  R := r1Claim
  κ := r1Kappa
  sites :=
    [(some ⟨970567 / 1000000, 10, 8, 545543 / 20⟩, some ⟨208937 / 250000, 7, 8, 388019 / 100⟩),
     (some ⟨1231467 / 1250000, 11, 8, 104334⟩, some ⟨914111 / 1000000, 8, 8, 109921 / 20⟩),
     (some ⟨1240699 / 1250000, 12, 8, 20686609 / 50⟩, some ⟨478003 / 500000, 9, 8, 132149 / 10⟩)]

/-- The parameters of the test. -/
def r1Pass : CertParams := r1Params (47 / 10 ^ 13) (1 / 300)

/-- The numbers of the run. -/
def r1Q : NumQ := r1RefinedWit.num 2 r1Pass r1Box

theorem r1_site_d0 : siteOk r1Q.n r1Q.τ 4 r1Box r1Kappa r1Pass.γ (r1Q.δ 0) (r1Q.c.getD 0 0)
    (r1RefinedWit.sites.getD 0 (none, none)).1 = true := by decide +kernel

theorem r1_site_b0 : siteOk r1Q.n r1Q.τ 4 r1Box r1Kappa r1Pass.γ (r1Q.b 0) (r1Q.cbar.getD 0 0)
    (r1RefinedWit.sites.getD 0 (none, none)).2 = true := by decide +kernel

theorem r1_site_d1 : siteOk r1Q.n r1Q.τ 4 r1Box r1Kappa r1Pass.γ (r1Q.δ 1) (r1Q.c.getD 1 0)
    (r1RefinedWit.sites.getD 1 (none, none)).1 = true := by decide +kernel

theorem r1_site_b1 : siteOk r1Q.n r1Q.τ 4 r1Box r1Kappa r1Pass.γ (r1Q.b 1) (r1Q.cbar.getD 1 0)
    (r1RefinedWit.sites.getD 1 (none, none)).2 = true := by decide +kernel

theorem r1_site_d2 : siteOk r1Q.n r1Q.τ 4 r1Box r1Kappa r1Pass.γ (r1Q.δ 2) (r1Q.c.getD 2 0)
    (r1RefinedWit.sites.getD 2 (none, none)).1 = true := by decide +kernel

theorem r1_site_b2 : siteOk r1Q.n r1Q.τ 4 r1Box r1Kappa r1Pass.γ (r1Q.b 2) (r1Q.cbar.getD 2 0)
    (r1RefinedWit.sites.getD 2 (none, none)).2 = true := by decide +kernel

theorem r1_sites : sitesOk r1Q 4 r1Box r1Kappa r1Pass.γ r1RefinedWit.sites = true :=
  sitesOk_of fun s hs => by
    have hk : s < 3 := hs
    interval_cases s
    · exact ⟨r1_site_d0, r1_site_b0⟩
    · exact ⟨r1_site_d1, r1_site_b1⟩
    · exact ⟨r1_site_d2, r1_site_b2⟩

theorem r1_wf : r1Q.wfOk = true := by decide +kernel

theorem r1_ok : r1Q.okB (capQ r1Q r1Pass.μ r1Pass.nuRay)
    (initQ r1Claim.bL r1Claim.bN r1Claim.bNt r1Claim.bT r1Pass.σK r1Pass.σB r1Pass.σT r1Pass.μ)
    49000 = true := by decide +kernel

theorem r1_tail : classicalOk 2 1 4 (r1Q.δ 3) r1Q.ctail = true := by decide +kernel

theorem r1_final : finalOkA r1Q r1Pass r1Box 49000 = true := by decide +kernel

/-- **`refinedCore` on R1**, at `e = 4.7·10⁻¹²`. -/
theorem r1_refinedCore : refinedCore 2 r1Pass r1Box r1RefinedWit = true :=
  refinedCore_of (by norm_num [r1RefinedWit]) r1_wf r1_ok r1_sites r1_tail r1_final

/-- The same witness fails at `e = 4.8·10⁻¹²`: the smallness is the binding comparison. -/
theorem r1_final_rejects :
    finalOkA r1Q (r1Params (48 / 10 ^ 13) (1 / 300)) r1Box 49000 = false := by decide +kernel

end KAM.CertificateSharp.V2

end
