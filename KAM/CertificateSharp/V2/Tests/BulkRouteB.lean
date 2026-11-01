/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteH
public import KAM.CertificateSharp.V2.Tests.Fiber3ToyB

/-!
# Route B with bulk sites, end to end, on `toyB3`

`toyB3` (`Tests/Fiber3ToyB.lean`: T3 on the strip `ρ = 1`, `n = 3`, `τ = 2`) passes
`routeBRefinedG` with six fibered sites. Here the two sites at the bites `1` and `101/200` are
**bulk** sites (`.bulk`, `bulkSiteOk`, the walk `walkB`) and the four others are the landed
fibered sites (`.g`): `toyB3_refinedBH_passes` is the whole v2 certifier at `routeBRefinedH`,
and `toyB3_refinedBH_torus` its soundness theorem at `cubicFreq`.

T3's frequency `(∛2/2, ∛4/2, 1/2)` has no slow coordinate (`ω' = (0.63, 0.79)`), so no run of
two or more fibres passes the acceptance test: the bulk walk evaluates every fibre, as `mode3`,
and its value equals the landed walk's (mirror: `scripts/certifier/fiber3_bulk.py`). This module
tests the integration of the bulk test into the engine, not its savings (`Tests/BulkToy.lean`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.CertificateSharp KAM.CertificateSharp.Fiber

/-- The bulk site at the bite `1` (the data of `b3f0`). -/
def b3f0B : BulkWit :=
  { N := 2, l := 3, J := 45, P := 64, e := 64741242463817,
    D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 },
    B := 214029 / 5000000000,
    gs := [18446744073709551616, 18446808814952015433, 18446808815179234024,
      18446808815179234026],
    rn := 5, rd := 4, tol := 0 }

/-- The bulk site at the bite `101/200` (the data of `b3f1`). -/
def b3f1B : BulkWit :=
  { N := 3, l := 3, J := 27, P := 64, e := 32454631529272055,
    D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 },
    B := 217079 / 10000000,
    gs := [18446744073709551616, 18479198705238823671, 18479255905374111821,
      18479255905551168504],
    rn := 5, rd := 4, tol := 0 }

theorem b3f0B_ok : bulkSiteOk 3 2 toyT3Box (1 / 12) 1 (4909 / 10000000) b3f0B = true := by
  decide +kernel

theorem b3f1B_ok :
    bulkSiteOk 3 2 toyT3Box (1 / 12) (101 / 200) (141 / 50000) b3f1B = true := by
  decide +kernel

/-- The sites of the two prefix stages: four landed fibered sites and two bulk sites. -/
def b3SitesH : BSitesH :=
  [(.g (.fiber b3d0), .g (.fiber b3s0), .bulk b3f0B),
    (.g (.fiber b3d1), .g (.fiber b3s1), .bulk b3f1B)]

/-- The witness of `routeBRefinedH`: the run of `b3Wit` with the sites `b3SitesH`. -/
def b3WitH (Xs : ℚ) : RefinedBWitH := { RefinedBWitH.ofG (b3Wit Xs) with sites := b3SitesH }

/-- The prefix sites of any run with these bites and constants. -/
theorem b3_sitesOkH (Q : NumBQ) (hkp : Q.kp = 2) (hτ : Q.τ = 2) (h0 : Q.δ 0 = 33 / 200)
    (h1 : Q.δ 1 = 33 / 400) (hs0 : Q.split * Q.δ 0 = 11 / 100) (hs1 : Q.split * Q.δ 1 = 11 / 200)
    (hf0 : Q.bfull 0 = 1) (hf1 : Q.bfull 1 = 101 / 200)
    (hc : Q.c = [719 / 200000, 3037 / 1000000]) (hc' : Q.c' = [3211 / 1000000, 2891 / 1000000])
    (hcb : Q.cbar = [4909 / 10000000, 141 / 50000]) :
    Q.sitesOkH 3 2 toyT3Box (1 / 2) (1 / 12) b3SitesH = true := by
  refine NumBQ.sitesOkH_of fun s hs => ?_
  rw [hkp] at hs
  interval_cases s
  · rw [hs0]
    simp only [hτ, h0, hf0, hc, hc', hcb, b3SitesH, List.getD_cons_zero, siteOkH_g]
    exact ⟨siteOkG_fiber_of b3d0_ok, siteOkG_fiber_of b3s0_ok, siteOkH_bulk_of b3f0B_ok⟩
  · rw [hs1]
    simp only [hτ, h1, hf1, hc, hc', hcb, b3SitesH, List.getD_cons_succ, List.getD_cons_zero,
      siteOkH_g]
    exact ⟨siteOkG_fiber_of b3d1_ok, siteOkG_fiber_of b3s1_ok, siteOkH_bulk_of b3f1B_ok⟩

/-- The numerical core with the bulk sites: the run's parts from `toyB3_core`, the sites here. -/
theorem toyB3_coreH :
    refinedBCoreH 3 toyB3.params toyB3.freqBox (b3WitH (1 / 10 ^ 20)) = true := by
  have h := toyB3_core
  simp only [refinedBCoreG, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩ := h
  exact refinedBCoreH_of h0 h1 h2 h3 h4
    (b3_sitesOkH _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl rfl)
    h6 h7

/-- **The v2 certifier passes `toyB3` at `routeBRefinedH`**, with two bulk sites. -/
theorem toyB3_refinedBH_passes :
    checkTorusCertificateV2 routeBRefinedH toyB3 (b3WitH (1 / 10 ^ 20)) = true :=
  checkTorusCertificateV2_routeBRefinedH_of toyB3_base toyB3_hamClaim toyB3_frame toyB3_coreH

/-- The same witness at the combined engine `routeV2H`. -/
theorem toyB3_routeV2H_passes :
    checkTorusCertificateV2 routeV2H toyB3 (Sum.inr (Sum.inr (b3WitH (1 / 10 ^ 20)))) = true :=
  (checkTorusCertificateV2_routeV2H_B toyB3 _).trans toyB3_refinedBH_passes

/-- **The torus of `toyB3` at `cubicFreq`**, through route B with bulk sites. -/
theorem toyB3_refinedBH_torus : CertifiedTorus toyB3 cubicFreq :=
  checkTorusCertificateV2_sound routeBRefinedH toyB3_refinedBH_passes toyCert3_freq (by
    have h : ((toyB3.params.γ : ℚ) : ℝ) = 1 / 12 := by
      rw [show toyB3.params.γ = 1 / 12 by decide +kernel]; norm_num
    have ht : ((toyB3.params.tau : ℕ) : ℝ) = 2 := by
      rw [show toyB3.params.tau = 2 by decide +kernel]; norm_num
    rw [h, ht]
    exact cubicFreq_isDiophantine_twelfth)

end KAM.CertificateSharp.V2

end
