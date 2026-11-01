/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteBK
public import KAM.CertificateSharp.V2.Tests.Fiber3ToyB

/-!
# Route B with extended bulk sites, end to end, on `toyB3`

`toyB3` (`Tests/Fiber3ToyB.lean`) passes `routeBRefinedG` with six fibered sites. Here the two sites
at the bites `1` and `101/200` are **extended bulk** sites (`.bulk2`, `bulk2SiteOk`, the walk
`walkB2` of `Fiber/Bulk2.lean`) and the four others are the landed fibered sites (`.h (.g …)`):
`toyB3_refinedBK_passes` is the whole v2 certifier at `routeBRefinedK` (`Fiber/RouteBK.lean`), and
`toyB3_refinedBK_torus` its soundness theorem at `cubicFreq`.

T3's frequency has no slow coordinate, so the walk takes no run of two or more fibres; it tests the
integration of the extended test into the engine (the light-crossing branch is taken at most nodes),
not its savings (`Tests/Bulk2Toy.lean`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.CertificateSharp KAM.CertificateSharp.Fiber

/-- The extended bulk site at the bite `1` (the data of `b3f0`). -/
def b3f0K : Bulk2Wit :=
  { N := 2, l := 3, J := 45, P := 64, e := 64741242463817,
    D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 },
    B := 214029 / 5000000000, rn := 5, rd := 4, tol := 0, s := 2, fuel := 64 }

/-- The extended bulk site at the bite `101/200` (the data of `b3f1`). -/
def b3f1K : Bulk2Wit :=
  { N := 3, l := 3, J := 27, P := 64, e := 32454631529272055,
    D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 },
    B := 217079 / 10000000, rn := 5, rd := 4, tol := 0, s := 2, fuel := 64 }

theorem b3f0K_ok : bulk2SiteOk 3 2 toyT3Box (1 / 12) 1 (4909 / 10000000) b3f0K = true := by
  decide +kernel

theorem b3f1K_ok :
    bulk2SiteOk 3 2 toyT3Box (1 / 12) (101 / 200) (141 / 50000) b3f1K = true := by
  decide +kernel

/-- The sites of the two prefix stages: four landed fibered sites and two extended bulk sites. -/
def b3SitesK : BSitesK :=
  [(.h (.g (.fiber b3d0)), .h (.g (.fiber b3s0)), .bulk2 b3f0K),
    (.h (.g (.fiber b3d1)), .h (.g (.fiber b3s1)), .bulk2 b3f1K)]

/-- The witness of `routeBRefinedK`: the run of `b3Wit` with the sites `b3SitesK`. -/
def b3WitK (Xs : ℚ) : RefinedBWitK :=
  { RefinedBWitK.ofH (RefinedBWitH.ofG (b3Wit Xs)) with sites := b3SitesK }

/-- The prefix sites of any run with these bites and constants. -/
theorem b3_sitesOkK (Q : NumBQ) (hkp : Q.kp = 2) (hτ : Q.τ = 2) (h0 : Q.δ 0 = 33 / 200)
    (h1 : Q.δ 1 = 33 / 400) (hs0 : Q.split * Q.δ 0 = 11 / 100) (hs1 : Q.split * Q.δ 1 = 11 / 200)
    (hf0 : Q.bfull 0 = 1) (hf1 : Q.bfull 1 = 101 / 200)
    (hc : Q.c = [719 / 200000, 3037 / 1000000]) (hc' : Q.c' = [3211 / 1000000, 2891 / 1000000])
    (hcb : Q.cbar = [4909 / 10000000, 141 / 50000]) :
    Q.sitesOkK 3 2 toyT3Box (1 / 2) (1 / 12) b3SitesK = true := by
  refine NumBQ.sitesOkK_of fun s hs => ?_
  rw [hkp] at hs
  interval_cases s
  · rw [hs0]
    simp only [hτ, h0, hf0, hc, hc', hcb, b3SitesK, List.getD_cons_zero, siteOkK_h, siteOkH_g]
    exact ⟨siteOkG_fiber_of b3d0_ok, siteOkG_fiber_of b3s0_ok, siteOkK_bulk2_of b3f0K_ok⟩
  · rw [hs1]
    simp only [hτ, h1, hf1, hc, hc', hcb, b3SitesK, List.getD_cons_succ, List.getD_cons_zero,
      siteOkK_h, siteOkH_g]
    exact ⟨siteOkG_fiber_of b3d1_ok, siteOkG_fiber_of b3s1_ok, siteOkK_bulk2_of b3f1K_ok⟩

/-- The numerical core with the extended bulk sites: the run's parts from `toyB3_core`. -/
theorem toyB3_coreK :
    refinedBCoreK 3 toyB3.params toyB3.freqBox (b3WitK (1 / 10 ^ 20)) = true := by
  have h := toyB3_core
  simp only [refinedBCoreG, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩ := h
  exact refinedBCoreK_of h0 h1 h2 h3 h4
    (b3_sitesOkK _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl rfl)
    h6 h7

/-- **The v2 certifier passes `toyB3` at `routeBRefinedK`**, with two extended bulk sites. -/
theorem toyB3_refinedBK_passes :
    checkTorusCertificateV2 routeBRefinedK toyB3 (b3WitK (1 / 10 ^ 20)) = true :=
  checkTorusCertificateV2_routeBRefinedK_of toyB3_base toyB3_hamClaim toyB3_frame toyB3_coreK

/-- **The torus of `toyB3` at `cubicFreq`**, through route B with extended bulk sites. -/
theorem toyB3_refinedBK_torus : CertifiedTorus toyB3 cubicFreq :=
  checkTorusCertificateV2_sound routeBRefinedK toyB3_refinedBK_passes toyCert3_freq (by
    have h : ((toyB3.params.γ : ℚ) : ℝ) = 1 / 12 := by
      rw [show toyB3.params.γ = 1 / 12 by decide +kernel]; norm_num
    have ht : ((toyB3.params.tau : ℕ) : ℝ) = 2 := by
      rw [show toyB3.params.tau = 2 by decide +kernel]; norm_num
    rw [h, ht]
    exact cubicFreq_isDiophantine_twelfth)

end KAM.CertificateSharp.V2

end
