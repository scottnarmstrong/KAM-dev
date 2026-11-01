/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyClaim
public import KAM.CertificateSharp.V2.Tests.Forced.TinyFreq
public import KAM.CertificateSharp.V2.Tests.Forced.Lemmas

/-!
# Route B on the forced toy `Tiny`, in the kernel

`refinedBWit`: route B at the refined data (`iso_g1_branch_B`), with the claim `Rclaim` of
`TinyClaim` and certified small-divisor sites at the three bites of each prefix stage (`δ_s`, the
split bite, `min r_s 1`); `X⋆ = (19 / 31250)`, threshold `γ⁴ρ⁴ / c₁ ≈ 5.33e-11` against
`err = (41 / 10000000000000)`. `refinedB_passes` is the whole v2 certifier at `routeV2All` with the
witness of `routeBRefined`, and `refinedB_torus` the certified torus.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The refined route-B witness of `Tiny`. -/
def refinedBWit : RefinedBWit where
  core :=
    { Xs := (19 / 31250), kp := 2, a := 2, ybar := 1 / 2, θ := 1 / 16, θξ := 1 / 8, θΩ := 1 / 8,
      q := 1 / 8, θN := 1 / 8, θω := 1 / 8, ts := 1 / 10, bF := (103 / 100000000),
      selfcons := false, lam0 := (103124897 / 50000000000), lamW0 := (206043751 / 100000000000),
      ePer0 := (206043751 / 100000000000), c := [(1249 / 100000), (1177 / 100000)],
      c' := [(1177 / 100000), (1169 / 100000)], cbar := [(291 / 12500), (371 / 20000)],
      ctail := (410399 / 5000000), cbtail := (857079 / 10000000), sB := (102010641 / 100000000),
      sT := (57501847 / 50000000), sLt := (100110271 / 100000000), sN := (20022119 / 20000000),
      sNt := (100110717 / 100000000), J := 20 }
  R := Rclaim
  κ := (1000000 / 1000001)
  sites :=
    [(some ⟨(773227 / 1000000), 6, 8, (9044 / 25)⟩,
      some ⟨(220053 / 250000), 7, 8, (25697 / 20)⟩,
      some ⟨(26037 / 125000), 4, 8, (171071 / 5000)⟩),
     (some ⟨(220053 / 250000), 7, 8, (25697 / 20)⟩,
      some ⟨(469567 / 500000), 9, 8, (507257 / 100)⟩,
      some ⟨(113319 / 250000), 5, 8, (21287 / 250)⟩)]

theorem refinedB_sites : (refinedBWit.num cert.params cert.freqBox).sitesOk 2 refinedBWit.core.J
    cert.freqBox refinedBWit.κ cert.params.γ refinedBWit.sites = true := by decide +kernel

theorem refinedB_core : refinedBCore 2 cert.params cert.freqBox refinedBWit = true :=
  refinedBCore_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) refinedB_sites (by decide +kernel) (by decide +kernel)

/-- **The forced toy through `routeV2All`**, at the witness of `routeBRefined`. -/
theorem refinedB_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inr (Sum.inr refinedBWit))) = true := by
  rw [checkTorusCertificateV2_routeV2All_bRefined]
  refine (checkV2_eq routeBRefined cert refinedBWit).trans ?_
  rw [base_ok, Bool.true_and]
  refine (routeBRefined_test cert refinedBWit).trans ?_
  have h1 : checkHamClaim cert refinedBWit.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedBWit.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedBWit.R &&
    checkFrameMajorants cert (refinedBWit.R.frame cert.freqBox) &&
    refinedBCore 2 cert.params cert.freqBox refinedBWit) = true
  rw [h1, h2, refinedB_core]
  rfl

/-- **The certified torus of `Tiny` through route B.** -/
theorem refinedB_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedB_passes freq dio

end KAM.CertificateSharp.V2.Forced.Tiny

end
