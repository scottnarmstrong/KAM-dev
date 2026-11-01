/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyClaim
public import KAM.CertificateSharp.V2.Tests.Forced.TinyFreq
public import KAM.CertificateSharp.V2.Tests.Forced.Lemmas
public import KAM.CertificateSharp.V2.RouteAll

/-!
# Route A on the forced toy `Tiny`, in the kernel

* `refinedWit`: route A at the refined data (`iso_g1_v2A`): the claim `Rclaim`, certified
  small-divisor sites at every bite of the prefix (`siteOk` with the balanced fibered checker),
  the classical tail; `X⋆ = (382)`, threshold `e* = X⋆ γ⁴ δ₀⁴ ≈ 6.91e-09` against
  `err = (41 / 10000000000000)`;
* `refinedA_passes`: the whole v2 certifier at `routeV2All` with the witness of `routeARefined`
  (the landed sub-checks from `TinyBase`, the claim from `TinyClaim`);
* `refinedA_torus`: the certified torus at the reference frequency
  (`checkTorusCertificateV2_sound`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The refined route-A witness of `Tiny`. -/
def refinedWit : RefinedWit where
  core :=
    { Xs := (382), kp := 3, th := (1 / 8),
      c := [(1249 / 100000), (1177 / 100000), (1169 / 100000)],
      cbar := [(291 / 12500), (371 / 20000), (1389 / 100000)], ctail := (1021567 / 12500000),
      sB := (6376861 / 6250000), sT := (115601901 / 100000000), sLt := (2002329 / 2000000),
      sN := (100138857 / 100000000), sNt := (10014649 / 10000000), t := (100494123 / 100000000),
      J := 20 }
  R := Rclaim
  κ := (1000000 / 1000001)
  sites :=
    [(some ⟨(773227 / 1000000), 6, 8, (9044 / 25)⟩,
      some ⟨(26037 / 125000), 4, 8, (171071 / 5000)⟩),
     (some ⟨(220053 / 250000), 7, 8, (25697 / 20)⟩,
      some ⟨(113319 / 250000), 5, 8, (21287 / 250)⟩),
     (some ⟨(469567 / 500000), 9, 8, (507257 / 100)⟩,
      some ⟨(668659 / 1000000), 6, 8, (36741 / 200)⟩)]

theorem refinedA_sites : sitesOk (refinedWit.num 2 cert.params cert.freqBox) refinedWit.core.J
    cert.freqBox refinedWit.κ cert.params.γ refinedWit.sites = true := by decide +kernel

theorem refinedA_core : refinedCore 2 cert.params cert.freqBox refinedWit = true :=
  refinedCore_of (by decide +kernel) (by decide +kernel) (by decide +kernel) refinedA_sites
    (by decide +kernel) (by decide +kernel)

theorem refinedA_test : refinedTest cert refinedWit = true := by
  have h1 : checkHamClaim cert refinedWit.R = true := hamClaim_ok
  have h2 : checkFrameMajorants cert (refinedWit.R.frame cert.freqBox) = true := frame_ok
  show (checkHamClaim cert refinedWit.R &&
    checkFrameMajorants cert (refinedWit.R.frame cert.freqBox) &&
    refinedCore 2 cert.params cert.freqBox refinedWit) = true
  rw [h1, h2, refinedA_core]
  rfl

/-- **The forced toy through `routeV2All`**, at the witness of `routeARefined`. -/
theorem refinedA_passes : checkTorusCertificateV2 routeV2All cert
    (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr refinedWit))))) = true := by
  rw [checkTorusCertificateV2_routeV2All_aRefined]
  refine (checkV2_eq routeARefined cert refinedWit).trans ?_
  rw [base_ok, Bool.true_and]
  exact (routeARefined_test cert refinedWit).trans refinedA_test

/-- **The certified torus of the forced toy `Tiny`** at `κ (ν₋(8) - 1, 1)`. -/
theorem refinedA_torus : CertifiedTorus cert ωstar :=
  checkTorusCertificateV2_sound routeV2All refinedA_passes freq dio

end KAM.CertificateSharp.V2.Forced.Tiny

end
