/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBEngine
public import KAM.CertificateSharp.V2.Tests.Frozen

/-!
# The numerical part of route B on the design package R1 (opt-in, not part of the library)

Not built by anything. Its module name follows `kernel-tests/README.md`: the file stands for
`KAM.CertificateSharp.V2.Tests.RouteBR1`. It imports only library modules, so it runs directly:
`nice -n 10 lake env lean kernel-tests/CertificateSharp/V2/RouteBR1.lean`. The whole of it, with
`RouteBR1Sites`, peaked at 1.8 GB (6 s) when it last ran as one file.

* **Refined (the branch `iso_g1_branch_B`)**: every part of `refinedBCore` other than the prefix
  sites passes at `e = 2.6·10⁻¹³`, that is `10^(-12.59)`, with a prefix of 3 stages and `a = 2`, and
  `finalB` fails at `e = 2.7·10⁻¹³`. The prefix sites are the bites of SHARP2-C6, assembled in
  `RouteBR1Sites.lean`: `r1B_refinedCore_of_sites` is conditional on them.
* **Frozen (the literal wrapper `iso_g1_v2B_frozen`)**: `frozenBCore` passes at
  `e = 1.6·10⁻¹⁹` (`10^(-18.80)`), prefix 3, classical constants, and fails at `1.7·10⁻¹⁹`.

What this does and does not show (as for route A in `RefinedR1.lean`): the claim `r1BClaim` is the
design's data (sampled sups × 1.05), **not** a checked bound; the refined figure is a property of
the branch with frequency-specific ray certificates and these data, not of the literal frozen form,
whose figure is the second one (AUDIT-ROUTEB-iso-1, F1). The box `r1Box` is a test datum; no torus
is produced.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The claim of the design package: sampled sups × 1.05 (the values of `r1Claim`). -/
def r1BClaim : RefClaim where
  dh := 105 / 100 * (18228 / 10000)
  dx := 105 / 100 * (175 / 100)
  d2x := 105 / 100 * (10342 / 10000)
  d2h := 105 / 100 * (18323 / 10000)
  bL := 105 / 100 * (13268 / 10000)
  bN := 105 / 100 * (13540 / 10000)
  bNt := 105 / 100 * (13787 / 10000)
  bT := 105 / 100 * (33130 / 10000)

/-- The numbers of the refined route-B run of R1. -/
def r1BCore : RunBWit where
  Xs := 157 / 10000
  kp := 3
  a := 2
  ybar := 1 / 2
  θ := 1 / 16
  θξ := 1 / 8
  θΩ := 1 / 8
  q := 1 / 8
  θN := 1 / 8
  θω := 1 / 8
  ts := 1 / 10
  bF := 47222 / 10 ^ 10
  selfcons := false
  lam0 := 10299 / 10 ^ 8
  lamW0 := 7114 / 10 ^ 8
  ePer0 := 7114 / 10 ^ 8
  c := [2978 / 10 ^ 6, 2912 / 10 ^ 6, 2900 / 10 ^ 6]
  c' := [2912 / 10 ^ 6, 2900 / 10 ^ 6, 163 / 2000]
  cbar := [6745 / 10 ^ 6, 4018 / 10 ^ 6, 3122 / 10 ^ 6]
  ctail := 163 / 2000
  cbtail := 817 / 10000
  sB := 808353 / 400000
  sT := 32193 / 50000
  sLt := 1462797 / 1000000
  sN := 298557 / 200000
  sNt := 6080067 / 4000000
  J := 4

/-- The refined route-B witness of R1: the bite witnesses of SHARP2-C6 at `δ₀, δ₁, δ₂` and
`b₀, b₁, b₂`; at `a = 2` the split bite of stage `s` is `δ_{s+1}`, classical at `s = 2`. -/
def r1BWit : RefinedBWit where
  core := r1BCore
  R := r1BClaim
  κ := r1Kappa
  sites :=
    [(some ⟨970567 / 1000000, 10, 8, 545543 / 20⟩, some ⟨1231467 / 1250000, 11, 8, 104334⟩,
        some ⟨208937 / 250000, 7, 8, 388019 / 100⟩),
      (some ⟨1231467 / 1250000, 11, 8, 104334⟩, some ⟨1240699 / 1250000, 12, 8, 20686609 / 50⟩,
        some ⟨914111 / 1000000, 8, 8, 109921 / 20⟩),
      (some ⟨1240699 / 1250000, 12, 8, 20686609 / 50⟩, none,
        some ⟨478003 / 500000, 9, 8, 132149 / 10⟩)]

/-- The parameters of the refined test. -/
def r1PassB : CertParams := r1Params (26 / 10 ^ 14) (1 / 300)

/-- The numbers of the run. -/
def r1BQ : NumBQ := r1BWit.num r1PassB r1Box

theorem r1B_site_s2 : siteOk 2 r1BQ.τ 4 r1Box r1Kappa r1PassB.γ (r1BQ.split * r1BQ.δ 2)
    (r1BQ.c'.getD 2 r1BQ.ctail) (r1BWit.sites.getD 2 (none, none, none)).2.1 = true := by
  decide +kernel

theorem r1B_wf : r1BQ.wfOk 2 = true := by decide +kernel

theorem r1B_fits : r1BQ.fitsOk r1BClaim.bL r1BClaim.bNt = true := by decide +kernel

theorem r1B_init :
    r1BQ.initOk r1BClaim.bL r1BClaim.bN r1BClaim.bNt r1PassB.σT r1PassB.μ = true := by
  decide +kernel

theorem r1B_ok : r1BQ.okB 2 (r1BQ.capBQ r1PassB.σT r1PassB.μ r1PassB.nuRay)
    (NumBQ.initBQ r1BClaim.bL r1BClaim.bN r1BClaim.bNt r1PassB.σK r1PassB.σB r1PassB.μ)
    (r1PassB.μ / 2) (157 / 10000) = true := by decide +kernel

theorem r1B_tail : r1BQ.tailOk 2 4 = true := by decide +kernel

theorem r1B_final : finalB r1BQ 2 r1PassB r1Box r1BClaim.bL r1BClaim.bNt (157 / 10000) = true := by
  decide +kernel

/-- `refinedBCore` on R1 at `e = 2.6·10⁻¹³`, from the prefix sites (`RouteBR1Sites.lean`). -/
theorem r1B_refinedCore_of_sites
    (hs : r1BQ.sitesOk 2 4 r1Box r1Kappa r1PassB.γ r1BWit.sites = true) :
    refinedBCore 2 r1PassB r1Box r1BWit = true :=
  refinedBCore_of (by norm_num [r1BWit, r1BCore]) r1B_wf r1B_fits r1B_init r1B_ok hs r1B_tail
    r1B_final

/-- The same witness fails at `e = 2.7·10⁻¹³`: the smallness is the binding comparison. -/
theorem r1B_final_rejects :
    finalB (r1BWit.num (r1Params (27 / 10 ^ 14) (1 / 300)) r1Box) 2
      (r1Params (27 / 10 ^ 14) (1 / 300)) r1Box r1BClaim.bL r1BClaim.bNt (157 / 10000) = false := by
  decide +kernel

/-- The frozen route-B witness of R1: classical constants, the default initial values. -/
def r1FrozenBWit : RunBWit :=
  { r1BCore with
    Xs := 387 / 10 ^ 10
    bF := 752497 / 10 ^ 14
    lam0 := 19075 / 10 ^ 8
    lamW0 := 1811 / 10 ^ 8
    ePer0 := 1811 / 10 ^ 8
    c := [409 / 5000, 51 / 625, 163 / 2000]
    c' := [51 / 625, 163 / 2000, 163 / 2000]
    cbar := [417 / 5000, 103 / 1250, 819 / 10000]
    sLt := 574623 / 100000
    sN := 22118963139 / 8000000000
    sNt := 22118963139 / 2000000000 }

/-- **`frozenBCore` on R1** (the literal `iso_g1_v2B_frozen`), at `e = 1.6·10⁻¹⁹`. -/
theorem r1_frozenB_passes :
    frozenBCore 2 (r1Params (16 / 10 ^ 20) (1 / 10 ^ 3)) r1Box r1FrozenBWit = true := by
  decide +kernel

/-- The same witness fails at `e = 1.7·10⁻¹⁹`. -/
theorem r1_frozenB_rejects :
    frozenBCore 2 (r1Params (17 / 10 ^ 20) (1 / 10 ^ 3)) r1Box r1FrozenBWit = false := by
  decide +kernel

end KAM.CertificateSharp.V2

end
