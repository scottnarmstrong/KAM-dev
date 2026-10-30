/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefinedEngine
public import KAM.Certificate.Tests.Toy2

/-!
# Stage 2 in the kernel, on the toy T2

The refined bounds of T2 are computed from its models: `‖DH‖ ≤ 2`, `‖DX_H‖ ≤ 1.01`, `‖D²X_H‖ = 0`,
`‖D²H‖ ≤ 1.01` by the disc pass (against the one-size `M = 2.97`), and the frame bounds `1.01` by the
majorants of C4 (against the defaults `5.92`, `8.76`, `35`). The certified small-divisor constants of
the two stages are `2·10⁻⁴` and `6·10⁻³`, against the classical `0.17` and `0.13`: `balBound` gives
`S((ω', 1), 1) ≤ 0.00012` at the frequency `(ν₋/2, 1/2) = κ (ν₋, 1)`, `κ = 1/2`.

`toyCert2_refined_passes` runs the whole certifier by `decide +kernel`, and `toyCert2_refined_torus`
is the soundness theorem at the reference frequency, through `iso_g1_v2A`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- The refined witness of T2. -/
def toyRefinedWit : RefinedWit where
  core :=
    { Xs := 1 / 10 ^ 30
      kp := 2
      th := 1 / 8
      c := [1 / 5000, 3 / 500]
      cbar := [1 / 5000, 1 / 5000]
      ctail := 111 / 1000
      sB := 3
      sT := 3
      sLt := 11 / 10
      sN := 11 / 10
      sNt := 11 / 10
      t := 11 / 10
      J := 2 }
  R :=
    { dh := 2, dx := 101 / 100, d2x := 1 / 100, d2h := 101 / 100
      bL := 101 / 100, bN := 101 / 100, bNt := 101 / 100, bT := 101 / 100 }
  κ := 1 / 2
  sites :=
    [(some ⟨1 / 100000, 3, 16, 12 / 100000⟩, some ⟨1 / 100000, 3, 16, 12 / 100000⟩),
     (some ⟨1 / 100, 3, 12, 45 / 100⟩, some ⟨1 / 100000, 3, 16, 12 / 100000⟩)]

theorem toyCert2_hamClaim : checkHamClaim toyCert2 toyRefinedWit.R = true := by decide +kernel

theorem toyCert2_refinedCore :
    refinedCore 2 toyCert2.params toyCert2.freqBox toyRefinedWit = true := by decide +kernel

/-- The whole v2 certifier on T2, at the refined data. -/
theorem toyCert2_refined_passes :
    checkTorusCertificateV2 routeARefined toyCert2 toyRefinedWit = true := by decide +kernel

/-- **The toy torus through route A at the refined data.** -/
theorem toyCert2_refined_torus : CertifiedTorus toyCert2 ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeARefined toyCert2_refined_passes toyCert2_freq (by
    have h : ((toyCert2.params.γ : ℚ) : ℝ) = 1 / 42 := by
      rw [show toyCert2.params.γ = 1 / 42 by decide +kernel]; norm_num
    have ht : ((toyCert2.params.tau : ℕ) : ℝ) = 1 := by
      rw [show toyCert2.params.tau = 1 by decide +kernel]; norm_num
    rw [h, ht]
    exact lunarNuMinus_half_isDiophantine)

/-- A too-small claim on `H` is rejected. -/
theorem toyCert2_hamClaim_rejects :
    checkHamClaim toyCert2 { toyRefinedWit.R with dx := 99 / 100 } = false := by decide +kernel

end KAM.CertificateSharp.V2

end
