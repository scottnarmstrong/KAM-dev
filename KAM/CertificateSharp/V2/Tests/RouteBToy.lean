/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBEngine
public import KAM.CertificateSharp.V2.Tests.Refined

/-!
# Route B in the kernel, on the toy T2 at the strip `ρ = 1`

Route B asks `ρ ≤ 1` (`NumB.Wf.ρ_le`; its schedule `δ₀ = (ρ - ρ∞)(a - 1)/(3a)` is unclipped), and
T2 has `ρ = 9`. `toyB` is T2 on the narrower strip `ρ = 1`, `ρ∞ = 1/100`, with the strip weight
`540 ≥ e^{2π}`: every other datum is T2's, and the landed sub-checks pass on it.

* `toyB_frozenB_passes`: the whole v2 certifier with `routeBFrozen` (the literal
  `iso_g1_v2B_frozen`: `M₁ = M₂ = M_h2 = M`, the default initial values, classical constants);
* `toyB_refinedB_passes`: the same with `routeBRefined` (the branch `iso_g1_branch_B` at the refined
  bounds of `toyRefinedWit.R`, computed from T2's models by the disc pass and the frame majorants),
  with a certified constant `1/50` at `δ₀ = 33/200` (classical: `0.102`);
* `toyB_frozenB_torus`, `toyB_refinedB_torus`: the soundness theorems at the reference frequency;
* the combined engine `routeABV2` with route B's witnesses, and a rejection.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM.Certificate

/-- T2 on the strip `ρ = 1`. -/
def toyB : TorusCertificate 2 ℚ :=
  { toyCert2 with
    params := { toyCert2.params with rho := 1, rhoInf := 1 / 100 }
    weight := ⟨1, 540⟩ }

/-- The frozen route-B witness of `toyB`. -/
def toyFrozenBWit : RunBWit where
  Xs := 1 / 10 ^ 25
  kp := 2
  a := 2
  ybar := 1 / 2
  θ := 1 / 16
  θξ := 1 / 8
  θΩ := 1 / 8
  q := 1 / 8
  θN := 1 / 8
  θω := 1 / 8
  ts := 1 / 10
  bF := 1 / 10 ^ 12
  selfcons := false
  lam0 := 1163 / 100000
  lamW0 := 3319 / 10 ^ 7
  ePer0 := 3319 / 10 ^ 7
  c := [51 / 500, 93 / 1000]
  c' := [93 / 1000, 11 / 125]
  cbar := [171 / 1000, 27 / 200]
  ctail := 11 / 125
  cbtail := 14 / 125
  sB := 777 / 250
  sT := 777 / 250
  sLt := 1554 / 125
  sN := 28749 / 3125
  sNt := 114996 / 3125
  J := 2

/-- The refined route-B witness of `toyB`. -/
def toyRefinedBWit : RefinedBWit where
  core :=
    { toyFrozenBWit with
      Xs := 1 / 10 ^ 20
      bF := 1 / 10 ^ 15
      lam0 := 393 / 100000
      lamW0 := 389 / 100000
      ePer0 := 389 / 100000
      c := [1 / 50, 93 / 1000]
      sLt := 2121 / 2000
      sN := 2121 / 2000
      sNt := 2121 / 2000 }
  R := toyRefinedWit.R
  κ := 1 / 2
  sites := [(some ⟨13 / 100, 3, 16, 5778 / 100⟩, none, none)]

theorem toyB_freq : FreqEncloses 2 toyB.freqBox ![lunarNuMinus / 2, 1 / 2] := toyCert2_freq

theorem toyB_dio : IsDiophantine ((toyB.params.γ : ℚ) : ℝ) ((toyB.params.tau : ℕ) : ℝ)
    ![lunarNuMinus / 2, 1 / 2] := by
  have h : ((toyB.params.γ : ℚ) : ℝ) = 1 / 42 := by
    rw [show toyB.params.γ = 1 / 42 by decide +kernel]; norm_num
  have ht : ((toyB.params.tau : ℕ) : ℝ) = 1 := by
    rw [show toyB.params.tau = 1 by decide +kernel]; norm_num
  rw [h, ht]
  exact lunarNuMinus_half_isDiophantine

/-- The whole v2 certifier on `toyB`, route B at the frozen data. -/
theorem toyB_frozenB_passes :
    checkTorusCertificateV2 routeBFrozen toyB toyFrozenBWit = true := by
  decide +kernel

/-- **The toy torus through route B at the frozen data** (`iso_g1_v2B_frozen`). -/
theorem toyB_frozenB_torus : CertifiedTorus toyB ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeBFrozen toyB_frozenB_passes toyB_freq toyB_dio

/-- The whole v2 certifier on `toyB`, route B at the refined data. -/
theorem toyB_refinedB_passes :
    checkTorusCertificateV2 routeBRefined toyB toyRefinedBWit = true := by
  decide +kernel

/-- **The toy torus through route B at the refined data** (`iso_g1_branch_B`). -/
theorem toyB_refinedB_torus : CertifiedTorus toyB ![lunarNuMinus / 2, 1 / 2] :=
  checkTorusCertificateV2_sound routeBRefined toyB_refinedB_passes toyB_freq toyB_dio

/-- The combined engine, with route B's refined witness. -/
theorem toyB_routeABV2_passes :
    checkTorusCertificateV2 routeABV2 toyB (Sum.inr (Sum.inr (Sum.inr toyRefinedBWit))) = true :=
  (checkTorusCertificateV2_routeABV2_routeB toyB (Sum.inr toyRefinedBWit)).trans
    ((checkTorusCertificateV2_orElse_inr routeBFrozen routeBRefined toyB toyRefinedBWit).trans
      toyB_refinedB_passes)

/-- A witness above the threshold of the recursion is rejected. -/
theorem toyB_frozenB_rejects :
    frozenBCore 2 toyB.params toyB.freqBox { toyFrozenBWit with Xs := 1 / 10 ^ 10 } = false := by
  decide +kernel

end KAM.CertificateSharp.V2

end
