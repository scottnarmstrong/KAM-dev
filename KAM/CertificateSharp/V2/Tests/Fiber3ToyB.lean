/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteBG
public import KAM.CertificateSharp.V2.Fiber.Shard
public import KAM.CertificateSharp.V2.Tests.Fiber3Toy

/-!
# Route B with three-frequency sites, on T3 at the strip `ρ = 1`

Route B asks `ρ ≤ 1` (`NumB.Wf.ρ_le`) and T3 has `ρ = 9`. `toyB3` is T3 on the strip `ρ = 1`,
`ρ∞ = 1/100`, with the strip weight `540 ≥ e^{2π}` (as `toyB` is T2's): every other datum is T3's,
`n = 3`, `τ = 2`, the frequency `cubicFreq = (∛2/2, ∛4/2, 1/2)`, and the landed sub-checks pass.

* **The sites.** The schedule (`a = 2`, `kp = 2`) has the bites `δ = 33/200, 33/400`, the split
  bites `11/100, 11/200` and the full bites `1, 101/200`. Each is a fibered site, decided by the
  kernel on its own (`b3*_ok`, 12 to 2,244 fibres); `b3_sitesOk` assembles them through
  `NumBQ.sitesOkG_of`. The certified constants are `14–160` times below the classical ones.
* **The torus.** `toyB3_refinedBG_passes` is the whole v2 certifier with `routeBRefinedG`, from
  its parts (`refinedBCoreG_of`); `toyB3_refinedBG_torus` is the soundness theorem at `cubicFreq`.
* **The threshold.** At the invariance error `5·10⁻²³` the core passes with the fibered sites at
  `X⋆ = 1.4·10⁻¹⁶` (`toyB3_threshold_fibered`) and fails with the classical sites at
  `X⋆ = 9·10⁻¹⁸`, near their largest `X⋆` (`toyB3_threshold_classical_fails`); the classical sites
  pass at `5·10⁻²⁴` (`toyB3_threshold_classical`). Each kernel theorem is about one `X⋆`. That no
  classical `X⋆` passes at `5·10⁻²³` is a sweep, not a kernel theorem: `#eval` sweeps of the same
  Lean `refinedBCoreG` put the last error passing at `1.1·10⁻²²` (fibered) and `8.0·10⁻²⁴`
  (classical), about `1.14` orders.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Fiber

/-- T3 on the strip `ρ = 1`. -/
def toyB3 : TorusCertificate 3 ℚ :=
  { toyCert3 with
    params := { toyCert3.params with rho := 1, rhoInf := 1 / 100 }
    weight := ⟨1, 540⟩ }

/-- The numbers of the route-B run of `toyB3` at `X⋆` with the constants `c`, `c'`, `cbar`. -/
def b3Core (Xs : ℚ) (c c' cbar : List ℚ) : RunBWit where
  Xs := Xs
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
  bF := 1 / 10 ^ 15
  selfcons := false
  lam0 := 1 / 400
  lamW0 := 1 / 400
  ePer0 := 1 / 400
  c := c
  c' := c'
  cbar := cbar
  ctail := 69071 / 1562500
  cbtail := 538161 / 10000000
  sB := 161 / 20
  sT := 161 / 20
  sLt := 2121 / 2000
  sN := 2121 / 2000
  sNt := 2121 / 2000
  J := 2

/-! ### The six fibered sites -/

/-- The fibered site at the bite `33/200` (220 fibres). -/
def b3d0 : FibWit where
  N := 10
  l := 5
  J := 14
  P := 64
  e := 2322137013275455680
  D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 }
  B := 77417 / 25000

/-- The fibered site at the bite `11/100` (544 fibres). -/
def b3s0 : FibWit where
  N := 16
  l := 6
  J := 12
  P := 64
  e := 4633385845345829963
  D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 }
  B := 62523 / 5000

/-- The fibered site at the bite `1` (12 fibres). -/
def b3f0 : FibWit where
  N := 2
  l := 3
  J := 45
  P := 64
  e := 64741242463817
  D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 }
  B := 214029 / 5000000000

/-- The fibered site at the bite `33/400` (1012 fibres). -/
def b3d1 : FibWit where
  N := 22
  l := 6
  J := 11
  P := 64
  e := 6544911537163088644
  D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 }
  B := 353649 / 10000

/-- The fibered site at the bite `11/200` (2244 fibres). -/
def b3s1 : FibWit where
  N := 33
  l := 7
  J := 10
  P := 64
  e := 9245046385353249900
  D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 }
  B := 40561 / 250

/-- The fibered site at the bite `101/200` (24 fibres). -/
def b3f1 : FibWit where
  N := 3
  l := 3
  J := 27
  P := 64
  e := 32454631529272055
  D := { q := 64, C0 := 23241441160490167842, C1 := 29282380947994691627, R0 := 1, R1 := 1 }
  B := 217079 / 10000000

theorem b3d0_ok :
    fiberSiteOk 3 2 toyT3Box (1 / 12) (33 / 200) (719 / 200000) b3d0 = true := by
  decide +kernel

theorem b3s0_ok :
    fiberSiteOk 3 2 toyT3Box (1 / 12) (11 / 100) (3211 / 1000000) b3s0 = true := by
  decide +kernel

theorem b3f0_ok :
    fiberSiteOk 3 2 toyT3Box (1 / 12) 1 (4909 / 10000000) b3f0 = true := by
  decide +kernel

theorem b3d1_ok :
    fiberSiteOk 3 2 toyT3Box (1 / 12) (33 / 400) (3037 / 1000000) b3d1 = true := by
  decide +kernel

theorem b3s1_ok :
    fiberSiteOk 3 2 toyT3Box (1 / 12) (11 / 200) (2891 / 1000000) b3s1 = true := by
  decide +kernel

theorem b3f1_ok :
    fiberSiteOk 3 2 toyT3Box (1 / 12) (101 / 200) (141 / 50000) b3f1 = true := by
  decide +kernel

/-- The sites of the two prefix stages. -/
def b3Sites : BSitesG :=
  [(.fiber b3d0, .fiber b3s0, .fiber b3f0), (.fiber b3d1, .fiber b3s1, .fiber b3f1)]

/-- The prefix sites of any run with these bites and constants, from the six site theorems. -/
theorem b3_sitesOk (Q : NumBQ) (hkp : Q.kp = 2) (hτ : Q.τ = 2) (h0 : Q.δ 0 = 33 / 200)
    (h1 : Q.δ 1 = 33 / 400) (hs0 : Q.split * Q.δ 0 = 11 / 100) (hs1 : Q.split * Q.δ 1 = 11 / 200)
    (hf0 : Q.bfull 0 = 1) (hf1 : Q.bfull 1 = 101 / 200)
    (hc : Q.c = [719 / 200000, 3037 / 1000000]) (hc' : Q.c' = [3211 / 1000000, 2891 / 1000000])
    (hcb : Q.cbar = [4909 / 10000000, 141 / 50000]) :
    Q.sitesOkG 3 2 toyT3Box (1 / 2) (1 / 12) b3Sites = true := by
  refine NumBQ.sitesOkG_of fun s hs => ?_
  rw [hkp] at hs
  interval_cases s
  · rw [hs0]
    simp only [hτ, h0, hf0, hc, hc', hcb, b3Sites, List.getD_cons_zero]
    exact ⟨siteOkG_fiber_of b3d0_ok, siteOkG_fiber_of b3s0_ok, siteOkG_fiber_of b3f0_ok⟩
  · rw [hs1]
    simp only [hτ, h1, hf1, hc, hc', hcb, b3Sites, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨siteOkG_fiber_of b3d1_ok, siteOkG_fiber_of b3s1_ok, siteOkG_fiber_of b3f1_ok⟩

/-! ### The witnesses -/

/-- The witness with fibered sites. -/
def b3Wit (Xs : ℚ) : RefinedBWitG where
  core := b3Core Xs [719 / 200000, 3037 / 1000000] [3211 / 1000000, 2891 / 1000000]
    [4909 / 10000000, 141 / 50000]
  R := t3RefClaim
  κ := 1 / 2
  sites := b3Sites

/-- The witness with classical sites. -/
def b3WitClassical (Xs : ℚ) : RefinedBWitG where
  core := b3Core Xs [499321 / 10000000, 72177 / 1562500] [1186807 / 25000000, 560973 / 12500000]
    [3914949 / 50000000, 6304251 / 100000000]
  R := t3RefClaim
  κ := 1 / 2
  sites := []

/-- The parameters of `toyB3` with the invariance error `err` and the displacement `disp`. -/
def b3ParamsAt (err disp : ℚ) : CertParams := { toyB3.params with err := err, disp := disp }

/-- The core of a fibered run from its parts. -/
theorem b3_core_of {p : CertParams} {Xs : ℚ} (hX : 0 < Xs)
    (h1 : ((b3Wit Xs).num p toyB3.freqBox).wfOk 3 = true)
    (h2 : ((b3Wit Xs).num p toyB3.freqBox).fitsOk (101 / 100) (101 / 100) = true)
    (h3 : ((b3Wit Xs).num p toyB3.freqBox).initOk (101 / 100) (101 / 100) (101 / 100) p.σT p.μ
      = true)
    (h4 : ((b3Wit Xs).num p toyB3.freqBox).okB 3
      (((b3Wit Xs).num p toyB3.freqBox).capBQ p.σT p.μ p.nuRay)
      (NumBQ.initBQ (101 / 100) (101 / 100) (101 / 100) p.σK p.σB p.μ) (p.μ / 2) Xs = true)
    (hγ : p.γ = 1 / 12)
    (hs : ((b3Wit Xs).num p toyB3.freqBox).sitesOkG 3 2 toyT3Box (1 / 2) (1 / 12) b3Sites = true)
    (h6 : ((b3Wit Xs).num p toyB3.freqBox).tailOk 3 2 = true)
    (h7 : finalB ((b3Wit Xs).num p toyB3.freqBox) 3 p toyB3.freqBox (101 / 100) (101 / 100) Xs
      = true) :
    refinedBCoreG 3 p toyB3.freqBox (b3Wit Xs) = true := by
  refine refinedBCoreG_of hX h1 h2 h3 h4 ?_ h6 h7
  rw [hγ]
  exact hs

/-! ### The torus -/

theorem toyB3_base : landedBase.check toyB3 = true := by decide +kernel

theorem toyB3_hamClaim : checkHamClaim toyB3 t3RefClaim = true := by decide +kernel

theorem toyB3_frame : checkFrameMajorants toyB3 (t3RefClaim.frame toyB3.freqBox) = true := by
  decide +kernel

theorem toyB3_core : refinedBCoreG 3 toyB3.params toyB3.freqBox (b3Wit (1 / 10 ^ 20)) = true :=
  b3_core_of (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (b3_sitesOk _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl rfl)
    (by decide +kernel) (by decide +kernel)

/-- **The whole v2 certifier on `toyB3`, route B with three-frequency sites.** -/
theorem toyB3_refinedBG_passes :
    checkTorusCertificateV2 routeBRefinedG toyB3 (b3Wit (1 / 10 ^ 20)) = true :=
  checkTorusCertificateV2_routeBRefinedG_of toyB3_base toyB3_hamClaim toyB3_frame toyB3_core

/-- **The toy 3-torus on the strip `ρ = 1`, through route B with three-frequency sites.** -/
theorem toyB3_refinedBG_torus : CertifiedTorus toyB3 cubicFreq :=
  checkTorusCertificateV2_sound routeBRefinedG toyB3_refinedBG_passes toyCert3_freq (by
    have h : ((toyB3.params.γ : ℚ) : ℝ) = 1 / 12 := by
      rw [show toyB3.params.γ = 1 / 12 by decide +kernel]; norm_num
    have ht : ((toyB3.params.tau : ℕ) : ℝ) = 2 := by
      rw [show toyB3.params.tau = 2 by decide +kernel]; norm_num
    rw [h, ht]
    exact cubicFreq_isDiophantine_twelfth)

/-! ### The threshold -/

theorem toyB3_threshold_fibered :
    refinedBCoreG 3 (b3ParamsAt (5 / 10 ^ 23) (1 / 10 ^ 9)) toyB3.freqBox (b3Wit (14 / 10 ^ 17)) =
      true :=
  b3_core_of (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (b3_sitesOk _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl rfl)
    (by decide +kernel) (by decide +kernel)

/-- The classical sites fail at err `5·10⁻²³` at this one `X⋆` (the "every `X⋆`" half is a sweep;
see the module docstring). -/
theorem toyB3_threshold_classical_fails :
    refinedBCoreG 3 (b3ParamsAt (5 / 10 ^ 23) (1 / 10 ^ 9)) toyB3.freqBox
      (b3WitClassical (9 / 10 ^ 18)) = false := by
  decide +kernel

theorem toyB3_threshold_classical :
    refinedBCoreG 3 (b3ParamsAt (5 / 10 ^ 24) (1 / 10 ^ 9)) toyB3.freqBox
      (b3WitClassical (9 / 10 ^ 18)) = true := by
  decide +kernel

end KAM.CertificateSharp.V2

end
