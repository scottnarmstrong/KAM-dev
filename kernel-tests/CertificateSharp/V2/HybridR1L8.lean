/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Frozen
public import KAM.CertificateSharp.V2.Tests.HybridR1L8Data

/-!
# The hybrid test on R1's L = 8 candidate: the restarted run (package C8d)

**Not built** (R1-scale; `kernel-tests/` is outside the library). It imports
`KAM.CertificateSharp.V2.Tests.HybridR1L8Data` by module path: place `HybridR1L8Data.lean` back
under `KAM/CertificateSharp/V2/Tests/` to compile, as `kernel-tests/README.md` says.

The finite candidate `K̂ = r1HybEmb` (R1, design package, `L = 8`) has error `e = 4.32·10⁻⁶`, far
above the route-A′ threshold `1.55·10⁻¹¹` (`Tests/RefinedRefR1`). The hybrid applies route A′ to
`K̂₁ = K̂ + ΔK̂` (`ΔK̂ = r1HybStep`, the finite Newton step) and transfers the conclusion back to
`K̂` (`docs/campaign/design/hybrid/format.md`, checks H0–H5). The exact mirror
`scripts/apost_sharp/hybrid_mirror.py` passes H0–H5 on
`docs/campaign/design/hybrid/hybrid-R1-L8.json`, with restarted error `e₁ = 5.19·10⁻¹²` against
`e₁* = 1.54·10⁻¹¹` (margin `+0.47` decades).

This module is check H5 without its sites: the restarted route-A′ core at `r1HybParams1` with the
witness `r1HybWitR`. `r1Hyb_refinedCoreR_of_sites` reduces `refinedCoreR` to `sitesOk`;
`Tests/HybridR1L8Core` closes `sitesOk` from the base run's certified bites (`ρ₁ = ρ`, so the
schedule and the constants are the base run's).

What this does and does not show:

* `wfOk`, `okR`, `budgetOk`, the classical tail and `finalOkA` of the restarted run are decided;
* the transferred claim `r1HybClaim` and `r1HybParams1` are the producer's numbers. Checks H0–H4
  (the step claims against `r1HybStep`, the frames, `e₁`, the torsion, the consistency of
  `r1HybParams1` with the base) are C8c's certifier, not yet written; the mirror checks them
  exactly, except the kernel-only claims (`lE`, `dE0`, `o0`, `o1`, `lH` and their ℝⁿ forms), which
  are floating values × 1.10 (format.md §6);
* the base claim the transfer starts from is `r1Claim` (design data, sampled sups × 1.05).

Kernel cost (one niced process; **not measured**, this module is never built here):

* the five decides: C6L8 measured `okR`, `budgetOk`, `wfOk`, the tail, `finalOkA` and the rejection
  of `Tests/RefinedRefR1` together at about 1 s. The rationals here are larger (`r1HybParams1` has
  denominators up to `10²⁴`, `X⋆ = 19934881/125`), so expect seconds;
* peak RSS about that of the imports (`Tests/Frozen`: 2.2 GB): expected ≤ 3 GB.
-/

@[expose] public section

namespace KAM.CertificateSharp.HybridR1Test

open KAM.Certificate KAM.CertificateSharp.V2

/-- `sitesOk` reads only `n`, `τ`, `kp`, `ρ`, `ρ∞`, `c` and `c̄` of the run. -/
theorem hyb_sitesOk_congr {Q Q' : NumQ} {J : ℕ} {box : FreqBox} {κ γ : ℚ}
    {sites : List (Option BiteWit × Option BiteWit)} (hn : Q.n = Q'.n) (hτ : Q.τ = Q'.τ)
    (hkp : Q.kp = Q'.kp) (hρ : Q.ρ = Q'.ρ) (hρi : Q.ρinf = Q'.ρinf) (hc : Q.c = Q'.c)
    (hcb : Q.cbar = Q'.cbar) : sitesOk Q J box κ γ sites = sitesOk Q' J box κ γ sites := by
  simp only [sitesOk, NumQ.δ, NumQ.δ0, NumQ.b, NumQ.r, hn, hτ, hkp, hρ, hρi, hc, hcb]

/-- The restarted witness of stage 2, for given sites. -/
def r1HybBase (sites : List (Option BiteWit × Option BiteWit)) : RefinedWit where
  core := r1HybCore
  R := r1HybClaim
  κ := r1Kappa
  sites := sites

/-- The restarted route-A′ witness (lever L8′; `bF`, `bT` are those of `r1RefinedWitR`). -/
def r1HybWitR (sites : List (Option BiteWit × Option BiteWit)) : RefinedWitR where
  base := r1HybBase sites
  bF := 1177 / 5000000
  bT := 99089 / 1250000

/-- The numbers of the restarted run (they do not depend on the sites). -/
def r1HybQ : NumQ := (r1HybBase []).num 2 r1HybParams1 r1Box

theorem r1HybBase_num (sites : List (Option BiteWit × Option BiteWit)) :
    (r1HybBase sites).num 2 r1HybParams1 r1Box = r1HybQ := rfl

theorem r1Hyb_wf : r1HybQ.wfOk = true := by decide +kernel

theorem r1Hyb_ok : r1HybQ.okR (1177 / 5000000)
    (capRQ r1HybQ r1HybParams1.μ r1HybParams1.nuRay (99089 / 1250000))
    (initRQ r1HybClaim.bL r1HybClaim.bN r1HybClaim.bNt r1HybParams1.σK r1HybParams1.σB
      r1HybParams1.μ) r1HybCore.Xs = true := by
  decide +kernel

theorem r1Hyb_budget : r1HybQ.budgetOk (r1HybParams1.σT - r1HybParams1.μ) r1HybClaim.bT
    (1177 / 5000000) (99089 / 1250000) = true := by
  decide +kernel

theorem r1Hyb_tail : classicalOk 2 1 4 (r1HybQ.δ 5) r1HybQ.ctail = true := by decide +kernel

theorem r1Hyb_final : finalOkA r1HybQ r1HybParams1 r1Box r1HybCore.Xs = true := by decide +kernel

/-- **H5 on R1's L = 8 candidate, given the sites**: the restarted run passes at
`e₁ = 5.19·10⁻¹²`. -/
theorem r1Hyb_refinedCoreR_of_sites {sites : List (Option BiteWit × Option BiteWit)}
    (hs : sitesOk r1HybQ 4 r1Box r1Kappa r1HybParams1.γ sites = true) :
    refinedCoreR 2 r1HybParams1 r1Box (r1HybWitR sites) = true :=
  refinedCoreR_of (by norm_num [r1HybWitR, r1HybBase, r1HybCore]) r1Hyb_wf r1Hyb_ok r1Hyb_budget
    hs r1Hyb_tail r1Hyb_final

/-- The margin: with three times the closeness budget, `finalOkA` still passes at
`e = 1.5·10⁻¹¹`. -/
theorem r1Hyb_final_room :
    finalOkA r1HybQ { r1HybParams1 with err := 15 / 10 ^ 12, disp := 3 * r1HybParams1.disp }
      r1Box r1HybCore.Xs = true := by
  decide +kernel

/-- … and fails at `e = 1.55·10⁻¹¹`: the smallness `e < X⋆ γ⁴ δ₀^{4τ}` is the binding comparison. -/
theorem r1Hyb_final_rejects :
    finalOkA r1HybQ { r1HybParams1 with err := 155 / 10 ^ 13, disp := 3 * r1HybParams1.disp }
      r1Box r1HybCore.Xs = false := by
  decide +kernel

end KAM.CertificateSharp.HybridR1Test

end
