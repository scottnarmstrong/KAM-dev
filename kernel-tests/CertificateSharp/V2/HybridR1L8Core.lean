/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.HybridR1L8
public import KAM.CertificateSharp.V2.Tests.RefinedRefR1

/-!
# The hybrid test on R1's L = 8 candidate: the restarted run with the base sites (package C8d)

**Not built**, and **not runnable on lemma.farm as it stands**: it imports `Tests/RefinedRefR1`
(19.2 GB, 6 min; it imports `Tests/RefinedR1`, 10.4 GB, 2.5 min) and `Tests/HybridR1L8` by module
path. Place all four (`RefinedR1`, `RefinedRefR1`, `HybridR1L8Data`, `HybridR1L8`) back under
`KAM/CertificateSharp/V2/Tests/` to compile.

The restarted strip is the base strip (`ρ₁ = ρ = 1/70`), so the restarted schedule `δ_s`, `b_s` is
the base schedule; the constants `c`, `c̄` and `γ` are the base run's too. So the five certified
sites of `r1RefinedWitR` apply verbatim (format.md §4, `"sites": "reuse-base"`):
`hyb_sitesOk_congr` moves `r1R_sites` to the restarted run. The module itself adds a congruence and
six decides on small ℚ and ℕ equalities: about the cost of its imports' `.olean` load.

What C8c adds to make the hybrid test complete (checks H0–H4 of format.md, not yet written), with
expected costs, **not measured**, from SJS-FEAS (packed product `t ≈ 1.3·10⁻⁴ S^1.9` s, model ops
220 kB per term) and C6L1 (`invarianceModel`, one coordinate at a time):

* polynomial claims `d0`, `dinf`, `d1`, `d1t`, `d0R`, `d1R`, `d1tR`: weighted norms of `r1HybStep`
  (261 half-lattice terms) and its derivative at three weights: seconds, ≤ 3 GB;
* `o0`, `o1`, `o0R`, `o1R`: the products `DK̂ᵀΩ₀DK̂`, `DK̂₁ᵀΩ₀DK̂₁` (supports ≤ 200, about 16 packed
  products): under a minute, ≤ 4 GB; one declaration per matrix entry;
* `lE`, `dE0`, `dE0R`, `lH`: the model of `Ẽ` (the invariance compose at `s₁ω*` and the jet of
  `X_H` along `K̂`, combined before the norm): minutes; one declaration per coordinate, each
  expected ≤ 6 GB;
* H1–H4: rational arithmetic on about 60 numbers: about 1 s.
-/

@[expose] public section

namespace KAM.CertificateSharp.HybridR1Test

open KAM.Certificate KAM.CertificateSharp.V2

/-- The restarted run's sites are the base run's: same strip, schedule, constants and `γ`. -/
theorem r1Hyb_sites :
    sitesOk r1HybQ 4 r1Box r1Kappa r1HybParams1.γ r1RefinedWitR.base.sites = true := by
  have hγ : r1HybParams1.γ = r1PassR.γ := by decide +kernel
  rw [hγ, hyb_sitesOk_congr (Q := r1HybQ) (Q' := r1QR) rfl (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  exact r1R_sites

/-- **H5 on R1's L = 8 candidate**: the restarted route-A′ run passes at `e₁ = 5.19·10⁻¹²`, with
the base run's certified sites. -/
theorem r1Hyb_refinedCoreR :
    refinedCoreR 2 r1HybParams1 r1Box (r1HybWitR r1RefinedWitR.base.sites) = true :=
  r1Hyb_refinedCoreR_of_sites r1Hyb_sites

end KAM.CertificateSharp.HybridR1Test

end
