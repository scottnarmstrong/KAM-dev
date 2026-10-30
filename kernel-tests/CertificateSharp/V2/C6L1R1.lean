/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Engine
public import KAM.CertificateSharp.V2.Tests.Frozen

/-!
# Route A with the ℓ¹ entry on the design package R1: the numerical core (package C6L1)

**Not built** (R1-scale; `kernel-tests/` is outside the library). Run by hand, one niced process:
`nice -n 5 lake env lean kernel-tests/C6L1R1.lean`.

`l1Core` passes at `e = 6.55·10⁻¹¹` (`10^(-10.18)`), prefix 5, `X⋆ = 680000`, `ϑ = 1/32`, and fails
at `e = 6.57·10⁻¹¹` with the same witness (the smallness binds; at `X⋆ = 700000` the tail decay
`J2` fails).

What this does and does not show:

* the small-divisor sites are C6/C6L8's certified bites for `r1Box` (the ℓ¹ strip is `ρ' = 1/70`,
  so the schedule `δ_s` is theirs; the sup data are taken on `T_{1/70 + 1/10⁵}`, `r1ParamsL`);
  `Γ_∞(sω*, δ₀) ≤ 5.1732` and `Γ_∞(sω*, ρ') ≤ 3.3839` are certified by the fibered test;
* the claims `r1ClaimL` (C6's `r1Claim`) and the ℓ¹ claims are design data, **not** checked bounds:
  `|E|₁ ≤ 4.4984 e`, `|Lᵀ|₁ ≤ 1.5586`, `|Nᵀ|₁ ≤ 1.6216`, `|L|₁ ≤ 1.4284`, `|N|₁ ≤ 1.4867`,
  `|T|₁ ≤ 3.7288` are the sampled values of `scripts/apost_sharp/l1_entry_r1.py` × 1.05; no lunar
  model is run. `a_N = |Lᵀ|₁ |E|₁/e ≤ 7.0112`, `a_L = |Nᵀ|₁ |E|₁/e ≤ 7.2946` (Wiener products).

Kernel cost (one niced process):

* measured in a `.drafts` probe: `r1L1_wf`, `r1L1_ok`, `r1L1_tail`, `r1L1_final`, `r1L1_entry`
  (both `Γ_∞` tests, 754 and 86 fibers) together about 12 s, peak RSS 4.1 GB (imports included);
* **not measured, expected from C6 and C6L8:** the ten bites. C6 measured 1.2–85 s for `l = 7…12`
  (module peak 10.4 GB); C6L8 measured 4:19 and 18.8 GB for one bite at `l = 13` (`δ₄`).
  The `l = 13` bite exceeds the 10 GB per-process limit of lemma.farm: it needs a rounded
  `balBound` (C6's suggestion) or a smaller cut-off at a cost in `c(δ₄)`. With prefix 4 (no
  `l = 13` bite) the same route passes at `X⋆ = 480000`, `e ≈ 4.6·10⁻¹¹` (`10^(-10.34)`, by `#eval`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.L1

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- R1 with the sup data on `T_{1/70 + 1/10⁵}`; the ℓ¹ data on `T_{1/70}`. -/
def r1ParamsL (err disp : ℚ) : CertParams := { r1Params err disp with rho := 1 / 70 + 1 / 10 ^ 5 }

/-- C6's claim of the design package: sampled sups × 1.05. -/
def r1ClaimL : RefClaim :=
  ⟨105 / 100 * (18228 / 10000), 105 / 100 * (175 / 100), 105 / 100 * (10342 / 10000),
    105 / 100 * (18323 / 10000), 105 / 100 * (13268 / 10000), 105 / 100 * (13540 / 10000),
    105 / 100 * (13787 / 10000), 105 / 100 * (33130 / 10000)⟩

/-- C6's and C6L8's bites. -/
def r1SitesL : List (Option BiteWit × Option BiteWit) :=
  [(some ⟨970567 / 1000000, 10, 8, 545543 / 20⟩, some ⟨208937 / 250000, 7, 8, 388019 / 100⟩),
   (some ⟨1231467 / 1250000, 11, 8, 104334⟩, some ⟨914111 / 1000000, 8, 8, 109921 / 20⟩),
   (some ⟨1240699 / 1250000, 12, 8, 20686609 / 50⟩, some ⟨478003 / 500000, 9, 8, 132149 / 10⟩),
   (some ⟨498137 / 500000, 12, 8, 1699320⟩, some ⟨977669 / 1000000, 10, 8, 46455⟩),
   (some ⟨124767 / 125000, 13, 8, 6798600⟩, some ⟨247171 / 250000, 11, 8, 178853⟩)]

/-- The run of R1: prefix 5, `X⋆ = 680000`, `ϑ = 1/32`, tight caps. -/
def r1BaseL : RefinedWit :=
  ⟨⟨680000, 5, 1 / 32,
    [2978 / 10 ^ 6, 2912 / 10 ^ 6, 2900 / 10 ^ 6, 2938 / 10 ^ 6, 2939 / 10 ^ 6],
    [6745 / 10 ^ 6, 4018 / 10 ^ 6, 3122 / 10 ^ 6, 2938 / 10 ^ 6, 2906 / 10 ^ 6], 4071 / 50000,
    4816779 / 2500000, 6544409 / 10000000, 13934217 / 10000000, 1424737 / 1000000,
    14510501 / 10000000, 892983 / 250000, 4⟩, r1ClaimL, r1Kappa, r1SitesL⟩

/-- The error of the test. -/
def r1ErrL : ℚ := 655 / 10 ^ 13

/-- The witness of R1 for route A with the ℓ¹ entry. -/
def r1L1Wit : L1Wit :=
  ⟨r1BaseL,
    ⟨⟨1 / 70, 1⟩, ⟨1 / 70 - (1 / 70 - 1 / 70000) / 6, 1⟩, 44984 / 10000 * r1ErrL,
      15586 / 10000, 16216 / 10000, 14284 / 10000, 14867 / 10000, 37288 / 10000⟩,
    ⟨1095501 / 156250, 9118257 / 1250000, 37288 / 10000, 105 / 100 * (33130 / 10000),
      12933 / 2500, 33839 / 10000, some (14284 / 10000, 14867 / 10000), 3679 / 10000⟩,
    ⟨377, 2463 / 2500, 5658 / 625⟩, ⟨43, 4571 / 5000, 11843 / 2000⟩⟩

/-- The parameters of the test. -/
def r1PassL : CertParams := r1ParamsL r1ErrL (1 / 300)

/-- The numbers of the run. -/
def r1QL : NumQ := r1L1Wit.num 2 r1PassL r1Box

theorem r1L1_wf : r1QL.wfOk = true := by decide +kernel

theorem r1L1_ok : okL1 r1QL r1L1Wit.E (capQ r1QL r1PassL.μ r1PassL.nuRay)
    (initQ r1ClaimL.bL r1ClaimL.bN r1ClaimL.bNt r1ClaimL.bT r1PassL.σK r1PassL.σB r1PassL.σT
      r1PassL.μ) 680000 = true := by
  decide +kernel

theorem r1L1_tail : classicalOk 2 1 4 (r1QL.δ 5) r1QL.ctail = true := by decide +kernel

theorem r1L1_entry : entryOk 2 r1QL r1PassL r1Box r1L1Wit = true := by decide +kernel

theorem r1L1_final : finalL1 r1QL r1L1Wit.E r1PassL r1Box 680000 = true := by decide +kernel

theorem r1L1_site (s : Fin 5) :
    siteOk r1QL.n r1QL.τ 4 r1Box r1Kappa r1PassL.γ (r1QL.δ s) (r1QL.c.getD s 0)
        (r1SitesL.getD s (none, none)).1 = true ∧
      siteOk r1QL.n r1QL.τ 4 r1Box r1Kappa r1PassL.γ (r1QL.b s) (r1QL.cbar.getD s 0)
        (r1SitesL.getD s (none, none)).2 = true := by
  fin_cases s <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem r1L1_sites : sitesOk r1QL 4 r1Box r1Kappa r1PassL.γ r1SitesL = true :=
  sitesOk_of fun s hs => r1L1_site ⟨s, hs⟩

/-- **`l1Core` on R1**, at `e = 6.55·10⁻¹¹`. -/
theorem r1_l1Core : l1Core 2 r1PassL r1Box r1L1Wit = true :=
  l1Core_of (by decide +kernel) r1L1_wf r1L1_ok r1L1_sites r1L1_tail r1L1_entry r1L1_final

/-- The same witness fails at `e = 6.57·10⁻¹¹`: the smallness is the binding comparison. -/
theorem r1L1_final_rejects :
    finalL1 r1QL r1L1Wit.E (r1ParamsL (657 / 10 ^ 13) (1 / 300)) r1Box 680000 = false := by
  decide +kernel

end KAM.CertificateSharp.V2.L1

end
