# SHARP2-C6L8: lever L8′ in the v2 certifier

Branch `sharp-c6l8`, from `sharp-v2` at 2fcf73d4. Opus 5.5. No file under `KAM/Certificate/**`,
`KAM/SpinOrbit/**`, `scripts/spin_orbit/**`, `certificates/**`, `KAM/Frozen/**` or `manifest/**` changed, and
no existing V2 file was edited. `AUDIT-L8P-1` passed with no change to the statements used here.

## Result

- `routeARefinedR`: a closed `EngineV2`, sound through `Ref.iso_g1_branch_R`, with the exact rational mirror
  of `routeAOkRI`.
- `routeAV2'` adds it to the existing routes. `routeAV2` is unchanged, and
  `checkTorusCertificateV2 routeAV2' c (Sum.inl ()) = checkTorusCertificateSharp c` holds by `rfl`.
- T2: the whole certifier passes by `decide +kernel`, and `toyCert2_refinedR_torus` is a torus.
- R1: the numerical core passes in the kernel at **e = 1.55·10⁻¹¹, log₁₀ −10.81**, and rejects 1.56·10⁻¹¹.

| Route | Prefix | e passed | e rejected | log₁₀ | Status |
|---|---:|---:|---:|---:|---|
| `routeARefined` (C6) | 3 | 4.7·10⁻¹² | 4.8·10⁻¹² | −11.33 | kernel, numerical core |
| `routeARefinedR` | 5 | 1.55·10⁻¹¹ | 1.56·10⁻¹¹ | **−10.81** | kernel, numerical core |

**The R1 figure is not a torus.** As in C6, `r1Claim` is the design's data (sampled sups × 1.05), not a checked
bound, and `r1Box` is a test datum. No Ham or frame check ran on lunar models. The certified part is the
arithmetic of the test at those inputs and the ten small-divisor bounds for `r1Box`.

**Against the design's −10.95.** The two use different data: the design is a float evaluation with 5% caps, and
−10.81 uses certified constants with tight caps (each cap at `init + sum`). The 0.14 orders come from the caps,
not from the lever.

## What L8′ itself gains on R1

The move from −11.33 to −10.81 is mostly the longer prefix. The lever's part, by `#eval` of the same Lean
tests, not kernel-checked, with the certified constants of this package:

| Prefix | No lever (`okB`, tight caps, ϑ scanned) | With L8′ (`okR`) |
|---:|---:|---:|
| 3 | X⋆ = 49550 (−11.32) | 48368 (−11.33), caps tuned for prefix 5 |
| 5 | X⋆ = 90316 (−11.06), at ϑ = 1/16 | 161000 (−10.81) |

- At prefix 3 L8′ gains nothing: `J2` binds there, with the classical `ctail`.
- At prefix 5 it gains about **+0.25 orders** by this scan. The scan is a grid, not an optimum.
- C6's table has −10.94 for prefix 5 without the lever, with float constants. I did not reconcile that with my
  −11.06. Against it the lever's gain would be +0.13. So the honest range is +0.13 to +0.25, below the
  roughly 0.4 of the design's 5% caps, because tight caps already recover part of it.

The float mirror agrees on the prefix dependence (5% caps, `route_a_lean_mirror`): −11.39, −11.37, −11.37 without
the lever and −11.39, −11.04, −10.95 with it, at prefixes 3, 4, 5.

**What binds at R1:** `J2`, the tail condition. With the caps re-tuned at each X, `16 C_E x₅` is 0.8987 at
X = 161000, 0.9985 at 161530 and 1.0124 at 161600, while every stage condition and cap holds at 161600. The
witness's caps are tight at 161000, so that fixed witness already fails its caps at 161200. The budgets at
X = 161000:

| Quantity | Value |
|---|---:|
| `𝒯_ab` sum | 0.07919 |
| `b_T + 2 b_F` | 0.079742 |
| room `t - H` | 0.08135 |
| `β_T` | 0.092327 |
| max of `B_loc x_s` | 2.35·10⁻⁴ |

**No frozen-data variant.** L8′ gains nothing there: on R1's default data the mirror gives −21.07 and −21.09 with
and without the lever. So `routeAFrozen` stays as it is, and I did not write `iso_g1_v2A_default'`. That comparison
is at the mirror's 5% caps. I did not repeat it with tight caps.

## Soundness statements

```lean
theorem NumQ.okR_sound {bF : ℚ} {σ m₀ : Fin 8 → ℚ} {Xs : ℚ} (hτ : 1 ≤ Q.τ)
    (h : Q.okR bF σ m₀ Xs = true) :
    routeAOkRI Q.toNum bF (fun i => (σ i : ℝ)) (fun i => (m₀ i : ℝ)) (Xs : ℝ)

theorem NumQ.budgetOk_sound {mT iH bF bT : ℚ} (h : Q.budgetOk mT iH bF bT = true) :
    Budget Q.toNum (mT : ℝ) (iH : ℝ) (bF : ℝ) (bT : ℝ)

theorem refinedCoreR_sound (c : TorusCertificate n α) (w : RefinedWitR) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.base.R) (hF : FrameFacts c w.base.R ωstar)
    (h : refinedCoreR n c.params c.freqBox w = true) : CertifiedTorus c ωstar

def routeARefinedR : EngineV2          -- test: checkHamClaim, checkFrameMajorants, refinedCoreR

def routeAV2' : EngineV2 :=
  sharpV2.orElse ((routeAFrozen.orElse routeARefined).orElse routeARefinedR)

theorem checkTorusCertificateV2_routeAV2'_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeAV2' c (Sum.inl ()) = checkTorusCertificateSharp c := rfl
```

`refinedCoreR` is `refinedCore` with `okR` in place of `okB`, plus `budgetOk`. `sitesOk`, `classicalOk` and
`finalOkA` are C6's. The local bound needs `ch = c_{s+1}` at the bite `δ_s/2`, which is a constant of the schedule,
so no new small-divisor test is needed. `RefinedWitR` is `RefinedWit` plus the rationals `bF`, `bT`, and its numbers
are all checked by the test. In the combined engine the new route's witness is `Sum.inr (Sum.inr w)`.

## R1 witness

Prefix 5, X⋆ = 161000, ϑ = 1/200, sB 1.9294169, sT 0.65, sLt 1.3937561, sN 1.428831, sNt 1.4554674, t 3.56,
b_F = 2.354·10⁻⁴, b_T = 0.0792712, c_tail = .08142 at δ₅.

| Site | l | Bound of S | c | Source |
|---|---:|---:|---:|---|
| δ₀, δ₁, δ₂ | 10, 11, 12 | as C6 | .002978, .002912, .002900 | C6's theorems, reused by defeq |
| b₀, b₁, b₂ | 7, 8, 9 | as C6 | .006745, .004018, .003122 | C6's theorems, reused by defeq |
| δ₃ | 12 | 1699320 | .002938 | new |
| b₃ | 10 | 46455 | .002938 | new |
| δ₄ | 13 | 6798600 | .002939 | new |
| b₄ | 11 | 178853 | .002906 | new |

δ₃ and δ₄ use the cut-off one below the one that makes the tail negligible, at a cost of 1.4% in `c`. At δ₃ going to
l = 13 would gain 0.18% in X⋆ for about 3 more minutes, and δ₄ at l = 14 was not attempted.

## Kernel cost

| Item | Wall | Peak RSS |
|---|---:|---:|
| `Tests/RefinedRef` (toy, whole certifier 3 times) | 8 s | not measured |
| `Tests/RefinedRefR1` build, four new bites | 6:00 | 19.2 GB |
| one bite at l = 13 alone (`.drafts`, includes imports) | 4:19 | 18.8 GB |
| `okR`, `budgetOk`, `wfOk`, tail, final, rejection, together | about 1 s | |

The module needs `Tests/RefinedR1` built first (C6: 143 s, 10.4 GB). The machine was under load 80–110 for part of
these runs, so the wall times are upper bounds. `Tests/RefinedRefR1` is in the generated root, so a future full build
carries those 6 minutes and the 19 GB peak. Exact ℚ reached l = 13 with no rounded form of `balBound`.

## Files

New, in `KAM/CertificateSharp/V2/`, 577 lines, largest 197:
- `RouteAQRef.lean`: `StepQ.rAb`, `bLoc0`, `bLoc`, `cond0`, `rateR`; `NumQ.bLocS`, `condR`, `okR`, `budgetOk`.
- `RouteARefinedRef.lean`: `RefinedWitR`, `capRQ`, `initRQ`, `refinedCoreR`, `refinedCoreR_of`, `refinedCoreR_sound`.
- `RouteARefinedRefEngine.lean`: `refinedRefTest`, `routeARefinedR`, `routeAV2'`.
- `Tests/RefinedRef.lean`, `Tests/RefinedRefR1.lean`: the kernel tests.

Regenerated: `KAM/Root/CertificateSharp.lean`.

## Checks

- `nice -n 5 lake build KAM.CertificateSharp.V2.Tests.RefinedRef KAM.CertificateSharp.V2.Tests.RefinedRefR1`:
  `Build completed successfully (3525 jobs).`
- `#print axioms` (`.drafts`) on `NumQ.okR_sound`, `NumQ.budgetOk_sound`, `refinedCoreR_sound`, `routeARefinedR`,
  `routeAV2'`, `checkTorusCertificateV2_routeAV2'_sharp`, `toyCert2_refinedR_torus`, `toyCert2_routeAV2'_passes`,
  `r1_refinedCoreR`, `r1R_final_rejects`: `[propext, Classical.choice, Quot.sound]`.
- `sh scripts/lint_sources.sh`: exit 1 from the ABI scratch probe only (missing frozen olean of this snapshot), no line
  of `V2/`. `check_lean_modules: PASS (1640 Lean files)`, `FROZEN-ANCHOR GUARD OK`.
- Name clashes:
  - Import probe: **partial.** 1142 of the 1613 root modules imported together with no error, including my five. The
    other 471 have no olean here (358 in `KAM.Planetary`), and building them is the whole-library build the rules
    forbid.
  - Parser of fully qualified declarations over all of `KAM/`: 52 names in the 5 new files, 0 clashes. It does not see
    structure fields or auto-generated names.
- No warning from the new files, no `set_option`, no `sorry`, `native_decide`, `unsafe`, `opaque` or `axiom`. All are
  under 800 lines and 100 characters.

## Deviations

1. Sound through the branch `Ref.iso_g1_branch_R`, not `iso_g1_v2A'`, for C6's reason: `max {C₂♯, c2I}` with v1's `C₂♯`
   blocks the ray room near a refined threshold. The brief allows it.
2. No frozen-data variant, as the brief makes it conditional on a gain.
3. `routeAV2'` nests the new route inside the second summand, so that `Sum.inl ()` stays the landed certifier as the
   brief wrote it.
4. Prefix 5 rather than C6's 3, with the δ₃, δ₄ cut-offs above, because the lever gives nothing at prefix 3.

## Uncertainties

- The caps were found by a grid and a fixed-point iteration, so −10.81 is a certified value, not an optimum. Since `J2`
  binds, a longer prefix might gain more at tight caps. I did not try prefix 6: it needs δ₅ at l ≥ 14.
- The disagreement with C6's −10.94 above is not traced.
- On lunar data the lever will cost the same two extra stages, about 6 more minutes and 19 GB, and its gain there is
  not measured.
- `AUDIT-L8P-1` F1–F3 are documentation findings on the L8P handoff and the blueprint. They do not touch this package,
  and I did not edit those files.

## Suspected errata

None in pinned sources.
