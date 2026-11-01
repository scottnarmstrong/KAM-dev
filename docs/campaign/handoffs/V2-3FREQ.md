# V2-3FREQ: sharp small-divisor sites for three frequencies

Branch `v2-3freq`, worktree `/home/scott/KAM-dev-worktrees/v2-3freq`, from `origin/main` at
`f80bdf6e`. Brief `~/kam-tools/briefs/V2-3FREQ.md` (improvement #4 of
`CERTIFIER-V2-IMPROVEMENTS.md`). Design: [`docs/campaign/design/V2-3FREQ.md`](../design/V2-3FREQ.md).

## Outcome

- **Additive only.** Relative to the merge base `f80bdf6e`, the branch adds 10 Lean modules. The
  only modified Lean file is the generated root `KAM/Root/CertificateSharp.lean`, written by
  `gen_root_imports.py`. No existing file under `KAM/` changed: `SmallDivQ.lean`, `Majorants.lean`,
  `RouteB*.lean` and the rest are imported read-only by the new engines. This was rechecked against
  the tightened rule (`git diff --name-status $(git merge-base HEAD origin/main) -- KAM`: `A` lines
  plus `M KAM/Root/CertificateSharp.lean` only).
- **Sharp sites for `n = 3`, any `τ`, with a proved infinite tail** (`fiberSiteOk`,
  `sdConst_ray_of_fiberSiteOk`).
  - The clock coordinate may be exact or enclosed.
  - The finite part is a kernel walk over the `2N(N+1)` fibres of `ω' ∈ ℝ²`, in integer fixed
    point with outward rounding.
  - The tail beyond `N` is `KAM.sdTail_le` at the certified `(γ/κhi, τ)`.
- **Engines.** `siteOkG` contains `siteOk`, and `sdConst_of_siteOkG` has the shape the v2 theorems
  consume. Two new engines use it: `routeARefinedG` and `routeBRefinedG`, combined in `routeAV2G`
  and `routeV2G`. Old refined witnesses map to new ones with the same verdict
  (`refinedCoreG_ofRefined`, `refinedBCoreG_ofRefined`), so the new engines are never worse.
- **Diophantine witnesses.** For a real cubic irrational there is a norm-form theorem and a
  rational checker (`cubicDioOk`, `isDiophantine_of_cubicDioOk`). It covers
  `ω = D⁻¹ A (1, θ, θ²)` for an integer matrix `A`, i.e. every coordinate used, with no complex
  conjugates and no transfer loss. Transfer lemmas: `isDiophantine_smulT` (scaling, any `τ`) and
  `isDiophantine_mono`.
- **A genuine 3-frequency example.** T3 (`toyCert3`, frequency `(∛2/2, ∛4/2, 1/2)`, `τ = 2`) passes
  the whole v2 certifier with fibered sites, by `decide +kernel`; `toyCert3_refinedG_torus` gives
  `CertifiedTorus toyCert3 cubicFreq`. The Diophantine premise comes from the new cubic theorem
  (`γ = 0.198`, against `1/12` from the landed special argument).
- **Python mirror** (`scripts/certifier/fiber3.py`) and **cross-language test**
  (`scripts/certifier/fiber3_xlang.py`). The test writes `Tests/Fiber3XLang.lean`: 25 kernel-decided
  values and one sharded walk, with exact boundary cases on both sides; one-unit mutations are caught.

## V2-3FREQ-FIX (audit AUDIT-V2-3FREQ-1: PASS WITH CHANGES, all LOW)

- **L2.** `origin/main` (`aaf1f3b0`) merged into `v2-3freq` (merge `7bde5002`). The only conflict
  was the generated root `KAM/Root/CertificateSharp.lean` (main's `Frame.MajorantsLN` beside
  `Freq.CubicNorm`). It was resolved by regenerating with `python3 -I scripts/gen_root_imports.py`
  (`--check` exit 0); the regenerated root has both entries. After the merge
  `git merge-tree $(git merge-base HEAD origin/main) origin/main HEAD` shows no conflict, and the
  branch still modifies no existing Lean file (only the generated root).
- **L1.** The threshold statements now say that the kernel theorems are about one `X⋆` each and
  that "no classical `X⋆` passes" is a sweep. They quote the audit's last passing values (route A
  classical `5.5·10⁻¹⁴`, route B classical `8.0·10⁻²⁴`, route B fibered `1.1·10⁻²²`). The same
  wording is in the docstrings of `Tests/Fiber3Toy.lean` and `Tests/Fiber3ToyB.lean`.
- **L3.** `Tests/Fiber3ToyB.lean` is in the files list, its memory is corrected (3.09 GB), and the
  suggested erratum docstring has the `γ > 0` qualifier.
- **Optional saving, done.** `toyCert3_refinedG_passes` is assembled from parts
  (`checkTorusCertificateV2_routeARefinedG_of`): the landed sub-checks come from
  `toyCert3_passes` (`landedBase_check_of_checkTorusCertificate`), and the core from
  `toyCert3_refinedCoreG`. The module now takes 11 s instead of 19 s, peak 2.55 GB instead of
  2.9 GB.
- **Rebuilt after the merge.** `Fiber.RouteAG`, `Tests.Fiber3Toy`, `Tests.Fiber3ToyB`,
  `Tests.Fiber3XLang` and `Tests.Fiber3RouteB` all report `Build completed successfully`, with no
  warnings in the new modules.

## Gain on the example (T3, route A refined, same data otherwise)

| Bite | Certified sharp `c` (fibres) | Exact-S float `c` | Classical `c♮(3,2,b)` | Factor |
|---|---|---|---|---|
| `b = 1` (`δ₀`, `b₀`, `b₁`) | `4.909·10⁻⁴` (12) | `2.82·10⁻⁴` | `0.0783` | 159 |
| `b = 1/2` (`δ₁`) | `2.853·10⁻³` (24) | `1.65·10⁻³` | `0.0629` | 22 |
| `b = 1/4`, `1/8`, `1/16`, `1/32`, `1/64` (mirror) | `3.88, 3.32, 2.94, 2.64, 2.37 ·10⁻³` (112–26,680) | | `0.0535 … 0.0429` | 14–18 |

**Threshold (largest invariance error the refined core accepts, at T3's parameters, caps 8.05):**

- Classical sites: the last error passing is `5.5·10⁻¹⁴` (`X⋆ ≈ 1.1·10⁻⁹`); `5.6·10⁻¹⁴` fails.
- Fibered sites: the last error passing is `6.1·10⁻¹²` (`X⋆ ≤ 1.27·10⁻⁷`); `6.2·10⁻¹²` fails.
- Gain: **about 2.0 orders**. These thresholds are sweeps, not kernel theorems: the mirror
  (`v2_q.py` with the certified constants) and the audit's `#eval` sweeps of the Lean
  `refinedCoreG` (AUDIT-V2-3FREQ-1, check 4), whose last passing values are quoted here.
- The kernel theorems are statements at one `X⋆` each:
  - `toy3_threshold_fibered`: err `5·10⁻¹²` passes with fibered sites at `X⋆ = 1.2·10⁻⁷`;
  - `toy3_threshold_classical_fails`: the same err fails with classical sites **at that `X⋆`**;
  - `toy3_threshold_classical`: classical sites pass at `5·10⁻¹⁴`.
- That no classical `X⋆` passes at `5·10⁻¹²` is the sweep's statement: no `X⋆` in
  `[10⁻¹², 10⁻⁶)` passes, on a grid of relative step at most 2 % (audit check 4).

## Part B (owner question 1 answered: yes): route B on T3 at `ρ = 1`

`KAM/CertificateSharp/V2/Tests/Fiber3ToyB.lean` (new). `toyB3` is T3 on the strip `ρ = 1`,
`ρ∞ = 1/100`, with the strip weight `540 ≥ e^{2π}`, exactly as `toyB` is T2's. Every other datum is
T3's: `n = 3`, `τ = 2`, `cubicFreq`, and the landed sub-checks pass.

- **Sites.** Route B's schedule (`a = 2`, `kp = 2`) has six sites, all fibered. Each is decided by
  the kernel on its own and assembled with `NumBQ.sitesOkG_of`:

  | Bite | Fibres | Certified `c` | Classical `c` | Factor |
  |---|---:|---|---|---:|
  | `δ₀ = 33/200` | 220 | `3.60·10⁻³` | `0.0499` | 14 |
  | split `11/100` | 544 | `3.21·10⁻³` | `0.0475` | 15 |
  | full `1` | 12 | `4.91·10⁻⁴` | `0.0783` | 160 |
  | `δ₁ = 33/400` | 1,012 | `3.04·10⁻³` | `0.0462` | 15 |
  | split `11/200` | 2,244 | `2.89·10⁻³` | `0.0449` | 16 |
  | full `101/200` | 24 | `2.82·10⁻³` | `0.0630` | 22 |

- **Torus.** `toyB3_refinedBG_passes` is the whole v2 certifier with `routeBRefinedG`, assembled
  from its parts (`checkTorusCertificateV2_routeBRefinedG_of`, `refinedBCoreG_of`).
  `toyB3_refinedBG_torus : CertifiedTorus toyB3 cubicFreq`.
- **Threshold.** The largest `X⋆` of route B's Newton conditions, by `#eval` of the same Lean
  tests, is `10^−15.85` with fibered sites against `10^−17.02` with classical ones. By the audit's
  `#eval` sweeps of `refinedBCoreG`, the last invariance error passing is `1.1·10⁻²²` (fibered)
  against `8.0·10⁻²⁴` (classical): **about 1.14 orders**. These thresholds are sweeps, not kernel
  theorems. The kernel theorems are statements at one `X⋆` each:
  - `toyB3_threshold_fibered`: err `5·10⁻²³` passes with fibered sites at `X⋆ = 1.4·10⁻¹⁶`;
  - `toyB3_threshold_classical_fails`: the same err fails with classical sites **at
    `X⋆ = 9·10⁻¹⁸`** (near their largest `X⋆`);
  - `toyB3_threshold_classical`: classical sites pass at `5·10⁻²⁴`.
  - That no classical `X⋆` passes at `5·10⁻²³` is the sweep's statement: none in `[10⁻²¹, 10⁻¹⁴)`
    passes (audit check 4).
- **New lemmas** in this branch's own `Fiber/RouteBG.lean`: `NumBQ.sitesOkG_of`, `refinedBCoreG_of`
  and `checkTorusCertificateV2_routeBRefinedG_of`. They are generic. The last one avoids a `show` on
  the concrete certificate, which hit the default recursion depth. No limit was raised.
- **Cost.** The module builds in 22 s. Its peak RSS is 3.09 GB measured by
  `lake env lean` (the audit's 3.09 GB; 3.08 GB here); `lake build` reports 2.75 GB. The largest
  single site is 2,244 fibres.
- **Axioms.** `[propext, Classical.choice, Quot.sound]` for all of the above.
- **Deferred to Scott, not started** (orchestrator, recorded): owner question 2 (bulk bound for
  far-from-resonance fibres) and owner question 3 (clock index as witness data).

## SJS planar frequencies (estimate, `docs/explorations/sjs-plan.md`)

> **Correction (1 November 2026, V2-BULK; see `docs/campaign/handoffs/V2-BULK.md`).** Two figures in
> this section are wrong.
>
> 1. **Shard counts, last column, too high by about 4×.** They assumed 2,500 fibres per 4 GB
>    declaration on a 3.39 GB import base. That base was measured on a non-module scratch file,
>    which loads all private data. A `lake build` module importing `Fiber/Site3` or `Fiber/Shard`
>    has a base of about 1.5–1.6 GB, so about 11,000 fibres fit per 4 GB shard (215 KB per fibre).
>    The corrected 4 GB shard counts are about 307, 1,275 and 5,278 for the three cubic-γ rows, and
>    256 for the FH row. The CPU column is unaffected.
> 2. **`N` at the third bite (`6.6·10⁻⁴`).** `N = 5,422` came from the float tail. With the landed
>    fixed point at `P = 64`, `powUp` cannot go below `2⁻⁶⁴`, and that bite needs
>    `E^{N+1} ≈ 3·10⁻²⁰ < 2⁻⁶⁴`, so witnesses there need `P ≥ 70`. With `P = 128` the exact `N` is
>    5,387, and the first two rows become 1,298 and 2,647. Both points also apply to
>    `docs/campaign/design/V2-3FREQ.md` §4.

Inputs:

- `ω = (0.0839549, 0.0338240, −1.85008·10⁻⁵)/2π` (period-1).
- Clock = the fast coordinate, reordered last, so `ω' = (0.40289, −2.2036·10⁻⁴)`.
- `S(ω, b)` from `scripts/sjs/results/S3_cache.json`, at bites `b = ρ/6, ρ/12, ρ/24`.
- Proved tail at `τ = 2`, requiring `T̂ ≤ 10⁻³ S`.

| `γ` (FH units) | bite `b` | `N` | fibres `2N(N+1)` | kernel CPU (1.2 ms/fibre) | shards ≤ 4 GB / ≤ 10 GB |
|---|---|---:|---:|---:|---:|
| `2.8·10⁻⁷` (cubic, plan's 10⁻⁸ row) | `2.65·10⁻³` | 1,310 | `3.4·10⁶` | 1.1 h | 1,374 / 115 |
| | `1.33·10⁻³` | 2,644 | `1.4·10⁷` | 4.7 h | 5,595 / 467 |
| | `6.6·10⁻⁴` | 5,422 | `5.9·10⁷` | 19.6 h | 23,523 / 1,961 |
| `1.69·10⁻⁶` (FH) | `2.65·10⁻³` | 1,184 | `2.8·10⁶` | 0.9 h | 1,123 / 94 |

Threshold gain for SJS, from the plan's own mirror (`scripts/sjs/results/sjs_thresholds.json`,
route B, τ = 2):

- With FH's γ: classical sites `10^−53.15`, frequency-specific on 2 stages `10^−49.76`.
  **Gain 3.4 orders.**
- With the numerical γ: `10^−51.07` → `10^−48.46`. **Gain 2.6 orders.**

This branch supplies exactly that checker (`routeBRefinedG` with `.fiber` sites). Certifying it
needs the walks above, sharded (`Fiber/Shard.lean`) and run as opt-in application builds. The plan's
"9·10³ near-resonant fibres" counts only fibres near resonance; the walk visits all of them.
A bulk bound for far fibres (owner question 2) would reduce the cost by orders of magnitude.

## Files

New Lean modules (all under 600 lines, ≤ 100 columns):

- `KAM/CertificateSharp/V2/Fiber/TailTau.lean` (102): `tailQ`, `sdTail_le_tailQ`, `expLowQ`.
- `KAM/CertificateSharp/V2/Fiber/Enum2.lean` (582): walk, fixed point, dyadic box, mode facts,
  kernel forms, `smallDivisorSum_snoc2_le_walk`.
- `KAM/CertificateSharp/V2/Fiber/Site3.lean` (326): `fiberSiteOk` and soundness on the ray,
  `SiteWitG`, `siteOkG`.
- `KAM/CertificateSharp/V2/Fiber/RouteAG.lean` (256): `routeARefinedG`, `routeAV2G`, `checkTorusCertificateV2_routeARefinedG_of`,
  `landedBase_check_of_checkTorusCertificate`.
- `KAM/CertificateSharp/V2/Fiber/RouteBG.lean` (279): `routeBRefinedG`, `routeV2G`, `NumBQ.sitesOkG_of`,
  `refinedBCoreG_of`, `checkTorusCertificateV2_routeBRefinedG_of`.
- `KAM/CertificateSharp/V2/Fiber/Shard.lean` (75): `balFold_succ_of`, `fiberSiteOk_of`.
- `KAM/CertificateSharp/Freq/CubicNorm.lean` (454): the cubic norm form and `cubicDioOk`.
- Tests:
  - `KAM/CertificateSharp/V2/Tests/Fiber3Toy.lean` (202): T3 end to end (route A).
  - `KAM/CertificateSharp/V2/Tests/Fiber3ToyB.lean` (279): `toyB3` (T3 at `ρ = 1`) end to end (route B).
  - `KAM/CertificateSharp/V2/Tests/Fiber3XLang.lean` (generated).
  - `KAM/CertificateSharp/V2/Tests/Fiber3RouteB.lean`: toy B through `routeBRefinedG`.

Generated: `KAM/Root/CertificateSharp.lean` (by `scripts/gen_root_imports.py`).

Scripts: `scripts/certifier/fiber3.py` (mirror, producer, cubic check, estimates) and
`scripts/certifier/fiber3_xlang.py` (cross-language test generator and `--check`).

Docs: `docs/campaign/design/V2-3FREQ.md` and this handoff.

## Approach

1. **Real analysis reused, not reproved.** `KAM.smallDivisorSum_snoc_le_fiber` (any `m`, any
   `τ`), `KAM.sdTail_le`, `sdSum_ray_le`, `isDiophantine_ray`, `sdConst_of_sdSum` and
   `smallDivisorSum_smul` were already general. Only the rational layer was specialised to `τ = 1`
   and `n = 2`. Note that `τ = 1` is empty in `ℝ³` by Dirichlet, so `sdsFiberBound_sound` at
   `m = 2` has an unsatisfiable premise.
2. **Clock.**
   - `ω* = ω*₂ (ω', 1)`, with `ω'` enclosed by interval division (`abs_div_sub_div_le`).
   - `(ω', 1)` is `(γ/κhi, τ)`-Diophantine (`clock_reduce`).
   - `S(ω*, b) ≤ κlo⁻² S((ω',1), b)`.
3. **Walk.**
   - Rows and columns of the diamond `|a| + |b| ≤ N` by bisection.
   - Soundness by an injection of `modeBox 2 N` into the cells (`walk2_sound`). Generic in the
     mode function; a failed mode fails the walk.
4. **Cost engineering**, driven by measurements:
   - Exact rationals on the certificate's box: 6.5 ms and 0.8 MB per fibre.
   - Integer fixed point on a dyadic box: 2.4 ms and 340 KB.
   - Kernel forms (`Nat.shiftLeft` for `2^P`, `Nat.blt`/`cond`, `Int.mul`): **1.2 ms and
     215 KB.**
   - Mathlib's `Monoid.npow` path for `2 ^ P` costs 0.2 ms per occurrence in the kernel.
   - `mode3K_eq` and `powUpK_eq` tie the kernel forms to the readable forms used in proofs.
5. **Cubic witnesses.**
   - The rational root theorem gives a finite no-root check.
   - Elementary independence of `1, θ, θ²` (no minimal polynomials).
   - `β(u) Y(u) = N(u)` by `linear_combination` with the sympy quotient.
   - `N(u) ≠ 0` via `Matrix.exists_mulVec_eq_zero_iff` and independence.
   - `Y(Aᵀk) = kᵀ (A H Aᵀ) k`, bounded entrywise on the θ enclosure.
6. **Engines.** Copies of `refinedCore_sound` and `refinedBCore_sound` with the site step replaced.
   Each new module is imported only by new engines and tests.

## Decisions (overnight, conservative, recorded)

- The clock is coordinate 2 (the last), as in the lunar specialisation. An application orders its
  frequency vector accordingly; a permuted torus is a different certificate.
- The fixed-point precision `P` and the dyadic scale `q` are witness data (64 on T3). The producer
  chooses them; the checker only checks.
- The walk is implemented for `m = 2` only (`n = 3`). The real theorem and the tail are general.
- No edit to any existing file. `SiteWitG` is a new inductive, not an extension of
  `Option BiteWit`.

## Checks (exact commands and output)

- `nice -n 5 lake build KAM.CertificateSharp.V2.Tests.Fiber3Toy`
  - Before the fix: `Built KAM.CertificateSharp.Freq.CubicNorm (4.3s)`, `… Fiber.Enum2 (6.0s)`,
    `… Fiber.Site3 (4.6s)`, `… Tests.Fiber3Toy (19s)`; 32.6 s wall, max RSS 2.9 GB.
  - After V2-3FREQ-FIX (landed sub-checks reused from `toyCert3_passes`):
    `Built KAM.CertificateSharp.V2.Tests.Fiber3Toy (11s)`, `Build completed successfully
    (3524 jobs)`; 12.8 s wall, max RSS 2.55 GB.
- `nice -n 5 lake build KAM.CertificateSharp.V2.Tests.Fiber3XLang`: `Build completed successfully`;
  3.7 s, 0.88 GB.
- `nice -n 5 lake build KAM.CertificateSharp.V2.Tests.Fiber3RouteB`:
  `Build completed successfully (3583 jobs)`.
- `nice -n 5 lake build KAM.CertificateSharp.V2.Fiber.RouteBG`: `Build completed successfully`.
- No warnings in the new modules (lint warnings were cleaned).
- `python3 -I scripts/certifier/fiber3_xlang.py --check`: `fiber3_xlang: the Lean module matches the
  mirror`. Mutation test: one expected `powUpK` value +1 → 2 build errors; regenerated → passes.
- `python3 -I scripts/gen_root_imports.py --check`: exit 0.
- `scripts/lint_sources.sh`: `check_lean_modules: PASS (3668 Lean files, …)` and
  `FROZEN-ANCHOR GUARD OK`; no line over 100 columns.
  - **Fails at the ABI step only**: `object file …/KAM/Frozen/Planetary/Theorems/
    FixedSunPlanetaryKAM.olean … does not exist`.
  - That frozen anchor and its provider closure (30+ `KAM.Planetary.*` modules) were never built in
    this worktree's `.lake` snapshot. `lake build … --no-build` lists them.
  - This is unrelated to the branch. I did not build that closure; the orchestrator's checkout has
    it.

## `#print axioms`

All of the following give `[propext, Classical.choice, Quot.sound]`:
`sdTail_le_tailQ`, `walk2_sound`, `smallDivisorSum_snoc2_le_walk`, `sdConst_ray_of_sdSum_le`,
`sdConst_ray_of_fiberSiteOk`, `sdConst_of_siteOkG`, `refinedCoreG_sound`, `refinedCoreG_ofRefined`,
`routeARefinedG`, `checkTorusCertificateV2_routeARefinedG_ofRefined`, `NumBQ.cert_rayG`,
`refinedBCoreG_sound`, `refinedBCoreG_ofRefined`, `routeBRefinedG`, `routeV2G`,
`isDiophantine_of_cubicDioOk`, `isDiophantine_smulT`, `cubicFreq_isDiophantine_norm`,
`toyCert3_refinedG_passes`, `toyCert3_refinedG_torus`, `toy3_threshold_fibered`,
`toy3_threshold_classical_fails`, `toyB_refinedBG_torus`.

`mode3K_eq` gives `[propext]`.

## Measurements

- **Fibered site on T3, full `fiberSiteOk` in the kernel:**

  | Bite | Fibres | Kernel time |
  |---|---:|---:|
  | `b = 1` | 12 | 0.04 s |
  | `b = 1/2` | 24 | 0.07 s |
  | `b = 1/4` | 112 | 0.21 s |
  | `b = 1/8` | 420 | 0.67 s |

- **Final walk, kernel only** (import base 3.39 GB RSS):

  | Fibres | Kernel time | Peak RSS |
  |---:|---:|---:|
  | 420 | 0.49 s | 3.48 GB |
  | 1,012 | 1.13 s | 3.62 GB |
  | 1,860 | 2.50 s | 3.79 GB |

  So about 1.2 ms and 215 KB per fibre. Machine load from other sessions varied by about ±30 %.

- **Exact-rational first attempt (abandoned):** 1,860 fibres took 12 s at 5.1 GB; 6,612 fibres took
  58 s at 9.1 GB.

  > **Memory-rule note:** two probes of the abandoned exact-rational form exceeded the 4 GB
  > per-process rule (5.1 GB and 9.1 GB, both under the 10 GB guard). Every probe after that ran
  > under a 4 GB RSS kill-wrapper.

- **Toy T3 module:** whole v2 certifier plus threshold checks in 11 s (19 s before reusing
  `toyCert3_passes`).

## Owner questions

1. **Route B with three frequencies.** Answered: yes. Done in Part B (`toyB3`).
2. **SJS scale (deferred to Scott).** Is a bulk bound for far fibres (`|x + p| ≥ η`, summed per shell
   `|k'|₁ = s` analytically) wanted? It would turn `3·10⁶–6·10⁷` walked fibres into about `10⁴`
   near-resonant ones (the plan's count), at the price of a near-resonance enumeration certificate
   (e.g. continued-fraction / three-distance data for `ω'`).
3. **Clock choice (deferred to Scott).** The checker fibres over coordinate 2. For SJS, should applications reorder the
   frequency vector so the fast coordinate is last (assumed in the estimate), or should the clock
   index become witness data?

### Cross-session notes (v2-fixes-96, branch `v2-sites`, not landed; recorded, no action taken)

- **Negative clock.** `fiberSiteOk` requires `clockC − clockR > 0`. A certificate whose last
  coordinate is negative can use V2-SITES-SIGN's `sdConst_ray_of_neg` (SDConst level, from
  `cohR_neg`) with `negBox`/`freqEncloses_negBox`/`isDiophantine_neg`: run `siteOkG` on
  `negBox box` and transfer. Nothing changes on this branch; it needs both branches landed.
- **Question 3 (clock index).** v2-fixes-96 recommends keeping the clock last and letting the
  application order its coordinates. A permutation is a change of variables on the torus, so an
  SDConst-level lemma is real work. The sdSum-level `sdSum (ω ∘ σ) = sdSum ω` is the easy part. The
  decision stays with Scott and the orchestrator.
- **No overlap.** Their `SiteShard.lean` shards the `n = 2` `balSum`/`balAll` walk; `Fiber/Shard.lean`
  shards `balFold`/`walk2`. They independently measured 0.86 MB per mode for exact rationals on
  LG00, matching the 0.8 MB per fibre measured here.

## Uncertainties

- The SJS numbers are estimates.
  - `N` comes from the exact tail formula with `T̂ ≤ 10⁻³ S`.
  - The cost extrapolates the T3 per-fibre measurement. SJS boxes need a larger `q` (tighter
    enclosure), which makes integers longer and the per-fibre cost somewhat higher.
  - Route B also has split-bite sites (bite `2δ/3` at `τ = 2`): about 2.25× the fibres of the `δ`
    site.
- The threshold figures are sweeps (the mirror's and the audit's `#eval` sweeps; last passing values
  route A `6.1·10⁻¹²` fibered and `5.5·10⁻¹⁴` classical, route B `1.1·10⁻²²` and `8.0·10⁻²⁴`).
  The kernel theorems are statements at one `X⋆` each: the fibered pass and the classical failure
  at the same error, and the classical pass at the lower error.

## Suspected errata and deviations

- `KAM/CertificateSharp/Freq/SmallDivisorFiber.lean` (module docstring and `sdsFiberBound_sound`)
  presents the fibered checker as general in `m`. Its premise
  `IsDiophantine (d.γ : ℝ) 1 (Fin.snoc ω' 1)` is unsatisfiable for `m ≥ 2` (Dirichlet: every
  `ω ∈ ℝ³` has `|k·ω| ≤ C|k|₁⁻²` infinitely often). The theorem is correct but vacuous beyond
  `m = 1`. Not a soundness issue. **Suggested docstring sentence** (not applied; the file is
  read-only for this branch): "useful only for `m = 1`: a `(γ, 1)`-Diophantine vector of `ℝ^{m+1}`
  with `γ > 0` exists only for `m ≤ 1`." (For `γ ≤ 0` the premise holds trivially; `fiberCheck`
  requires `0 < γ`.)
- **Deviation from the brief's wording:** the "exact sum over `0 < |k|₁ ≤ N`" is realised as the
  fibered sum over `0 < |k'|₁ ≤ N` with every `k_last` summed analytically. That is a superset of
  the box, bounded from above, plus the proved tail for `|k'|₁ > N`. The full 3-D box would be
  `≈ 4N³/3` modes.
- **Deviation from the design draft:** the walk uses a witness-supplied dyadic box and integer
  fixed point instead of the certificate's rational box. Measured: exact rationals cost 5× the time
  and 4× the memory.

V2-3FREQ DONE

V2-3FREQ-B DONE

V2-3FREQ-FIX DONE
