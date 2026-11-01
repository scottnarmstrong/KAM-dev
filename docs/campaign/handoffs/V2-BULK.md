# V2-BULK handoff: a bulk bound for the fibres far from resonance

Date: 1 November 2026. Branch `v2-bulk` from `origin/main` at `01d36418`. Additive only: no existing
`.lean` file changes except the generated root `KAM/Root/CertificateSharp.lean`. `SmallDivQ.lean`,
`Frame/Majorants.lean` and the landed `Fiber/*` modules are byte-identical. The design is
[V2-3FREQ.md §7](../design/V2-3FREQ.md#7-v2-bulk-a-bulk-bound-for-the-fibres-far-from-resonance)
(`V2-BULK DESIGN READY` was printed before any Lean was written). This task is owner question 2 of
the V2-3FREQ handoff, decided by Scott on 2026-11-01.

## Result in one paragraph

The landed three-frequency site walks every fibre `k' = (a, b)` with `0 < |a| + |b| ≤ N`, which is
`2N(N + 1)` fibres. The bulk walk bounds whole runs of fibres instead.
- **Why runs are possible.** Along a row `a`, the distance `|x_b + p|` is affine in `b` and the weights
  are geometric in `|b|`. A run is therefore bounded from its two endpoints, with no Diophantine input.
- **Walk structure.** Rows are bisected. Near a crossing of an integer (a near-resonance) the walk
  ends in single fibres, evaluated exactly as the landed `mode3`. Elsewhere it takes long runs,
  accepted when the distance varies by at most `5/4` or when their value is negligible.
- **SJS measurements.** At the plan's first bite (`N = 1298`) the bound uses **44,568 nodes instead
  of 3.37·10⁶ fibres** and is `0.46 %` above the plain walk's sum. Kernel cost is about 1 min in
  4 shards, against 1.1 h in about 300 shards. At the third bite: 654k nodes for 5.8·10⁷ fibres,
  15 min against 19 h. That is 76–89× fewer evaluations.
- **Short of the target.** The orchestrator's target was ~10⁴. The remaining factor of about 4
  needs one more run type (owner question 1 below).

## Files (all new except the generated root)

Each module was rebuilt alone after removing its own build artifacts; time is `lake build`'s, peak
is the RSS of that module's process.

| File | Lines | Build | Peak |
|---|---:|---:|---:|
| `KAM/CertificateSharp/V2/Fiber/Bulk.lean` | 980 | 7.0 s | 1.51 GB |
| `KAM/CertificateSharp/V2/Fiber/BulkSite.lean` | 203 | 4.0 s | 1.51 GB |
| `KAM/CertificateSharp/V2/Fiber/RouteH.lean` | 506 | 4.0 s | 1.60 GB |
| `KAM/CertificateSharp/V2/Tests/BulkToy.lean` | 167 | 4.2 s | 1.65 GB |
| `KAM/CertificateSharp/V2/Tests/BulkRouteB.lean` | 116 | 1.9 s | 1.49 GB |
| `KAM/CertificateSharp/V2/Tests/BulkXLang.lean` (generated) | 253 | 4.1 s | 1.64 GB |
| `scripts/certifier/fiber3_bulk.py` (mirror, producer, SJS counts) | 414 | | |
| `scripts/certifier/fiber3_bulk_xlang.py` (writes `BulkXLang.lean`; `--check`) | 237 | | |
| `docs/campaign/design/V2-3FREQ.md` §7 (design, measurements) | +73 | | |
| `KAM/Root/CertificateSharp.lean` (generated, 6 lines added) | | | |

All Lean files are modules, at most 980 lines and at most 100 columns.

## Approach

**Run bound (`Fiber/Bulk.lean`).** A run is `b = σ(lo + i)`, `i₀ ≤ i ≤ i₁`, `σ = ±1`, on the
dyadic box `DBox2`.
- `blkK` takes `p = nearP(X(i₀))`, `Z(i) = X(i) + p 2^q` and `Rd(i) = |a| R₀ + (lo + i) R₁`.
- It checks `sameSign Z(i₀) Z(i₁)`, `Rd < |Z|` and `2(|Z| + Rd) ≤ 2^q` at both ends.
- `F = sZ − Rd` and `G = sZ + Rd` are affine in `i` (`affine_ge_min`, `affine_le_max`), so every
  fibre of the run has `Λ/2^q ≤ |x + p| ≤ 1/2`, with `Λ = min F` (`run_point`).
- The run's value `blkValK` is `mode3`'s term with weights `mulUp(powUp(j₀), G_t)` and
  `mulUp(powUp(j₀ + |p|), G_t)`.
  - `G_t ≥ 2^P Σ_{j<2^t} x^j` is a table checked once (`gTabOk0`, by doubling).
  - A single fibre (`i₀ = i₁`, `G₀ = 2^P`) gives exactly `mode3`'s value (`BulkXLang`: `xl_fibre_*`
    equals `xl_mode_*`).

**Walk.** `walkB` takes rows `a = i − N` by `balFold`.
- `rowB` splits a row into two half-rows, `b ≥ loP a` and `b ≤ −1`.
- `hrow` bisects a half-row. A node is one run if `blkK` passes and the acceptance test `accOk`
  holds: `rd·max G ≤ rn·Λ`, or value `≤ tol`. Otherwise the node splits. A single fibre must pass.
- The acceptance test affects cost and tightness only.

**Soundness.** `BCov ω' x S v` says some per-fibre `(p_k, L_k)` on the mode set `S` satisfies
`KAM.smallDivisorSum_snoc_le_fiber`'s hypotheses with summands (weights `x^j`, `x = e/2^P`) summing to
at most `v`.
- It glues over disjoint unions (`BCov.union`, `BCov.biUnion`) and passes to subsets (`BCov.subset`).
- `blkK_spec`, then `hrow_spec`, then `rowB_spec`, then `walkB_sound` give `BCov (modeBox 2 N) (s/2^P)`.
- `smallDivisorSum_snoc2_le_bulk` applies the fibered theorem with `E_j = x^j`. Its output has the
  same form as `smallDivisorSum_snoc2_le_walk`: `E₁·3.3075 + s/2^P + tailQ`.

**Site (`Fiber/BulkSite.lean`).** `bulkSiteOk` is `fiberSiteOk` with `walkB` in place of `walk2`,
plus the table checks `l < gs.length` and `gTabOk0`.
- Soundness goes through `sdConst_ray_of_snocBound`, the clock reduction and constant test shared
  with `fiberSiteOk`.
- Sharding: `bulkPreOk` with `bulkSiteOk_of`. The landed `balFold_succ_of` assembles `walkB` from
  row blocks.
- `SiteWitH` is `g (w : SiteWitG)` or `bulk (w : BulkWit)`. `sdConst_of_siteOkH` has the shape of
  `sdConst_of_siteOkG`.

**Engines (`Fiber/RouteH.lean`).**
- `routeARefinedH` and `routeBRefinedH` are the `G` engines with `siteOkH` sites. Their definitions
  and soundness proofs are copied verbatim by script (rename `G` to `H`), with
  `sdConst_of_siteOkH` at the sites.
- `RefinedWitH.ofG` and `RefinedBWitH.ofG` keep the verdict (`refinedCoreH_ofG`,
  `refinedBCoreH_ofG`).
- `routeV2H = routeV2G.orElse (routeARefinedH.orElse routeBRefinedH)` is the landed certifier at
  the sharp witness (`checkTorusCertificateV2_routeV2H_sharp`, `rfl`).

## Checks and their output

- **Builds.** Each of the six new modules: `Build completed successfully`, no warnings in the new
  files (table above).
- **Axioms** (`#print axioms`, scratch file): `smallDivisorSum_snoc2_le_bulk`, `walkB_sound`,
  `sdConst_ray_of_bulkSiteOk`, `bulkSiteOk_of`, `sdConst_of_siteOkH`, `refinedCoreH_sound`,
  `refinedBCoreH_sound`, `routeV2H`, `refinedCoreH_ofG`, `refinedBCoreH_ofG`,
  `checkTorusCertificateV2_routeV2H_sharp`, `bkSite_sdConst`, `bkSite_ok_sharded`,
  `bkSite_rejects`, `toyB3_refinedBH_torus`: all `[propext, Classical.choice, Quot.sound]`.
- **Cross-language.**
  - `python3 -I scripts/certifier/fiber3_bulk_xlang.py --check`: "the Lean module matches the
    mirror". Its 28 kernel-decided values include site verdicts on both sides of the exact bound
    and constant, and three SJS rows at `P = 128`.
  - The landed `fiber3_xlang.py --check` also matches.
- **Bulk against landed (mirror `check`).** On the toy box, the bulk walk's value is
  `1.00023`, `1.0017` and `1.0049` × the landed walk's at `b = 1/16, 1/32, 1/64`. At each bite the
  landed `fiberSiteOk` also passes at the bulk-certified constant.
- **Repository checks.**
  - `python3 -I scripts/gen_root_imports.py --check`: exit 0.
  - `python3 -I scripts/check_lean_modules.py`: PASS (4129 files).
- **`scripts/lint_sources.sh`.**
  - Passing steps: forbidden patterns, widths, file sizes, roots, errata, module check, and
    "FROZEN-ANCHOR GUARD OK".
  - Failing step: only the ABI-hash step, because
    `.lake/build/lib/lean/KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean` does not
    exist in this worktree. This is environmental, the same as in V2-3FREQ; the frozen planetary
    modules were not built here.
- **Merge.**
  - Relative to `origin/main` (`a2bb4b89`), the branch adds 9 files and modifies only the
    generated root and the design doc. Main has not touched either since the merge base.
  - `git merge-tree` (old form; git 2.34 has no `--write-tree`) shows 0 conflict markers.

## Measurements

**Toy (`Tests/BulkToy.lean`).** The frequency is `(θ − 1, 3θ² + 24θ − 35, 1)`, `θ = ∛2`. Its middle
coordinate is `3.08·10⁻⁴`, a slow step like SJS's `2.2·10⁻⁴`. The cubic norm gives
`γ = 3.0835·10⁻⁴`.

| bite | `N` | fibres | bulk nodes (single fibres, runs) | bulk `c` | classical `c♮` |
|---|---:|---:|---|---:|---:|
| `1/16` | 29 | 1,740 | 162 (12, 126) | `1.80·10⁻³` | 0.0452 |
| `1/32` (in the default build) | 65 | 8,580 | 452 (18, 317) | `5.73·10⁻⁴` | 0.0437 |
| `1/64` | 146 | 42,924 | 1,546 (74, 915) | `1.65·10⁻⁴` | 0.0429 |

Kernel timings, measured as user time over the import base:

| site | landed walk | bulk walk |
|---|---|---|
| `1/16` | 2.6 s, +0.38 GB | within noise of the base |
| `1/32` | killed by the 4 GB cap (scratch file, 3.3 GB base) | `BulkToy` builds in 4.2 s at 1.65 GB, with a second sharded proof of the same site |
| `1/64` | not run | about 2.5 s, +0.4 GB |

**SJS-plan frequencies.** The FH25 planar frequencies, with the fast one as the clock:
`ω' = (0.402883, −2.2037·10⁻⁴)`. The other settings:
- tail `T̂ ≤ 10⁻³ S`, with `S` from `scripts/sjs/results/S3_cache.json`;
- `P = 128`, `q = 64`, `rn/rd = 5/4`, `tol = 10⁻⁹ S`.

Counts are from the exact mirror (`python3 -I scripts/certifier/fiber3_bulk.py sjs`).

| γ | bite | `N` | fibres | nodes | values | single fibres | runs | bulk over plain walk |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| cubic `2.8·10⁻⁷` | `2.65·10⁻³` | 1,298 | 3,372,204 | 44,568 | 28,212 | 2,192 | 20,977 | +0.455 % |
| | `1.325·10⁻³` | 2,647 | 14,018,512 | 168,464 | 94,579 | 8,410 | 74,972 | +0.224 % |
| | `6.6·10⁻⁴` | 5,387 | 58,050,312 | 653,691 | 345,363 | 31,959 | 286,039 | +0.305 % |
| FH `1.69·10⁻⁶` | `2.65·10⁻³` | 1,186 | 2,815,564 | 39,060 | 25,419 | 1,947 | 18,349 | +0.455 % |

The kernel cost laws come from `lake build` of temporary shard modules (deleted, not committed)
importing `Fiber/BulkSite`:
- The base is 1.5–1.6 GB.
- An 8,033-node shard (rows `i ∈ [512, 1024)` of the first bite) built in 13 s at 3.05 GB. That is
  about **1.4 ms and 180–190 KB per node**.
- The densest 512-row block (21,249 nodes) exceeds 4 GB, so shards hold at most about 12–13k nodes.
- The plain walk's law (V2-3FREQ) is 1.2 ms and 215 KB per fibre.

Projections from these laws:

| bite | bulk | plain walk |
|---|---|---|
| `2.65·10⁻³` | 1.0 min, 4 shards | 1.1 h, 307 shards |
| `1.325·10⁻³` | 3.9 min, 13 shards | 4.7 h, 1,275 shards |
| `6.6·10⁻⁴` | 15 min, 51 shards | 19 h, 5,278 shards |

**The acceptance trade-off at the first SJS bite** (`N = 1298`):

| `rn/rd`, `tol` | nodes | values | bulk over plain walk | certified `c` |
|---|---:|---:|---:|---|
| `9/8`, `10⁻⁹ S` | 48,960 | 32,604 | +0.25 % | `2.355·10⁻⁷` |
| `5/4`, `10⁻⁹ S` | 44,568 | 28,212 | +0.46 % | `2.358·10⁻⁷` |
| `5/4`, `0` | 138,977 | 122,621 | +0.46 % | `2.358·10⁻⁷` |
| `5/4`, `10⁻⁷ S` | 39,383 | 23,027 | +0.46 % | `2.358·10⁻⁷` |
| `3/2`, `10⁻⁹ S` | 41,482 | 25,126 | +1.10 % | `2.365·10⁻⁷` |
| `2`, `10⁻⁹ S` | 39,390 | 23,034 | +2.13 % | `2.377·10⁻⁷` |

**Frequencies without a slow coordinate.** On T3 (`ω' = (0.63, 0.79)`), no run of two or more
fibres passes, so the bulk walk evaluates every fibre (its value equals the landed walk's) at about 2×
the nodes (bisection overhead). Applications should keep `.g (.fiber w)` there. `Tests/BulkRouteB`
uses two such bulk sites only to test the integration (`toyB3` through `routeBRefinedH`, and its
`CertifiedTorus` at `cubicFreq`).

## Owner questions

1. **Reaching about 10⁴ nodes at the first SJS bite.**
   - *Where the nodes go now.* Each integer crossing costs `O(log_{rn/rd}(1/η))` runs on each side,
     and each half-integer crossing costs `O(log M)` splits.
   - *Two cheap extensions.*
     1. A one-sided run next to an integer crossing, bounded by `Σ_j (F₀ + j d)⁻² ≤ F₀⁻² +
        1/(d (F₀ + d/2))` with `d` the exact slope of `F`. It costs `O(1)` per crossing, with a loss
        of a few percent on that run only.
     2. A run across a half-integer crossing, where `p` changes by one inside the run. The float
        model puts the saving at a third of the nodes.
   - Each needs a new run type in `blkK` with its own `*_spec`. Together they should reach about
     10⁴ nodes (`2.2·10³` single fibres plus `O(rows)`). Wanted?
2. **Default acceptance parameters for applications:** `rn/rd = 5/4` and `tol = 10⁻⁹ S` (`S` from a
   float estimate; soundness does not depend on it) are what the mirror's producer uses. Alternatives
   are tabulated above.
3. **`routeV2H` as the engine for three-frequency applications** (it contains `routeV2G`), or keep
   `routeV2G` and use `routeBRefinedH` directly?
4. Still deferred, not started: the clock index as witness data (V2-3FREQ owner question 3).

## Suspected errata and deviations

- **The shard counts in my V2-3FREQ handoff were too high, by about 4×.** It assumed 2,500 fibres
  per declaration from a 3.39 GB import base. That base was measured on a non-module scratch file,
  which loads all private data.
  - A `lake build` module importing `Fiber/Site3` or `Fiber/Shard` has a base of about 1.5–1.6 GB,
    so about 11k fibres fit per 4 GB shard.
  - Corrected plain-walk shard counts at the three SJS bites: 307 / 1,275 / 5,278. The handoff
    gave 1,374 / 5,595 / 23,523.
- **`P = 64` cannot certify the third SJS bite.** `powUp` rounds up to at least `2^{−P}`, and the
  third bite (`b = 6.6·10⁻⁴`) needs `E^{N+1} ≈ 3·10⁻²⁰ < 2^{−64}`. The landed producer
  `fiber3.produce_site` defaults to `P = 64`; its witnesses there need `P ≥ 70`. The V2-3FREQ table's
  `N = 5,422` at that bite came from the float tail; the exact one with `P = 128` gives `N = 5,387`.
- **Deprecation warnings in this Mathlib.** `if_pos`/`if_neg` and `if_true`/`if_false` are
  deprecated, and the build replays such warnings from existing files
  (`KAM/Strip/CohomologicalRussmann*.lean`). The new files avoid them (`↓reduceIte`).

## Uncertainties

- **The SJS frequency vector.** The counts use FH25's printed frequencies (radius `10⁻³⁰`), not the
  plan's cubic vector. The two agree to about `10⁻⁸` relative, and the walk depends on `ω'` only
  through its position relative to the integers, so the structure is the same. Single counts can
  differ by a few percent.
- **The kernel law.** It comes from one 8,033-node shard (1.4 ms per node) and one 80-row scratch
  probe (0.9 ms per node, machine under load). The minutes above use 1.4 ms per node.
- **The SJS witnesses are not built.** The SJS walks are not part of this branch. They are opt-in
  application builds, sharded with `bulkSiteOk_of` and `balFold_succ_of`.

V2-BULK DONE
