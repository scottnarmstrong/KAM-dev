# V2-BULK-RUNS handoff: tent runs and crossing runs for the bulk walk

Date: 1 November 2026. Branch `v2-bulk`, new commits on top of the audited head `f9fa56ba` and the
V2-BULK-FIX head `a5567900`. Additive only:
- no existing `.lean` file changes except the generated root `KAM/Root/CertificateSharp.lean`;
- the V2-BULK modules (`Fiber/Bulk`, `Fiber/BulkSite`, `Fiber/RouteH`, the `Tests/Bulk*` modules)
  are byte-identical to the audited head.

Task (orchestrator decision 1): build the two run types (crossing-adjacent, half-integer crossing)
toward about 10⁴ nodes at the first SJS bite, each with its own soundness proof. Design:
[V2-3FREQ.md §8](../design/V2-3FREQ.md#8-v2-bulk-runs-tent-runs-crossing-runs-and-a-computed-crossing-cut).

## Result

At the first SJS bite the extended walk `walkB2` bounds `S` with **13,719 nodes**, against 44,568
for `walkB` and 3.37·10⁶ fibres for the plain walk. The bound is 0.40 % above a floating-point
evaluation of the fibered sum, and the certified constant matches `walkB`'s (2.357·10⁻⁷ against
2.358·10⁻⁷). At the third bite: 122,921 nodes against 653,691.

Each run type has its own soundness theorem: `tentK_spec` and `apK_spec`. The extended walk is sound
whatever its cut points and acceptance rules (`hnode_spec`, `walkB2_sound`).

**Caveat: kernel cost tracks value computations, not nodes** (this section describes the walk
before V2-BULK-CUTS; see the CUTS section below).
- Before the cuts, each node that ends up split could compute up to three values, one each for the
  plain, tent and crossing tolerance tests. The cuts remove the tent and crossing ones. Each value
  costs about three binary powers of `P`-bit numbers.
- The values drop only 28 % at the first bite (20,425 against 28,212) and 2.1× at the third
  (164,699 against 345,363).
- Extrapolated from two probed blocks (of six): about 50 s for the first bite in 4–5 shards,
  against about 1 min (projected) for `walkB`. The densest 512-row block now fits one 4 GB shard (3.8 GB); under `walkB` it did not
  fit.
- Possible savings are listed below as owner question 1.

## Files (all new except the generated root and the docs)

Each module was rebuilt alone after removing its own build artifacts.

| File | Lines | Build | Peak |
|---|---:|---:|---:|
| `KAM/CertificateSharp/V2/Fiber/BulkRuns.lean` | 1,120 | 8.0 s | 1.67 GB |
| `KAM/CertificateSharp/V2/Fiber/Bulk2.lean` | 570 | 2.9 s | 1.44 GB |
| `KAM/CertificateSharp/V2/Fiber/Bulk2Site.lean` | 157 | 1.7 s | 1.45 GB |
| `KAM/CertificateSharp/V2/Fiber/RouteBK.lean` | 268 | 2.5 s | 1.55 GB |
| `KAM/CertificateSharp/V2/Tests/Bulk2Toy.lean` | 69 | 4.4 s | 1.80 GB |
| `KAM/CertificateSharp/V2/Tests/Bulk2RouteB.lean` | 105 | 1.6 s | 1.36 GB |
| `KAM/CertificateSharp/V2/Tests/Bulk2XLang.lean` (generated, 31 values) | 228 | 3.9 s | 1.63 GB |
| `scripts/certifier/fiber3_bulk2.py` (exact mirror, producer, SJS counts) | | | |
| `scripts/certifier/fiber3_bulk2_xlang.py` (writes `Bulk2XLang.lean`; `--check`) | | | |
| `docs/campaign/design/V2-3FREQ.md` §8; this handoff | | | |
| `docs/campaign/handoffs/V2-3FREQ.md`: dated correction note (commit `3dcc07aa`) | | | |

All Lean files are modules, at most 1,120 lines and at most 100 columns, with no `sorry` and no
option overrides.

## Approach (details in design §8)

- **`BulkRuns.lean`.**
  - `powDownK`, a floor-rounded binary power, with `powDownK_le`: a lower bound of `x^n`.
  - `gsumK`, with `gsumK_ge`: the geometric weight sum at any length, with no table.
  - `blkK_spec_gen`: `blkK_spec` at the run's own length. Its proof is copied from `Fiber/Bulk.lean`
    with the one step that used the dyadic length replaced.
  - The two telescoping bounds, `receding_sum_le` and `approach_sum_le`.
  - The run values `firstK`, `constK` and `valK`.
  - The tent run: `tent_point`, `tentK`, `tentK_spec`.
  - The crossing run: `sgnZ`, `rec_first_le`, `app_first_le`, `apK`, `apK_spec`.
- **`Bulk2.lean`.**
  - Walk pieces: `oadd`, `runSet_split`, `BCov.split`, `singles`, `sideAP`, `crossCut`, `hnode`,
    `rowB2`, `walkB2`.
  - Their specs, `walkB2_sound`, `smallDivisorSum_snoc2_le_of_cover` (the shared final step) and
    `smallDivisorSum_snoc2_le_bulk2`.
- **`Bulk2Site.lean`.** `Bulk2Wit` (no table; `s`, `fuel`), `bulk2SiteOk`,
  `sdConst_ray_of_bulk2SiteOk`, `bulk2PreOk`/`bulk2SiteOk_of` (shards), `SiteWitK`, `siteOkK`,
  `sdConst_of_siteOkK`.
- **`RouteBK.lean`.**
  - `routeBRefinedK`, copied by script from `RouteBG` (G renamed to K, with `sdConst_of_siteOkK`).
  - `RefinedBWitK.ofH`, with `refinedBCoreK_ofH` and `checkTorusCertificateV2_routeBRefinedK_ofH`
    (same verdict as `routeBRefinedH`).
  - Per decision 3, there is no combined engine; that is V2-CONSOL's.

## Checks and their output

- **Builds.** All seven new modules: `Build completed successfully`, no warnings in the new files
  (table above).
- **Axioms** (`#print axioms`), all `[propext, Classical.choice, Quot.sound]`:
  - core lemmas: `powDownK_le`, `gsumK_ge`, `receding_sum_le`, `approach_sum_le`, `blkK_spec_gen`,
    `tentK_spec`, `apK_spec`, `hnode_spec`, `walkB2_sound`;
  - bounds and sites: `smallDivisorSum_snoc2_le_of_cover`, `smallDivisorSum_snoc2_le_bulk2`,
    `sdConst_ray_of_bulk2SiteOk`, `bulk2SiteOk_of`, `sdConst_of_siteOkK`;
  - route B: `refinedBCoreK_sound`, `refinedBCoreK_ofH`, `routeBRefinedK`;
  - tests: `bk2Site64_sdConst`, `bk2Site32_rejects`, `toyB3_refinedBK_torus`, `xl_site_exact`.
- **Cross-language.** `python3 -I scripts/certifier/fiber3_bulk2_xlang.py --check` matches. Its 31
  kernel-decided values cover:
  - `powDownK`, `gsumK`, and a crossing cut;
  - tent runs accepted and rejected;
  - crossing runs receding, approaching and rejected;
  - rows and the walk on the toy box;
  - `bulk2SiteOk` on both sides of the exact bound and constant;
  - three SJS rows at `P = 128`.
- **Toy (`Tests/Bulk2Toy.lean`).** On the toy of `Tests/BulkToy.lean`:
  - at `b = 1/64` (42,924 fibres), `walkB2` visits 924 nodes against `walkB`'s 1,546 and certifies
    `c = 1.648·10⁻⁴`, the same as `walkB`, against the classical 0.0429;
  - at `b = 1/32`, 334 nodes against 452, and a constant 1 % low is rejected.
- **Repository checks.**
  - `gen_root_imports.py --check`: exit 0.
  - The three cross-language `--check` scripts all match.
  - `check_lean_modules.py`: PASS (4,136 files).
  - The V2-BULK modules are unchanged since `a5567900`.
- **`scripts/lint_sources.sh`.** Every step passes, including "FROZEN-ANCHOR GUARD OK", except the
  ABI-hash step. It fails because the frozen planetary oleans are not built in this worktree; this
  is environmental, as before.
- **End to end (`Tests/Bulk2RouteB.lean`).** `toyB3` passes `routeBRefinedK` with two `.bulk2`
  sites, giving `CertifiedTorus toyB3 cubicFreq`.

## Measurements

Exact mirror, `python3 -I scripts/certifier/fiber3_bulk2.py sjs`, run under the 8 GB `systemd-run`
cap. "Over float sum" is relative to a floating-point evaluation of the fibered sum.

| γ | SJS bite | `N` | fibres | `walkB2` nodes | values | single fibres | tent runs | crossing runs | crossing cuts (light) | over float sum |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| cubic | `2.65·10⁻³` | 1,298 | 3,372,204 | **13,719** | 20,425 | 3,501 | 745 | 1,406 | 738 (188) | +0.40 % |
| cubic | `1.325·10⁻³` | 2,647 | 14,018,512 | **38,028** | 56,265 | 14,257 | 3,088 | 5,173 | 3,084 (853) | +0.22 % |
| cubic | `6.6·10⁻⁴` | 5,387 | 58,050,312 | **122,921** | 164,699 | 65,476 | 12,488 | 16,006 | 12,785 (2,249) | +0.31 % |
| FH | `2.65·10⁻³` | 1,186 | 2,815,564 | **12,573** | 19,041 | 3,001 | 619 | 1,276 | 620 (146) | +0.39 % |

The `walkB` counts for comparison (V2-BULK) are 44,568 / 168,464 / 653,691 nodes and 28,212 / 94,579
/ 345,363 values.

**Kernel probes** (first bite, temporary shard modules importing `Fiber/Bulk2`, deleted after
measuring, 4 GB cap):

| block | `walkB2` nodes | values | build | peak | `walkB` on the same block |
|---|---:|---:|---:|---:|---|
| typical | 1,860 | 2,259 | 11 s | 2.0 GB | 8,033 nodes, 13 s, 3.05 GB |
| densest | 7,311 | 12,942 | 19 s | 3.8 GB | 21,249 nodes, over 4 GB (killed) |

The whole first bite comes to about 50 s of kernel time in 4–5 shards. This is an estimate from the
six block counts; only two blocks were run.

**Float-model checks used for the design** (scratch scripts, not committed):
- tent runs alone cut `walkB`'s nodes by a third, with no loss;
- the first receding formula, with its infinite tail, overcounted short runs by 1.6 % of `S`. That
  led to the finite telescoping bound with `powDownK`. Excess by run type after the fix, at the
  first bite against the walk's own weights: plain +0.03 %, receding +0.13 %, approaching +0.05 %,
  tent 0.00 %, single fibres 0.00 %.

## Owner questions

1. **Kernel cost per node.** Cheap follow-ups, all changing acceptance only (soundness unaffected):
   - try `tentK` only when the plain shape fails, and `apK` only when it holds, since their
     structural checks are complementary: about one value fewer per split node;
   - compute each run's crossing-run value only after its quality test;
   - use `P = 64` at the first two bites (`P = 128` is needed only at the third). This was done in
     V2-BULK-CUTS and reverted by audit E1 (V2-BULK-RUNS-FIX): `P = 128` at all bites.

   Dropping the tolerance tests outright was tried in the mirror and does not help (more nodes, as
   many values). Wanted?
2. **Engine.** `routeBRefinedK` is the route-B engine with extended sites. Per decision 3 it is not
   combined; V2-CONSOL will include `SiteWitK` (or its successor) after landing.
3. Still deferred: the clock index as witness data.

## Suspected errata and deviations

- **The crossing cut's single fibres dominate at the third bite** (65,476 of 122,921 nodes before
  V2-BULK-CUTS; 76,726 of 144,083 after). Before the cuts, the light-crossing branch (crossing fibre
  plus two crossing runs) was taken only when both side runs were accepted, and most crossings at
  that bite were too heavy for the tolerance. Since the cuts it no longer fires. A weight-dependent
  half-width is the recorded, deferred refinement (CUTS section).
- `if_pos`/`if_neg` and `Int.ofNat_eq_coe` are deprecated in this Mathlib. The new files use
  `↓reduceIte` and `Int.ofNat_eq_natCast`.

## Uncertainties

- The kernel estimate for the full first bite extrapolates from two of six 512-row blocks. The
  per-value cost varied between the two blocks (machine load).
- The SJS counts use FH25's printed frequencies (radius `10⁻³⁰`), as in V2-BULK.

V2-BULK-RUNS DONE

## V2-BULK-CUTS (orchestrator decision: acceptance-only cost cuts, then stop)

Commit `c3164201`. New and changed code is in the unaudited run-type modules only; soundness is
unchanged.

- **Dispatch.** `hnode` tests `plainShape` (the shape test that plain and crossing runs share). When
  it holds, it tries a plain run (`blkK`) and then a crossing run (`apK`). Otherwise it tries a tent
  run (`tentK`). Soundness of the three branches is `run3_spec`.
- **Crossing runs** are accepted by quality alone, with no tolerance fallback, so a rejected crossing
  run costs no value. `apK` lost its `tol` argument.
- **Precision.** The producer first used `P = 64` at the first two SJS bites. Since
  V2-BULK-RUNS-FIX it uses `P = 128` at all bites (audit E1): `P = 64` raised `N` and gave about 2 %
  more nodes and values, with no kernel-time gain.
- **Tests regenerated.** `Bulk2XLang` has 31 values. The accepted approaching crossing run is now
  taken from the `b = 1/64` toy walk, because the `1/32` toy's only one had been accepted by the
  dropped tolerance. The `Bulk2Toy` witnesses and the `Bulk2RouteB` sites are unchanged and pass.
- **Builds.** All seven run-type modules rebuilt alone: 2.5–7.4 s, at most 1.76 GB, no warnings in
  the new files.

**Exact mirror (`fiber3_bulk2.py sjs`, 8 GB cap), at `P = 128`, so the same `N` before and after
the cuts:**

| SJS bite | `N` | fibres | nodes | values | before the cuts (nodes / values) | over float sum | `c` |
|---|---:|---:|---:|---:|---|---:|---|
| `2.65·10⁻³` | 1,298 | 3,372,204 | 15,299 | **15,903** | 13,719 / 20,425 | +0.40 % | `2.357·10⁻⁷` (unchanged) |
| `1.325·10⁻³` | 2,647 | 14,018,512 | 45,364 | **46,954** | 38,028 / 56,265 | +0.22 % | unchanged |
| `6.6·10⁻⁴` | 5,387 | 58,050,312 | 144,083 | **147,868** | 122,921 / 164,699 | +0.31 % | unchanged |

Values, which drive kernel cost, fall 22 %, 17 % and 10 %. At the same `N`, nodes rise: the
light-crossing branch (crossing fibre plus two crossing runs) relied on the tolerance fallback and no
longer fires, so those crossings take the `±s` single fibres instead. The first commit of the cuts
reported `P = 64` figures at the first two bites (`N` = 1,318 and 2,688, so 3.1 % more fibres at the
first bite): 15,619 / 16,221 and 46,340 / 47,928.

**Kernel probes** (first bite, temporary shard modules, deleted, 4 GB cap):

| 512-row block | `P` | nodes | values | build | peak |
|---|---:|---:|---:|---:|---:|
| densest | 64 (`N = 1,318`) | 7,519 | 8,098 | 15 s | 3.41 GB |
| densest | 128 | 7,465 | 8,042 | 15 s | 3.41 GB |
| typical | 64 (`N = 1,318`) | 2,338 | 2,341 | 14 s | 1.99 GB |

Before the cuts the densest block took 19 s and 3.81 GB (12,942 values). `P = 64` against `P = 128`
made no measurable difference on that block. Extrapolated from the two probed blocks (of six), the
whole first bite is about 40 s of kernel time in 4 shards. That compares with about 50 s before the
cuts (also extrapolated) and about 1 min (projected) for `walkB`.

**Checks.**
- `#print axioms` of `apK_spec`, `run3_spec`, `hnode_spec`, `walkB2_sound`,
  `smallDivisorSum_snoc2_le_bulk2`, `sdConst_ray_of_bulk2SiteOk`, `refinedBCoreK_sound`,
  `bk2Site64_sdConst` and `toyB3_refinedBK_torus`: `[propext, Classical.choice, Quot.sound]`.
  `xl_ap_app` uses `[propext]` only.
- `gen_root_imports.py --check`: exit 0. `fiber3_bulk2_xlang.py --check`: matches.
  `check_lean_modules.py`: PASS.
- `lint_sources.sh` passes every step except the ABI-hash step (the frozen planetary oleans are not
  built in this worktree).

**Recorded, not started (orchestrator):** the weight-dependent single-fibre window around crossings,
which addresses the third bite's 76,726 single fibres. It waits until an SJS certificate is actually
scheduled.

V2-BULK-CUTS DONE

## V2-BULK-RUNS-FIX (audit AUDIT-V2-BULK-RUNS-1: PASS WITH CHANGES, Lean sound)

- **D1.** Pre-cut statements are marked as such: the crossing run's tolerance acceptance and the
  three tolerance values per split node (design §8, and this handoff's caveat), each with a pointer
  to the CUTS subsection.
- **D2.** The whole-bite kernel times (about 50 s before the cuts, about 40 s after) are labelled as
  extrapolations from two probed blocks of six.
- **D3.** The CUTS tables state `N` and fibres and compare at equal `N` (`P = 128`). The probe rows
  at `P = 64` carry `N = 1,318`. Stale numbers are fixed: the toy's 924 nodes, and the line counts of
  `Bulk2.lean` (570), `BulkRuns.lean` (1,120) and `Bulk2Toy.lean` (69).
- **E1 (orchestrator decision).** The producer (`scripts/certifier/fiber3_bulk2.py`, `sjs`) uses
  `P = 128` at all bites. A rerun gives 15,299 / 15,903, 45,364 / 46,954 and 144,083 / 147,868 nodes
  / values, matching the audit's own run.
- No Lean file changes. The cross-language module still matches
  (`fiber3_bulk2_xlang.py --check`), because its SJS rows already used `P = 128`.

V2-BULK-RUNS-FIX DONE
