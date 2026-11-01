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

## Gain on the example (T3, route A refined, same data otherwise)

| Bite | Certified sharp `c` (fibres) | Exact-S float `c` | Classical `c♮(3,2,b)` | Factor |
|---|---|---|---|---|
| `b = 1` (`δ₀`, `b₀`, `b₁`) | `4.909·10⁻⁴` (12) | `2.82·10⁻⁴` | `0.0783` | 159 |
| `b = 1/2` (`δ₁`) | `2.853·10⁻³` (24) | `1.65·10⁻³` | `0.0629` | 22 |
| `b = 1/4`, `1/8`, `1/16`, `1/32`, `1/64` (mirror) | `3.88, 3.32, 2.94, 2.64, 2.37 ·10⁻³` (112–26,680) | | `0.0535 … 0.0429` | 14–18 |

**Threshold (largest invariance error the refined core accepts, at T3's parameters, caps 8.05):**

- Classical sites accept up to `5.6·10⁻¹⁴` (`X⋆ ≤ 1.16·10⁻⁹`).
- Fibered sites accept up to `6.1·10⁻¹²` (`X⋆ ≤ 1.27·10⁻⁷`).
- Gain: **2.0 orders**. These figures come from the mirror (`v2_q.py` with the certified
  constants).
- The kernel confirms the crossing: `toy3_threshold_fibered` (err `5·10⁻¹²` passes with fibered
  sites), `toy3_threshold_classical_fails` (the same with classical sites fails), and
  `toy3_threshold_classical` (classical passes at `5·10⁻¹⁴`).

## SJS planar frequencies (estimate, `docs/explorations/sjs-plan.md`)

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
- `KAM/CertificateSharp/V2/Fiber/RouteAG.lean` (235): `routeARefinedG`, `routeAV2G`.
- `KAM/CertificateSharp/V2/Fiber/RouteBG.lean` (239): `routeBRefinedG`, `routeV2G`.
- `KAM/CertificateSharp/V2/Fiber/Shard.lean` (75): `balFold_succ_of`, `fiberSiteOk_of`.
- `KAM/CertificateSharp/Freq/CubicNorm.lean` (454): the cubic norm form and `cubicDioOk`.
- Tests:
  - `KAM/CertificateSharp/V2/Tests/Fiber3Toy.lean` (190): T3 end to end.
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
  - `Built KAM.CertificateSharp.Freq.CubicNorm (4.3s)`, `… Fiber.Enum2 (6.0s)`,
    `… Fiber.Site3 (4.6s)`, `… Tests.Fiber3Toy (19s)`.
  - `Build completed successfully (3524 jobs)`; 32.6 s wall, max RSS 2.9 GB.
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

- **Toy T3 module:** whole v2 certifier plus threshold checks in 19 s.

## Owner questions

1. **Route B with three frequencies.** It needs a positive example with `ρ ≤ 1`. T3 (`ρ = 9`) only
   exercises route A. Toy B (n = 2) exercises `routeBRefinedG` through `ofRefined`. Should a T3
   variant with `ρ ≤ 1` be built (a new toy certificate)?
2. **SJS scale.** Is a bulk bound for far fibres (`|x + p| ≥ η`, summed per shell
   `|k'|₁ = s` analytically) wanted? It would turn `3·10⁶–6·10⁷` walked fibres into about `10⁴`
   near-resonant ones (the plan's count), at the price of a near-resonance enumeration certificate
   (e.g. continued-fraction / three-distance data for `ω'`).
3. **Clock choice.** The checker fibres over coordinate 2. For SJS, should applications reorder the
   frequency vector so the fast coordinate is last (assumed in the estimate), or should the clock
   index become witness data?

## Uncertainties

- The SJS numbers are estimates.
  - `N` comes from the exact tail formula with `T̂ ≤ 10⁻³ S`.
  - The cost extrapolates the T3 per-fibre measurement. SJS boxes need a larger `q` (tighter
    enclosure), which makes integers longer and the per-fibre cost somewhat higher.
  - Route B also has split-bite sites (bite `2δ/3` at `τ = 2`): about 2.25× the fibres of the `δ`
    site.
- The T3 threshold figures (`6.1·10⁻¹²`, `5.6·10⁻¹⁴`) are the mirror's. The kernel confirms only
  the crossing at `5·10⁻¹²` and the classical pass at `5·10⁻¹⁴`.

## Suspected errata and deviations

- `KAM/CertificateSharp/Freq/SmallDivisorFiber.lean` (module docstring and `sdsFiberBound_sound`)
  presents the fibered checker as general in `m`. Its premise
  `IsDiophantine (d.γ : ℝ) 1 (Fin.snoc ω' 1)` is unsatisfiable for `m ≥ 2` (Dirichlet: every
  `ω ∈ ℝ³` has `|k·ω| ≤ C|k|₁⁻²` infinitely often). The theorem is correct but vacuous beyond
  `m = 1`. Not a soundness issue. **Suggested docstring sentence** (not applied; the file is
  read-only for this branch): "useful only for `m = 1`: a `(γ, 1)`-Diophantine vector of `ℝ^{m+1}`
  exists only for `m ≤ 1`."
- **Deviation from the brief's wording:** the "exact sum over `0 < |k|₁ ≤ N`" is realised as the
  fibered sum over `0 < |k'|₁ ≤ N` with every `k_last` summed analytically. That is a superset of
  the box, bounded from above, plus the proved tail for `|k'|₁ > N`. The full 3-D box would be
  `≈ 4N³/3` modes.
- **Deviation from the design draft:** the walk uses a witness-supplied dyadic box and integer
  fixed point instead of the certificate's rational box. Measured: exact rationals cost 5× the time
  and 4× the memory.

V2-3FREQ DONE
