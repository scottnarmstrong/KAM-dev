# V2-ENERGY handoff: improvement 2, the isoenergetic energy-row bound

Branch `v2-energy`, based on `origin/main` at `ac143010`. Not pushed, not merged. Brief:
`~/kam-tools/briefs/V2-ENERGY.md`.

## Result

| Step | State | Commit |
|---|---|---|
| 1. Measure, study | done, `V2-ENERGY STUDY READY` printed | `337387e4` |
| 2. Theorem side | done: `iso_g1_branch_E`, old theorem recovered at `Mh1 = M` | `38ccce3e` |
| 3. Checker side | done: `routeBRefinedE`, `routeV2AllE`, toy tests | `c9bca062` |
| 4. Mirror, cross-language test, comparison | done | `522d1cc2`, this commit |

**It works, but no current application benefits.**

- Route A refined already uses `dh`, so it has no slack and needs no new engine.
- Route B on LG00 T′ gains +1.62 decades (42×), but route A stays ahead: 99× against 5.66× at L = 20 with classical sites.
- Lunar N = 65 gains 0.000.
- It buys no L or kernel cost on either application.

**One check could not complete: the ABI step of `scripts/lint_sources.sh`** (see Checks).

## Files

No existing `.lean` file is edited. `git diff --diff-filter=MDR --name-only origin/main HEAD -- '*.lean'` lists only the
generated roots `KAM/Root/CertificateSharp.lean` and `KAM/Root/Iso.lean`, so the rule tightened mid-task is met. Nothing
imports the new modules except the new engines and tests.

**Theorem side** (`KAM/Iso/Sharp2/`):

- `RouteBE/Scheme.lean`: `RunBaseE`, `RunHypE`, with a parameter `Mh1`, `y0 : N.y0 = Mh1 * N.sN` and
  `dH : ∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ Mh1`.
- `RouteBE/Step.lean`: `RunHypE.good_step`.
- `RouteBE/Core.lean`: `RunHypE.isNewton`, `RunHypE.core`.
- `RouteBE.lean`: `iso_g1_branch_E`, `iso_g1_branch_B_of_E`, `iso_g1_branch_B_eq_of_E`.

**Checker side** (`KAM/CertificateSharp/V2/`):

- `RouteBE.lean`: `RunBWit.numE`, `RefinedBWit.numE`, `refinedBCoreE`, `refinedBCoreE_of`, `refinedBCoreE_sound`,
  `refinedBETest`, `refinedBETest_bT`, `routeBRefinedE`, `checkTorusCertificateV2_routeBRefinedE_sound`.
- `RouteAllE.lean`: `routeV2AllE := routeV2AllLN.orElse routeBRefinedE`, three `rfl` theorems.
- `Tests/RouteBE.lean`: toy tests.
- `Tests/RouteBEMirror.lean`: generated cross-language test.

**Python and docs:** `scripts/apost_sharp/energy_row.py`, `scripts/apost_sharp/route_be_mirror.py`, small additions to
`structured_b.py`, `docs/campaign/studies/V2-ENERGY-ROW.md`, `docs/campaign/studies/v2-energy-data/dry_tp_L20.json` (a copy
of LG00-T2's dry run, so the study does not depend on another session's scratch directory).

## Approach

- **Why the chain is copied.** `RunBaseI` contains the field `y0 : N.y0 = M * N.sN`, and `M` also bounds five objects through
  `IsoStanding.bounds`, so the old lemmas cannot be reached at a smaller `Mh1`. The equality is consumed at one proof site,
  `RouteB/Step.lean:227`. With old files frozen, the record and everything depending on it are repeated in new modules.
- **The copy is auditable.** A script generated it from the originals; `RunHypE`'s helpers that do not mention the record
  (`GoodI`, `schemeIB`, `iterI`, `iterI_spec`, the limit lemmas) are reused. After normalizing the renames, 12 of 1,116
  copied lines differ from the originals:
  - `Scheme`: 4, the two structure headers and the fields `y0`, `dH`.
  - `Step`: 2, the energy row now reads `R.dH`.
  - `Core`: 0.
  - Branch: 6, the statement's `Mh1`, `hy0`, `hdH`, and the record's `dH := hdH`.
- **The specialization is exact.** `iso_g1_branch_B_of_E` has the old statement word for word, proved from
  `iso_g1_branch_E` at `Mh1 = M`. `iso_g1_branch_B_eq_of_E : @iso_g1_branch_B = @iso_g1_branch_B_of_E := rfl` makes the
  kernel confirm the two statements are the same proposition.
- **The premise** is only `hdH : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1`, a bound on `H`. Nothing is conclusion-shaped.
- **The `Mh1` claim** is the existing `RefClaim.dh`, checked by `checkHamClaim` (`HamFacts.dh`). No new pass and no new
  witness field: the study shows anything below `dh` moves no threshold.
- **Engines.** `routeBRefinedE` runs `checkHamClaim`, `checkFrameLN` and `refinedBCoreE`. It keeps F2's omission of `bT`.
  `routeBRefined`, `routeBRefinedLN`, `routeV2All` and `routeV2AllLN` are unchanged. No route-A engine, per the brief's
  condition.

## Checks and output

```text
$ lake build --no-build ... (all modules below, built one at a time under a 4 GB scope)
KAM.Iso.Sharp2.RouteBE                               built, 11 s
KAM.CertificateSharp.V2.RouteBE, RouteAllE           built
KAM.CertificateSharp.V2.Tests.RouteBE                built, 26 s
KAM.CertificateSharp.V2.Tests.RouteBEMirror          built, 4 s
$ python3 -B -I scripts/apost_sharp/route_be_mirror.py       # exit 0
Lean cross-language test up to date: True
lower  X* = 351/500000000: y0 = dh s_N routeBOk True (log10 e* -18.271); y0 = M s_N routeBOk True []
upper  X* = 351/500000000: y0 = dh s_N routeBOk True (log10 e* -18.271); y0 = M s_N routeBOk True []
tp     X* = 199/250000000000: y0 = dh s_N routeBOk True (log10 e* -16.341); y0 = M s_N routeBOk False [J1 ...]
```

**Toy tests, all by `decide +kernel`:**

- an ordinary witness passes `routeBRefinedE`, alone and inside `routeV2AllE`;
- `toyBGain` (between the two thresholds, `X⋆` 2.34·10⁻⁵ old, 3.06·10⁻⁵ new) passes it and is rejected by `routeBRefined`
  and `routeBRefinedLN`, with `refinedBCore` itself false;
- `dh := 199/100` is rejected, while `refinedBCoreE` alone accepts it, so `checkHamClaim` is what rejects it;
- both toy torus theorems hold, at a witness the landed engine rejects.

**Cross-language test:** 80 kernel theorems compare Python's exact rationals with Lean's `StepBQ`, for 2 witnesses, both
`y₀`, stages 0–2, and `sC0`, `sCDK`, `sQ`, `sCab`, `sBloc`, `sCnu`, plus `y₀` and the `okB` verdicts. Rationals are compared
by numerator and denominator modulo `2^61 - 1`, since they do not fit the line limit. A mirror with `y₀` off by 1 % is
refuted on 34 of the 80 theorems, so the test does detect drift.

**`scripts/lint_sources.sh`: exit 1, from the ABI step only.** Line length, modules (`check_lean_modules: PASS`), root check
and `FROZEN-ANCHOR GUARD OK` all pass. `abi_hashes.py --check` stops at a missing olean,
`KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM`: 43 of the 179 anchor files have no olean in the seed taken from the
main checkout. This branch touches no frozen file, but **the ABI check has not been run on it**; the landing build should
run it. A full `lake build` was not run either.

## Axioms

```text
iso_g1_branch_E                                [propext, Classical.choice, Quot.sound]
iso_g1_branch_B_of_E                           [propext, Classical.choice, Quot.sound]
iso_g1_branch_B_eq_of_E                        [propext, Classical.choice, Quot.sound]
refinedBCoreE_sound                            [propext, Classical.choice, Quot.sound]
checkTorusCertificateV2_routeBRefinedE_sound   [propext, Classical.choice, Quot.sound]
toyB_refinedBE_torus                           [propext, Classical.choice, Quot.sound]
toyB_routeV2AllE_torus                         [propext, Classical.choice, Quot.sound]
```

## Measurements

Full tables are in [V2-ENERGY-ROW](../studies/V2-ENERGY-ROW.md).

| Route on LG00 T′ (`err` 8.06·10⁻¹⁸) | `log10 e*` | Margin at L = 20 | Least L at margin ≥ 10× |
|---|---:|---:|---:|
| A refined, classical (current) | -15.098 | 99× | 19 |
| B refined, classical, today | -17.962 | 0.135× | 23 |
| **B refined, classical, `routeBRefinedE`** | **-16.341** | **5.66×** | **21** |

- **Lunar N = 65:** route B and route A both unchanged, +0.000.
- **Toy cost** (user CPU net of imports, median of 5): `routeBRefined` 2.03 s, `routeBRefinedLN` 1.16 s, `routeBRefinedE`
  1.13 s; peak 3.82, 3.67, 3.67 GiB. Changing `y₀` costs nothing; the saving against the landed engine is F2's.
- **Checking cost of the claim:** none, since `checkHamClaim` already runs in every refined route.
- The least-L column is estimated from the dry-run `err` values, not from new dry runs.

## Owner questions

Deferred under overnight mode; nothing here blocks.

1. **Keep or shelve `routeBRefinedE`?** It is sound, additive and cheap to keep, and it serves any future application with
   `M ≫ dh` that selects route B. No current application needs it. I kept it, as the brief directs; the conservative
   choice for landing is to land it, since nothing imports it except its tests.
2. **Frequency sites on LG00.** Route A with frequency-specific constants would reach about 8900× on T′ against 99×, which
   could allow L = 17. `clockOk` needs a positive last coordinate and LG00's is -41.48, so the enhanced `siteOk` rejects it.
   These are uncertified design floats, and the certification cost on LG00 is unmeasured. Is it worth a sign change in the
   generator, or a new site check in a new module? `SmallDivQ.lean` itself must not change. This looks more valuable for
   LG00 than improvements 1 or 2.

## Deviations and errata

- **Correction to my #1 study:** its "improvement 2 would gain about 15 times more on LG00" holds for route B only. Route A
  already had that gain, which the study did not say.
- **Files beyond the brief's list:** the `dry_tp_L20.json` copy, made so the study has no dependency on a scratch path.
- **Not done:** T″ was not measured (still being computed). The lock torus was not evaluated.
- **Measurement noise:** the machine's load average was about 30; I report user CPU, not wall time, for that reason.
- **Suspected errata in pinned sources:** none.
