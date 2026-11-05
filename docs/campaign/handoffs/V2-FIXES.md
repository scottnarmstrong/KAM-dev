# V2-FIXES handoff: the confirmed v2-certifier fixes and the route-B bound experiment

Branch `v2-fixes`, based on `f80bdf6e`. Not pushed, not merged. Brief: `~/kam-tools/briefs/V2-FIXES.md`.

## Result

| Item | State | Commit |
|---|---|---|
| F1 `check_modconstb_v2.py` | done: exits 0, 32 cases under both cap conventions | `41767c75` |
| F3 `v2_adapter.py` | done | `07b2a566` |
| F4 two-frequency guards | done: benchmark values byte-identical | `07b2a566` |
| F2 route B without `bT` | done, additive; **saves little in a real run** | `d552c3c7`, `d4643f72` |
| #1 structured bounds | **verdict: do not implement** ([study](../studies/V2-STRUCTURED-B.md)) | this commit |
| Fixes doc | each fix marked with its commit | this commit |

**One check could not complete: the ABI step of `scripts/lint_sources.sh`.** See Checks.

## Files

**New Lean modules** (no existing module edited; `git diff --diff-filter=MDR` over `KAM/CertificateSharp`, `KAM/Sharp2`,
`KAM/Iso`, `KAM/Certificate`, `KAM/SpinOrbit`, `KAM/Frozen`, `manifest` lists 0 files):

- `KAM/CertificateSharp/Frame/MajorantsLN.lean`: `checkFrameLN`, `FrameMajorantsLN`, `checkFrameLN_sound`.
- `KAM/CertificateSharp/V2/RouteBLN.lean`: `FrameFactsLN`, `refHypB_ofLN`, `refinedBCore_soundLN`, `refinedBLNTest`,
  `refinedBLNTest_bT`, `routeBRefinedLN`, `checkTorusCertificateV2_routeBRefinedLN_sound`,
  `refinedBLNTest_of_refinedBTest`.
- `KAM/CertificateSharp/V2/RouteAllLN.lean`: `routeV2AllLN := routeV2All.orElse routeBRefinedLN`, three `rfl` theorems.
- `KAM/CertificateSharp/V2/Tests/RouteBLN.lean`: the toy tests.
- `KAM/Root/CertificateSharp.lean`: four lines from `gen_root_imports.py`. No module imports a root.

**Python changed:** `check_modconstb_v2.py`, `v2_adapter.py`, `smalldiv.py` (both), `smalldiv_sup.py`, `thresholds_v2.py`,
`optimize.py`, `lunar_oracle.py`.

**Python new:** `scripts/certifier/check_v2_adapter.py`, `scripts/apost_sharp/check_smalldiv_shapes.py`,
`scripts/apost_sharp/structured_b.py`.

**Docs:** `CERTIFIER-V2-FIXES.md` (status table), `CERTIFIER-SHARPNESS.md` (one stale sentence about the adapter's default),
`studies/V2-STRUCTURED-B.md`, this file.

## Approach

- **F1.** `mkp` reads the cap through `cap_sK`, the same option and default as `stageB`. The comparison loops over
  `dk_cap` on and off. Each of the 32 cases also runs a negative control at the other convention's cap, which must differ.
  The theorem's `σK − μ/2` is untouched.
- **F3.** The default directory comes from the adapter's real path. `_load` keeps one module per resolved directory. During
  the import every mirror module name resolves to that directory; afterwards `sys.path` and the caller's `sys.modules`
  entries are restored, also on failure. This matters in practice: `scripts/certifier/smalldiv.py` has the same name as
  the mirror's `smalldiv`, and the old code also popped the wrong `sys.path` entry.
- **F3 side effect.** `thresholds_v2.py` imported `smalldiv_sup` lazily, which only worked because `sys.path` stayed
  polluted. It now imports it at the top.
- **F4.** `check_finite` and `check_two_freq` guard `S_finite`, `c_freq`, `gamma_inf`; finiteness guards go on the general
  formulas (`c_classical` keeps `n = 3`, which SJS uses). The same `n` trap was in `certifier/smalldiv.gamma_spec`. Shape
  guards also went into `optimize.gamma_spec` and `lunar_oracle.dioph_gamma`, and `thresholds_v2` now passes its `n`.
- **F2.** `refinedBLNTest` is `checkHamClaim && checkFrameLN && refinedBCore` at the unchanged `RefinedBWit`. Because
  `FrameFacts` carries `bT` and existing files are frozen for this work, `refHypB_ofLN` and `refinedBCore_soundLN` repeat
  the two proofs at `FrameFactsLN`. Route A's torsion majorant and the base `checkTorsion` are unchanged.

## Checks and output

```text
$ nice -n 10 python3 -B -I scripts/apost_sharp/check_modconstb_v2.py      # exit 0
R1 cross-check (32 cases, both cap conventions): all equal
cap-mismatch negative controls detected: 32 / 32
monotonicity violations under Dom (plain/iso, L10 on/off): 0 / 6423
$ nice -n 10 python3 -B -I scripts/certifier/check_v2_adapter.py          # exit 0
v2_adapter checks: all passed
$ nice -n 10 python3 -B -I scripts/apost_sharp/check_smalldiv_shapes.py   # exit 0
small-divisor shape checks: all passed
$ lake build --no-build KAM.CertificateSharp.V2.Tests.RouteBLN KAM.CertificateSharp.V2.Tests.RouteAll \
    KAM.CertificateSharp.Hybrid.Iso
All targets up-to-date (3653 jobs).
```

- **Mutations:** with `mkp` reverted to the raw cap, or with the convention swapped, F1 exits 1. Against the original
  files, `check_v2_adapter.py` and `check_smalldiv_shapes.py` both exit 1.
- **F4 values:** the JSON of 20 benchmark groups, `smalldiv.py`'s printed output and `certifier/smalldiv.py`'s `gamma_spec`
  were captured before the edits and are byte-identical after.
- **F3 value:** `log10_threshold` on a synthetic package gives `-10.70791717325115` through the old and the new adapter.
- **`route_b_lean_mirror.py`** still runs, reporting R1 at `-12.224`.
- **Toy tests:** an ordinary witness passes; `bT = 0` passes `routeBRefinedLN` and is rejected by `routeBRefined`; each of
  `bL`, `bN`, `bNt` understated is rejected although `refinedBCore` alone accepts that mutant; an understated `dx` is
  rejected; both toy torus theorems hold. `refinedBLNTest_bT` proves independence from `bT` for every certificate, by
  `rfl`, and `refinedBLNTest_of_refinedBTest` proves the old acceptance implies the new.
- **Builds:** targeted only, one at a time, under a 4 GB scope. No application library was built.

**`scripts/lint_sources.sh`: exit 1, from the ABI step only.**

- Line length, modules (`check_lean_modules: PASS`), root check, errata and `FROZEN-ANCHOR GUARD OK` all pass.
- `abi_hashes.py --check` stops at `object file ... KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean` missing.
- The cause is the build seed: 43 of the 179 anchor files have no olean here, and the main checkout's `.lake` lacks this
  one too. This branch touches no frozen file.
- Finishing it needs a wider build than a targeted one, so I left it. **The ABI check has not been run on this branch**;
  the landing build should run it.

## Axioms

```text
checkTorusCertificateV2_routeBRefinedLN_sound  [propext, Classical.choice, Quot.sound]
refinedBCore_soundLN                           [propext, Classical.choice, Quot.sound]
checkFrameLN_sound                             [propext, Classical.choice, Quot.sound]
refinedBLNTest_bT                              [propext, Classical.choice, Quot.sound]
refinedBLNTest_of_refinedBTest                 [propext, Classical.choice, Quot.sound]
toyB_refinedBLN_torus                          [propext, Classical.choice, Quot.sound]
toyB_routeV2AllLN_torus                        [propext, Classical.choice, Quot.sound]
```

## Measured savings of F2

**Toy `toyB`:** one `decide +kernel` in a fresh process, median of 3, `Elab.async=false`, minus the import baseline of 2.43 s.

| Check | Net wall | Peak RSS |
|---|---:|---:|
| `checkFrameL` / `checkFrameN` / `checkFrameT` | 0.24 s / 0.44 s / 1.33 s | 3.48 / 3.52 / 3.71 GiB |
| engine test, `routeBRefined` → `routeBRefinedLN` | 2.05 s → 1.40 s (32 %) | 3.82 → 3.67 GiB |
| whole certifier, same two engines | 2.80 s → 2.92 s (no saving) | 3.90 → 3.90 GiB |

The whole certifier shows no saving, and the difference is within run-to-run spread. The base `checkTorsion` builds the
same torsion models, which is the likely reason: only the small row pass is really dropped. I did not isolate that.

**Representative shard: LG00 L = 20, `KAM.LG00Cert.Final.FrameT`.** This is the one module a sharded route-B certificate of
that size would drop; the torsion literals stay, because `checkTorsion` needs them.

| Source | CPU | Wall | Peak RSS |
|---|---:|---:|---:|
| LG00 ledger | 279.8 s | 4:41 | 2.81 GB (2.62 GiB) |
| re-run here, read-only, nice 10, under load | 346.6 s | 5:52 | 5.00 GB, 4.23 GB of it the import baseline |

That is **0.26 % of the certificate's 30.11 CPU-h** (0.32 % at the re-run's figure). LG00 uses route A today, so this is
what a route-B run would save, not a saving anyone gets now. No application speedup should be claimed from F2. Its value is
the cleaner check: a route-B certificate no longer has to supply a bound the theorem never reads.

## #1 verdict: do not implement

Details in [V2-STRUCTURED-B](../studies/V2-STRUCTURED-B.md).

| Data | `c_Th`: `2 M₁` → structured | `c_DTh`: `2 M₂` → structured | threshold gain |
|---|---:|---:|---:|
| lunar N = 65 | 4 → 2.10 | 2.99 → 1.50 | +0.48 (classical), +0.44 (frequency) |
| LG00 L = 20 | 498 → 397 | 10340 → 9713 | +0.11 |

- `c_Th` binds (`J2` through the torsion cap `t`, and `J3 cap5` on the lunar data). `c_DTh` does not: +0.000 alone.
- No acceptance changes in any case evaluated. Route A stays ahead with frequency sites on the lunar data (-14.12 against
  -14.68) and with classical sites on LG00 (-15.10 against -17.85).
- On LG00 improvement 2 would gain +1.6 decades, about 15 times more. It is a theorem-interface change and was not built.

## Uncertainties

- The #1 figures are mirror thresholds, not kernel-checked witnesses, and route B's frequency sites are design floats.
- The inputs were reconstructed, because SO's generated state and `gen_L20/state.pkl` are on a volume not mounted here.
  They reproduce the landed claims and LG00's reported route-A threshold, `7.9·10⁻¹⁶`.
- The lock's librational torus was not evaluated. "Lunar" means the two N = 65 band tori.
- A full `lake build` was not run. The landing build covers it.

## Deviations and errata

- **Memory:** the LG00 shard probe peaked at 5.0 GB RSS, above the brief's 4 GB per process. It ran under a 4 GB
  `MemoryMax` scope that did not trigger, and 4.23 GB of that RSS is the import baseline. It is well under the 10 GB guard.
  It read the `lg00-cert` build read-only; that worktree's `git status` is clean.
- **Beyond the brief's file list:** two regression scripts, the F4 guards in `optimize.py` and `lunar_oracle.py`, the
  `thresholds_v2.py` import change and the `CERTIFIER-SHARPNESS.md` sentence. Each follows directly from F3 or F4.
- **Not fixed:** `scripts/sjs/sjs_thresholds.py` line 25 has the same personal-worktree default as F3. The brief names only
  the adapter.
- **Suspected errata in pinned sources:** none.
