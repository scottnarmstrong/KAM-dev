# Handoff V2-PUBLIC: a reproducible public workflow for the v2 certifier (improvement #8)

**Superseded in part by [V2-PUBLIC-FIX](V2-PUBLIC-FIX.md)** (AUDIT-V2-PUBLIC-1 and the owner's decisions:
the complete route-B pre-check, the clause-by-clause diagnostics, `Micro.real_torus` with the torus location,
SHA-pinned actions and a checksummed elan, and scipy split into `scripts/requirements-scipy.txt`). Rows
corrected in place are marked *(FIX)*.

Worker: V2-PUBLIC. Branch `v2-public` (from `origin/main` `01d36418`), worktree
`/home/scott/KAM-dev-worktrees/v2-public`. Brief: `/home/scott/kam-tools/briefs/V2-PUBLIC.md`. Source:
[CERTIFIER-V2-IMPROVEMENTS §8](../design/CERTIFIER-V2-IMPROVEMENTS.md#8-provide-a-reproducible-public-workflow).
Commits: `39110bc3` (environment, diagnostics, profile tool, CI driver), `284e1652` (MicroReading,
forced_micro profile, example specs), `215b5fb1` (workflow, receipt draft), `7d00f086` (quickstart,
receipt, README), and this handoff.

## Gate status

* **Reproduce a small perturbed example from a fresh checkout with documented commands: met for the
  producer, and for the kernel check at this commit's sources.** A depth-1 clone of the branch, then
  `scripts/setup_python_env.sh`, then the documented steps 2–4 of
  [QUICKSTART.md](../../certifier/QUICKSTART.md), produced the six `Quick*.lean` modules **byte for
  byte identical** to those the kernel accepted in this worktree (`lake build …QuickRoutes`, 27 s). The
  `#print axioms` of `Quick.sharp_torus`, `frozenA_torus`, `frozenB_torus` and `real_torus` is the
  standard three. Not run: a from-scratch Lean build in the fresh clone. That is 421 modules, and
  Lake's default parallelism at 2.5 GB per process would break the memory policy. Its cost is measured
  per module instead (below).
* **Tell what an application proves from its public receipt:** [RECEIPT.md](../../certifier/RECEIPT.md)
  has a template with nine fixed sections (identification, model, chart, frequency, route, exact
  theorem, axioms, kernel ledger, what is not proved) and the `Quick` run filled in.

## Files

New:

| File | Content |
|---|---|
| `scripts/requirements.txt` | the core manifest *(FIX)*: `numpy==2.5.3`, `mpmath==1.3.0`, each with every sha256 PyPI publishes (68 hashes); `scripts/requirements-scipy.txt` adds the optional `scipy==1.18.1` (61 hashes) |
| `scripts/lock_requirements.py` | rewrites / `--check`s those hashes from PyPI for the pinned versions |
| `scripts/setup_python_env.sh` | one-command setup: venv (default `.venv/`, git-ignored), `pip install --require-hashes --only-binary=:all:`, prints versions |
| `scripts/certifier/forced/forced_profile.py` | the `route_select.py` profile `forced_<tag>` of a forced-toy model spec (err and product pairs against `L = prune_digits`, mirror only) |
| `scripts/certifier/forced/forced_diag.py` | the named failure lines `FAIL/PASS route=… check=…: numbers, by how much` |
| `scripts/ci_checks.py` | named checks in groups `mirror`, `lint`, `lean`, with timings (the CI jobs, runnable locally) |
| `scripts/certifier/fixtures/route-select/forced_micro.json` | `forced_profile.py Micro --cost-s 38.4` (measured) |
| `KAM/CertificateSharp/V2/Tests/Forced/MicroReading.lean` (42 lines) | `Micro.real_torus`: `sharp_torus` read in real model coordinates (default build; the quickstart's pattern, kept under CI) |
| `.github/workflows/certifier-ci.yml` | `workflow_dispatch` only; jobs `mirror`, `lint`, opt-in `lean-fixtures` |
| `docs/certifier/QUICKSTART.md` | model → profile → route choice → certificate → kernel → reading, with the recorded outputs and costs |
| `docs/certifier/RECEIPT.md` | receipt template and the worked example |
| `docs/certifier/examples/quick-trial.json`, `quick.json` | the example model at the trial and the chosen truncation |

Existing files changed (all additive; outputs on success unchanged, checked below):

| File | Change |
|---|---|
| `scripts/certifier/forced/forced_build.py` | +3: on a failing landed base, FAIL lines before the existing assert |
| `scripts/certifier/forced/forced_routes.py` | `--frozen` *(FIX)*: evaluates every clause of `sharpTest`, `frozenCore` and `frozenBCore` (with `finalBF`) in the exact mirrors and, if one fails, prints a line per clause and exits 1 before writing. Before, a failing A or B crashed with a traceback, and a failing sharp route wrote a module the kernel rejects. Refined A: FAIL lines before the existing assert. `--B`: FAIL lines and exit 1 (before: an assert, or a `TypeError` on `None`) |
| `scripts/certifier/route_select.py` | `why_none`: a route-by-route explanation when no exact candidate or no sharp fallback is admissible; a guard printing why A.L8′ and l1-entry are skipped when no refined A threshold exists (before: `ValueError` from `max()`) |
| `scripts/certifier/forced/README.md` | rows for the two new scripts, a quickstart pointer, xlang count 31 → 52 (stale) |
| `.gitignore` | `/.venv/` |
| `KAM/Root/CertificateSharp.lean` | regenerated by `python3 -I scripts/gen_root_imports.py` (one import) |

No existing `.lean` file is edited, nothing under `KAM/Frozen`, `manifest`, `KAM/Certificate`,
`KAM/SpinOrbit`, `KAM/Sharp2`, `KAM/Iso`, `scripts/spin_orbit`, `certificates`, `docs/tracks/SO`, nor any
file owned by kamx-v2fix, kamx-conf or kamx-certside.

## Approach

1. **Dependencies.** An AST scan of the producer tools' transitive import closure
   (`scripts/certifier`, `…/forced`, `scripts/apost_sharp`, `scripts/packed`, and the 20
   `scripts/spin_orbit` modules they import; 89 files) finds three third-party packages. **numpy** and
   **mpmath** are used directly. **scipy** *(FIX: corrected)* is imported only by
   `scripts/spin_orbit/dsolve.py` (GMRES), which `hpsolve` imports; among the producer tools it is reached
   only through `rot_build.recompute_E`, which `rot_build.build` runs when `newE=True`. No producer tool in
   scope passes `newE` (only `scripts/spin_orbit/rot_scan.py` does), so none of them needs scipy at run
   time; `lunar_oracle.py` and `measure_residual.py` import `rot_build` but build with `newE=False`. Two
   lazily imported modules, `lg00_gen` and `lg00_chart` (`structured_b.py`, `route_profiles.py`), live
   only in the lg00 worktrees. I chose `requirements.txt` with every PyPI hash: one file, installable
   with stock pip (`--require-hashes`) on any platform PyPI serves, and no lock tool to install.
   `lock_requirements.py` moves pins reproducibly. The versions are those this machine ran
   (numpy 2.5.3, mpmath 1.3.0) plus the newest scipy (1.18.1) compatible with them.
2. **Quickstart.** `route_select.py` had no profile for the forced toy. `forced_profile.py` writes one
   from a model spec. On the toy, the truncation `L` is `prune_digits`; support is counted in genuine
   product pairs, which drive kernel cost, hence `--beta 1`. The example is a model of my own: `N = 10`,
   `ε = (3·10⁻¹², 10⁻¹²)`. `route_select` picks the sharp baseline at `L = 15` (measured err
   `2.33·10⁻¹⁹`, margin 1.03 decades, 1308 pairs) instead of the trial `L = 27` (9716 pairs). The
   one-command emitter `forced_routes.py --frozen` proves sharp, frozen A and frozen B together. The doc
   explains why the `best` row (`A.refined.classical`) is not followed for the toy.
3. **Diagnostics.** One line format,
   `FAIL route=<route_select name> check=<Lean/mirror check>: <numbers>, <margin or log10(err/e*)>`.
   It covers the landed base sub-checks (`checkInvariance`, `checkEnergy`, …), `sharpTest`
   (smallness/displacement), `frozenCore` parts, `finalB` smallness, `routeBOk` failure, the refined-A
   mirror and compiled-Lean verdicts, and route_select admissibility (threshold / margin / sites /
   precision). All lines go to stderr, only on failure paths.
4. **CI.** `scripts/ci_checks.py` is the single entry point, so CI and local runs are identical. Groups:
   * `mirror` (10 checks, Python only): `check_modconstb_v2`, `check_smalldiv_shapes`, `hybrid_numq`
     (validate), `route_b_lean_mirror`, `check_v2_adapter`, `fiber3_xlang --check`,
     `route_select --validate` against `validation.json` and `validation.log`, forced-toy and
     `gen_stepbq` regeneration (14 files), `forced_micro` profile regeneration, and a regression of the
     failure diagnostics;
   * `lint`: `lint_sources.sh` with its one Lean-dependent step (ABI hashes) stubbed, by the
     guard-mutation suite's own regex, failing closed if the script changes shape; plus a pin check
     that every third-party import is pinned with hashes;
   * `lean` (opt-in job, after `lake build` of `Tests/Forced/*` and `Fiber3XLang`): `forced_xlang.py`,
     52 compiled-Lean comparisons.
5. **Receipt.** Aligned with the application contract's table. The "does not prove" list is mandatory.

## Checks and their output

* Fresh clone (`git clone --depth 1 --branch v2-public file://…`, at `215b5fb1`):
  `scripts/setup_python_env.sh` gives `python 3.13.13, numpy 2.5.3, mpmath 1.3.0, scipy 1.18.1` (6.4 s).
  Then `.venv/bin/python -I scripts/ci_checks.py --group mirror` gives `10 checks, 0 failed, 89.0s`, and
  `--group lint` gives `2 checks, 0 failed, 119.5s`. The quickstart steps 2–4 produce the six `Quick*.lean`
  modules identical to the kernel-checked ones, and step 7 leaves `git status` clean.
* Worktree: `python3 -I scripts/ci_checks.py --group lean` gives `PASS forced-xlang 25.4s`
  (`cross-language agreement: ALL AGREE (52 comparisons)`).
* Success output unchanged: `route_select.py --validate --json …` is byte-identical to
  `validation.json` and `validation.log` after every edit. `forced_build`/`forced_routes --frozen`
  regenerate Tiny, Micro and TinyC2 identically (`forced-regen`).
* Pinned PyPI wheels against the conda-forge numpy that wrote the fixtures: every Lean file and JSON
  fixture is identical, except the wall-clock field `report.check_seconds` (0.4 against 0.3), which the
  comparison ignores.
* Negative test: a one-byte change to `MicroData.lean` in a scratch copy gives
  `FAIL forced-regen … differ: KAM/CertificateSharp/V2/Tests/Forced/MicroData.lean`.
* Failure paths exercised: `forced_routes.py Tiny --frozen` gives the three FAIL lines and `nothing written`,
  exit 1. `forced_build.py` with `err_slack 1/2` gives
  `FAIL route=landed-base check=checkEnergy: … value/err 10^0.30`. `route_select forced_micro --margin 30`
  gives 8 `FAIL route=… check=margin` lines; `--margin 12` gives the sharp-fallback explanation only.
* Lean: `lake build KAM.CertificateSharp.V2.Tests.Forced.MicroReading` gives `Built … (1.2s)`.
  `lake build KAM.Root.CertificateSharp` gives `Build completed successfully` (126 s; it also built 31
  pre-existing `CertificateSharp` modules missing from this worktree's snapshot; none edited; peak
  4.3 GB in that run, where the root part's import load alone is 3.7 GB). Then
  `gen_root_imports.py --check`: OK; `check_lean_modules: PASS (4124 Lean files)`.
* `scripts/lint_sources.sh`: every file-based layer passes (`check_lean_modules: PASS`,
  `FROZEN-ANCHOR GUARD OK`, no forbidden pattern, width or size finding). The ABI-hash layer **could not
  run here**: `object file …/KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean … does not exist`.
  The sealed anchors' closures have 47 modules unbuilt in this worktree's snapshot. This branch touches no
  frozen file and nothing a frozen module imports, so I did not build them. The landing gate should run
  the full lint on the landed build.
* Python hygiene: every new or edited line is ≤ 120 characters (three pre-existing longer lines remain in
  `forced_build.py`/`forced_routes.py`), and `py_compile` passes on all touched files.

## Axioms

```
'KAM.CertificateSharp.V2.Forced.Micro.real_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.Forced.Micro.sharp_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Local example (not committed): `Quick.sharp_torus`, `Quick.frozenA_torus`, `Quick.frozenB_torus` and
`Quick.real_torus` all use the standard three.

## Measurements

| What | Measured (AMD Ryzen 7 7700, 16 threads) |
|---|---|
| CI `mirror` | 83 s (worktree), 89 s (fresh clone); `route_b_lean_mirror` is 46 s of it |
| CI `lint` | 113–120 s (`lint_sources.sh` without ABI on 4124 Lean files) |
| CI `lean` | `forced_xlang` 25 s, after the build below |
| Lean fixtures (`Tests/Forced/*` (32) + `Fiber3XLang`, KAM closure) | 445 modules; 1235 CPU-s / 1531 s serial elaboration (`lake env lean` per module); critical path 169–177 s; simulated 313–407 s on 4 cores, 171–184 s on 16; ≤ 2.51 GB per process |
| Quickstart step 0 (`MicroReading` closure) | 421 modules; 1150 CPU-s; simulated 5–6 min on 4 cores, ~3 min on 16 |
| Mathlib cache | not measured (already present): 6.7 GB unpacked |
| Quickstart producer steps | profile 10.5 s, route_select 1.4 s, forced_build 1.6 s, forced_routes 1.0 s (≤ 40 MB) |
| Quickstart kernel step | 6 modules, 27.6 s module time, 27.1 s wall, ≤ 2.0 GB; reading 3.5 s, 3.6 GB |
| Setup | venv 225 MB; wheels 52.5 MB (numpy 16.7, scipy 35.3, mpmath 0.5) |

GitHub runners are slower per core, so the CI numbers should be expected at 1.5–2.5×. That factor is an
estimate; I could not measure on GitHub.

Findings from the measurements:

* **Micro is over-resolved.** With its measured cost, `route_select forced_micro --beta 1` finds the
  sharp route admissible at `L = 15` (measured err `6.02·10⁻²⁰`, margin 1.67 decades), at about 1/11 of
  the predicted kernel cost of its `L = 27`.
* **route_select's cost model has no per-module fixed cost.** It predicts `Quick` at
  38.4 × 1308/9716 ≈ 5 s, but the kernel step took 27 s: each module spends about 1.5–2 s loading
  imports. This is negligible at the CPU-hour scale of the lunar and LG00 profiles, and dominant for toys.
  The cost column also rounds to 0.001 CPU-h (3.6 s), so all toy candidates tie and margin breaks the tie.
  Both are documented; route_select is unchanged.

## Owner questions

1. **CI triggers.** *Decided: manual only (`workflow_dispatch`).*
2. *(Removed: KAM-dev itself is the public repository, and the workflow lives in it. The quickstart now
   starts from `git clone https://github.com/scottnarmstrong/KAM-dev.git`.)*
3. **Supply chain.** *Decided (V2-PUBLIC-FIX): actions pinned by full commit SHA, checkout without
   persisted credentials, elan v4.2.4 from its release tarball checked against its sha256.*
4. **Lean fixtures job.** It needs about 1235 CPU-s of KAM build, the Mathlib clone and cache, and a
   `.lake/build` cache keyed on the Lean sources. Is that acceptable as an opt-in job, and on which runner
   size? The standard 4-vCPU/16-GB runner fits: at most 2.5 GB per Lean process.
5. **scipy.** *Decided (V2-PUBLIC-FIX): split out into `scripts/requirements-scipy.txt`
   (`setup_python_env.sh --with-scipy`); the core and the quickstart need only numpy and mpmath.*
6. **Python range.** The pins need Python ≥ 3.12, and setup warns off 3.13. Pin 3.13 strictly?
7. **The `Quick` example.** Check it in as a fixture (6 modules, about 28 s in the default build), or
   keep it generated by the user as now? `Micro` and `Micro.real_torus` are the checked-in analogue.
8. **`route_select` for small certificates.** Add a per-module fixed cost and a finer cost unit? Not
   done, because it would change the validated lunar and LG00 outputs.

## Suspected defects and deviations (tooling; no pinned-source errata)

* `scripts/apost_sharp/check_modconst_v2.py` fails on `main`: it reports `DIFF` for `CDK` and `QtN`, then
  raises `KeyError: 'Q'` at line 168. This is the v1 cross-check against `KAM/Sharp2/ModConstants.lean`,
  presumably stale since the constants were refactored. It is excluded from CI and not fixed (out of
  scope); its route-B sibling `check_modconstb_v2.py` passes.
* `hybrid_numq.py` would exit 0 even on `validate: FAIL`: its `__main__` ignores the result of `validate()`.
  `ci_checks.py` requires the `validate: PASS` line instead (it passes today).
* The shared `Format.lean`: `forced_build.py` rewrites it at the tag's precision `P`, so a tag with
  `P ≠ 96` breaks every checked-in toy. This is documented in the quickstart; the tool is unchanged.
* The forced-toy certificate's Gram and torsion inverses are float (numpy) results rounded at 2⁻⁴⁰.
  Byte identity across CPUs or BLAS builds is therefore expected, not guaranteed. It held between
  conda-forge numpy and the PyPI wheels here. Validity does not depend on it: the kernel checks whatever
  is emitted.
* Not pinned: `sympy` (only `scripts/wave/w0_checks.py`, not a producer tool) and the out-of-tree
  `lg00_gen`/`lg00_chart`, which the pin check allows by name.
* Deviation: `forced_routes.py --frozen`, `--B` now exit 1 with diagnostics where they previously crashed
  or wrote a module the kernel would reject. Success paths are byte-identical.

V2-PUBLIC DONE
