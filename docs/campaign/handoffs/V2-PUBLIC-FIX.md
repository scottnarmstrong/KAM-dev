# Handoff V2-PUBLIC-FIX: the audit changes and the owner's decisions

Worker: V2-PUBLIC. Branch `v2-public`, worktree `/home/scott/KAM-dev-worktrees/v2-public`, on top of
`5bb4a1aa` (the V2-PUBLIC handoff). Inputs: AUDIT-V2-PUBLIC-1 (`kam-tools/audits/AUDIT-V2-PUBLIC-1.md`)
(PASS WITH CHANGES) and the orchestrator's messages of 1 November 2026 (Scott's decisions: CI stays
manual-only; actions pinned by SHA with checksummed elan and no persisted credentials; scipy split out;
KAM-dev is the public repository). The original handoff [V2-PUBLIC](V2-PUBLIC.md) is corrected in place
where it was wrong or superseded (rows marked *(FIX)*).

## Changes

| Item | Change | Files |
|---|---|---|
| **C1** (required) | The `--frozen` pre-check now evaluates **every clause of `frozenBCore`** in the exact mirror, `finalBF` included. Those clauses are `0 < X*`; `μ < σK`, `μ < σB`, `σB − μ < sB`; `wfOk`/`fitsOk`/`initOk`; `okB` (J1–J4); `sitesOk` and `tailOk` (`classicalOk`); and `finalB` smallness, **displacement** `max(c2Q, c3Q)·err ≤ disp·γ²ρ^{2τ}` and **σω** `disp < (σω − s)·freqNormLo`, plus `finalBF`'s sharp displacement. Sharp (`sharpTest`, both clauses) and frozen A (`frozenCore` through `frozen_A`'s assert) were already complete. `c3Q` (`freqSum`) was not in `route_b_lean_mirror.py`; it is now `forced_diag.c3B`. The QUICKSTART sentence now reads: every clause of the three route tests is evaluated in their exact mirrors, and nothing is written if one fails; the mirrors' agreement with Lean is tested in CI. | `forced_diag.py` (`routeB_parts`, `c3B`, `frozenB_lines`), `forced_routes.py` (pre-check), `QUICKSTART.md` step 4, `V2-PUBLIC.md` row |
| C1, new check | `forced_diag.py --xlang Micro` compares the new mirror with the compiled Lean on `Micro.frozenBWit`. It checks `c1Q`, `c2Q` and `c3Q` exactly, then `frozenBCore`, then `finalBF` and `finalB` at three values of `disp`: the certificate's, one between the two displacement thresholds, and one below both. Each displacement clause is thereby seen to pass and to fail. It is in CI as `routeB-xlang` (group `lean`). | `forced_diag.py`, `ci_checks.py`, workflow |
| **C2** | `frozenA_lines` prints the three `finalOk` clauses separately (`frozenCore.final.smallness`, `.displacement` with its needed `disp`, `.sigma_omega`), plus a line per other failing `frozenCore` part. | `forced_diag.py` |
| **C3** | `route_select.py`: "(errors above)" becomes "(errors below)"; the per-route error lines are logged after it. | `route_select.py` |
| **C6** | The stubbed `lint_sources.sh` runs from memory: `sh -c "<stub>" scripts/lint_sources.sh`, with `$0` set to the original path from which the script finds the root. Nothing is written into the checkout, and concurrent runs cannot collide. The docstring says so. | `ci_checks.py` |
| **C5** | `Micro.real_torus` adds the location of the torus, `∀ θ, ‖k θ − realRestriction cert.K θ‖ ≤ disp` (`CertifiedTorusAt.norm_realRestriction_sub_le`), and `1 < s∞ < σω`. The QUICKSTART pattern `Quick.real_torus` and the RECEIPT example are updated the same way. | `MicroReading.lean` (47 lines), `QUICKSTART.md` step 6, `RECEIPT.md` |
| C4 nit | The version gate in `setup_python_env.sh` accepts 3.20–3.99 with a note instead of a wrong error. | `setup_python_env.sh` |
| **Actions** (owner) | Every action is pinned by full commit SHA with its release in a comment: `actions/checkout@3d3c42e5…` (v7.0.1, 2026-07-17), `actions/setup-python@5fda3b95…` (v7.0.0, 2026-07-20; v7.1.0 from 2026-10-22 was passed over as too recent), `actions/cache@55cc8345…` (v6.1.0, 2026-06-23). All three run on `node24`, and the inputs used (`persist-credentials`, `python-version`, `path`/`key`/`restore-keys`) exist in each `action.yml` at that SHA. These are lightweight tags; each SHA was confirmed as a commit through the GitHub API. Every checkout sets `persist-credentials: false`. | workflow |
| **elan** (owner) | Instead of `curl …/master/elan-init.sh \| sh`, the job downloads `elan-x86_64-unknown-linux-gnu.tar.gz` of release **v4.2.4** (2026-08-25), checks it with `sha256sum -c` against `42b94d42…31f63` (GitHub's published asset digest, matched by my own download), extracts it, and runs `elan-init -y --no-modify-path --default-toolchain none`. | workflow (`env: ELAN_VERSION, ELAN_SHA256`) |
| **scipy** (owner) | `scripts/requirements.txt` = numpy 2.5.3 + mpmath 1.3.0 (68 hashes). New `scripts/requirements-scipy.txt` = `-r requirements.txt` + scipy 1.18.1 (61 hashes): pip's hash-checking mode needs scipy's dependency numpy hashed in the same install. `setup_python_env.sh --with-scipy` installs it; the default is the core only. `lock_requirements.py` rewrites and `--check`s both files. The CI pin check reads both and allows the optional package only in its one importer, `scripts/spin_orbit/dsolve.py` (`OPTIONAL` in `ci_checks.py`). CI and the quickstart install the core only. | `requirements*.txt`, `setup_python_env.sh`, `lock_requirements.py`, `ci_checks.py`, QUICKSTART, RECEIPT |
| **Public repository** (owner) | The private/public-mirror owner question is removed. The quickstart starts from `git clone https://github.com/scottnarmstrong/KAM-dev.git`, and the receipt names the repository. | `V2-PUBLIC.md`, `QUICKSTART.md`, `RECEIPT.md` |

**Correction to V2-PUBLIC.** I had written that `lunar_oracle.py` and `measure_residual.py` reach scipy
through `rot_build.recompute_E`. They do not. `recompute_E` runs only from `rot_build.build(...,
newE=True)`, and the only caller passing `newE` is `scripts/spin_orbit/rot_scan.py` (SO track). Both tools
call `build` without it. So no producer tool in scope needs scipy at run time; it sits in the import
closure only through `hpsolve` → `dsolve`. Corrected in V2-PUBLIC's approach item 1.

## Checks and their output

* Route-B mirror against compiled Lean (`FORCED_WORK=… python3 -I scripts/certifier/forced/forced_diag.py --xlang Micro`):
  `route-B mirror against Lean: ALL AGREE (10 comparisons)`. `c1Q`, `c2Q` and `c3Q` agree exactly.
  `frozenBCore` is `true`. `finalBF` is true/false/false and `finalB` true/true/false at
  `disp = 10⁻³`, `1.27·10⁻¹⁷` and `5.91·10⁻²⁰`.
* On Micro all 12 route-B clauses PASS, and the three `frozenCore.final` clauses PASS.
  `forced_routes.py Tiny --frozen` prints one line per clause (FAIL: sharp smallness, frozen-A
  `final.smallness`, B `finalB.smallness`; every other clause PASS), then `nothing written`, exit 1.
* `python3 -I scripts/ci_checks.py`, in the **core-only** venv (no scipy):
  `--group mirror` gives `10 checks, 0 failed, 124.1s` (the machine was loaded). `--group lint` gives
  `2 checks, 0 failed, 116.0s`; a watcher polling `scripts/.ci*` every 2 s saw no file during the lint run.
  `--group lean` gives `2 checks, 0 failed, 19.1s` (`forced-xlang`, `routeB-xlang`).
* `route_select --validate` remains byte-identical to its fixtures (the `route-select` check), and the
  forced-toy regeneration is unchanged (`forced-regen`).
* Pin rules: `requirements-pins` reports third-party `['mpmath', 'numpy', 'scipy']`, core pins
  `{'mpmath': '1.3.0', 'numpy': '2.5.3'}`, optional `{'scipy': '1.18.1'}`. In a negative test, an added
  `import scipy` in a scratch copy of `route_select.py` gives `FAIL … OPTIONAL PACKAGE IMPORTED ELSEWHERE`.
  `lock_requirements.py --check` gives `matches PyPI` for both files.
* Setup: the default prints `python 3.13.13, numpy 2.5.3, mpmath 1.3.0` (86 MB venv; scipy not importable).
  `--with-scipy` prints `…, scipy 1.18.1` (225 MB).
* Workflow: it parses; its only trigger is `workflow_dispatch`; every `uses:` matches `@<40 hex>  # vX.Y.Z`;
  every checkout has `persist-credentials: false`. I ran the elan step locally with a scratch `HOME`: the
  sha256 is OK and `elan 4.2.4 (227caca13 2026-08-25)` is installed. With a wrong checksum it printed
  `FAILED`; under `bash -eo pipefail` the step exits 1 and installs nothing.
* Lean: `lake build KAM.CertificateSharp.V2.Tests.Forced.MicroReading` gives `Built … (6.4s)`.
  `gen_root_imports.py --check` passes. `check_lean_modules: PASS (4124 Lean files)`. For `Quick` I
  regenerated the files in the worktree; they are byte-identical to before. `lake build …QuickRoutes`
  succeeds in 49 s under load. The updated QUICKSTART snippet elaborates. All `Quick*` files and their
  build outputs were then deleted.
* `scripts/lint_sources.sh`: `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, and no pattern, width or
  size finding. As in V2-PUBLIC, the ABI-hash layer cannot run in this worktree: the frozen modules are
  unbuilt in its snapshot, and this branch touches none of them.

## Axioms

```
'KAM.CertificateSharp.V2.Forced.Micro.real_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.Forced.Micro.sharp_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.Forced.Quick.sharp_torus' depends on axioms: [propext, Classical.choice, Quot.sound]   (local)
'Quick.real_torus' depends on axioms: [propext, Classical.choice, Quot.sound]                                   (local)
```

## Owner questions (remaining)

From V2-PUBLIC, still open: 4 (the opt-in Lean job's runner and cache policy), 6 (Python 3.13 strictly?),
7 (check in the `Quick` example?), 8 (`route_select` cost model for small certificates). New: the action
pins are recent majors (checkout v7, setup-python v7, cache v6) rather than the v4/v5/v4 the first draft
named. When should they be bumped, and by whom? Dependabot cannot run on a manual-only workflow without
being enabled separately.

## Suspected defects and deviations

No pinned-source errata. Tooling, already reported: `check_modconst_v2.py` fails on main. New deviation:
`forced_routes.py --frozen` now imports `forced_diag` on its success path for the pre-check. It prints
nothing there, so the outputs stay byte-identical.

V2-PUBLIC-FIX DONE
