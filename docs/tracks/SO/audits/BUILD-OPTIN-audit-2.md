# BUILD-OPTIN independent audit 2

**Verdict: PASS.** F1–F3 are closed for the reviewed fix. The landing gate checks every application after the core build, rejects stale certificate data before any such build, and handles stale light modules serially under the cap. All generated roots/parts have `public section`; fresh root checking and lint pass. No blocking regression was found in the fix diff.

## Scope and provenance

- Worktree: `/root/code/KAM-inp-buildoptin`; HEAD verified as `4edf977e72815f84a9f3ad184434364f4cc23a1f`.
- Exact fix diff: `git diff ade92a4f 4edf977e`, 42 files. This is a round-2 fix audit, not a fresh theorem/proof or full-package audit.
- Read the repository rules, PLAN.md, DECISIONS.md including D51, original audit brief, round-1 report, and handoff including “Audit 1 findings (FAIL) and fixes.” The same focused, refute-first audit method applies.
- Frozen input fingerprint: SHA-256 `9b3351e08c738c8f0bbb683735f99aac62f272353c4da01531c475432d30b3f8` of the sorted concatenation of `sha256 + "  " + path + "\n"` for all 42 changed files at this HEAD.
- Read-only inspection and in-memory mocks only, except creation of this report. No source edits, commits, pushes, actual landing, rebuilding, kernel replay, process termination, or external access. All real Lean/Lake work was serialized with `LEAN_NUM_THREADS=1`; real Lake invocations used only `build --no-build`.

## F1 — CLOSED: unconditional application freshness gate

At this HEAD, `scripts/prebuild_heavy.py:97–113` iterates **all** entries in `cfg['applications']` and calls the actual `stale([lib])`, which issues `lake build --no-build <Lib>`. There is no Git-path selection and no exclusion of shared-core, lakefile, toolchain, manifest, or mapping changes.

For each reported frontier, lines 101–105 scan **all** returned names for certificate-data membership before selecting a light module to build. Any data target returns 3 immediately. Otherwise only `todo[0]` is sent to the capped builder, and the library freshness check repeats. A repeated stale light target returns 1 rather than looping indefinitely.

### Fresh mocked-subprocess refutation

Ran `LEAN_NUM_THREADS=1 python3 -B -I - <<'PY' ... PY`, loading the real file with:

```python
ns = runpy.run_path('scripts/prebuild_heavy.py', run_name='audit_readonly')
cfg = ns['roots'].load_config()
with patch.object(ns['subprocess'], 'run', fake_run):
    rc = ns['check_all'](cfg)
```

Only `subprocess.run` was mocked. The real `check_all`, `stale` parser, `heavy` predicate, and `capped_build` ran. The fake subprocess accepted only exact `lake build --no-build <Lib>` queries or the exact real `CAP + ['lake', 'build', target]` build command; it asserted that every simulated build target was non-heavy. Return codes and build counts were asserted for every scenario. No shell command or Lake process was launched by these mocks.

`[]` below means an up-to-date response. Successive frontiers were supplied in Lake's `Some required targets logged failures:` format, with nonzero return code 3; current targets returned 0. Path-change labels describe why the corresponding application is stale: the new gate deliberately receives no changed-path input.

| Requested scenario | Band frontiers supplied | Result | Simulated capped builds |
|---|---|---|---|
| Application edit | `KAM.SpinOrbit.Data.Format` | 3 | none |
| Shared core Model edit | `KAM.SpinOrbit.Data.CsegSupport`, `KAM.SpinOrbit.Data.Upper.Action0` | 3 | none |
| Lake/options edit | `KAM.SpinOrbit.Data.Lower.Action0` | 3 | none |
| Mapping edit, only generated roots stale | `KAMLunarBand.SpinOrbit.Data.Upper` → `KAMLunarBand.SpinOrbit.Data.Lower` → `KAMLunarBand` → `[]` | 0 | those three light targets, sequentially |
| Core-only unrelated edit, applications current | `[]` | 0 | none |
| Stale light-only assembly | `KAM.SpinOrbit.LunarFinalR2V2` → `KAMLunarBand.SpinOrbit.Top` → `[]` | 0 | those two light targets, sequentially |

Every successful scenario also asserted that `KAMLunarLock` was queried. Additional attempts to refute the heavy-build barrier gave:

| Adversarial scenario | Result | Simulated capped builds |
|---|---|---|
| Light target first and heavy Format second in the same frontier | 3 | none |
| Band current; lock frontier `KAM.SpinOrbit.Data.LockN65.Action0` | 3 | none |
| First frontier light; subsequent frontier heavy Format | 3 | one light target only |
| Same light target remains stale after its build | 1 | one light target only |
| Failed Lake query with no parseable failure list | `SystemExit` diagnostic | none |
| Capped light build returns nonzero | `SystemExit(1)` | failed light attempt; no continuation |

Exact summary output:

```text
application edit rc=3 checks=1 capped builds=[]
shared core Model edit rc=3 checks=1 capped builds=[]
lake/options edit rc=3 checks=1 capped builds=[]
mapping edit/light roots rc=0 checks=5 capped builds=['KAMLunarBand.SpinOrbit.Data.Upper', 'KAMLunarBand.SpinOrbit.Data.Lower', 'KAMLunarBand']
core-only unrelated edit rc=0 checks=2 capped builds=[]
stale light-only assembly rc=0 checks=4 capped builds=['KAM.SpinOrbit.LunarFinalR2V2', 'KAMLunarBand.SpinOrbit.Top']
mixed light first/heavy second rc=3 checks=1 capped builds=[]
lock heavy rc=3 checks=2 capped builds=[]
light then newly visible heavy rc=3 checks=2 capped builds=['KAMLunarBand.SpinOrbit.Top']
same light remains stale rc=1 checks=2 capped builds=['KAMLunarBand.SpinOrbit.Top']
ALL 10 SCENARIOS PASS; actual check_all, stale, heavy, capped_build; only subprocess.run mocked
unparseable Lake failure STOP: prebuild_heavy: lake build --no-build failed without a failure list:
unexpected failure
capped build failure STOP: 1
```

### Landing order and prevention of heavy builds

Read the complete landing script. At the frozen revision:

```text
scripts/land-branch.sh:30  regenerate and validate roots/mapping
scripts/land-branch.sh:34  nice -n 5 lake build ... || fail ...
scripts/land-branch.sh:40  python3 -I scripts/prebuild_heavy.py --check-all ... || fail ...
scripts/land-branch.sh:41  source lint ... || fail ...
scripts/land-branch.sh:42  push ... || fail ...
```

Every actual branch landing that reaches this point runs the check after the core build, irrespective of changed files. Earlier errors abort; the existing “already in main” no-op returns without landing a new change. A driver exit 3 stops the shell landing through `fail`, whose shell exit is 1, before push.

The heavy predicate uses the declared `application_only` prefixes; the unchanged current mapping declares `KAM.SpinOrbit.Data`. It uses component-wise prefix matching, so application generated parts named `KAMLunarBand.SpinOrbit.Data.*` are correctly treated as light, while actual `KAM.SpinOrbit.Data.*` modules are rejected. All current band data and the lock data prefix lie under the protected prefix.

I also inspected the pinned installed Lake source: `Lake/Build/Common.lean:313–320` rejects an out-of-date build action in `--no-build` mode before running its build body; `Lake/Build/Module.lean` resolves dependencies before the module build action. Thus reported light frontier targets have their import artifacts ready; a stale heavy dependency prevents its dependent light module from becoming that build frontier. The mixed-frontier test confirms that even a light-first list cannot bypass the full heavy scan. The capped command retains the kernel-probe flock, `MemoryMax=10G`, `MemorySwapMax=0`, `LEAN_NUM_THREADS=1`, and `nice -n 5`.

This establishes the no-heavy-build property for the reviewed mapping and stable landing inputs. It is not a claim about future expensive modules placed outside the declared protected prefixes or concurrent external source/artifact mutation. Those are scope limits, not a surviving F1 counterexample. The deliberate `--lib` command remains able to build heavy modules; the landing invokes `--check-all` instead.

## F2 — CLOSED: all generated roots and parts have the required section

Independently loaded the real generator, called `classify` and `render` in memory, and enumerated all generated `.lean` roots/parts excluding lakefile.lean. Checked the actual files, not just the renderer template. Output:

```text
classification errors: []
generated roots and parts: 35 core: 27 applications: 8
missing or misplaced public section: []
largest generated file: (843, 'KAMLunarBand/SpinOrbit/Data/Lower.lean')
Lean changes other than appending public section: []
```

Each file ends with exactly one `\npublic section\n`, after its module docstring. For every changed Lean file, compared its bytes as UTF-8 text with `git show ade92a4f:<path>` and verified the entire change is exactly that appended text. Existing copyright comments, module commands and public imports are preserved. The generator appends `SECTION` in both root and part render paths (`scripts/gen_root_imports.py:310,313`), so the fix persists on regeneration.

Fresh commands and output:

```text
python3 -I scripts/gen_root_imports.py --check
exit 0, no output

LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
exit 0
check_lean_modules: PASS (3525 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (169 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

No heartbeat/recursion-depth overrides, oversized Lean files, proof escapes, or new lint failures were accepted by this run.

## F3 — CLOSED: GUARDS.md agrees with D51

Reviewed the complete file and the exact documentation changes. The root-import row now describes core/application assignment, data exclusion, cross-library import checks, application roots, generated parts and quarantine globs. The replay row now states core coverage by default and application coverage with `--lib <Lib>`. The usage includes `--lib`, and the new paragraph explains the prerequisite application `--no-build` and skipped-module count.

The landing paragraph now describes the actual sequence: core build, unconditional `--check-all`, light builds under the cap, exit 3 for stale data, then lint with core ABI checks. APPLICATIONS.md's tooling table was updated to match. Historical replay/mutation measurements remain explicitly dated evidence; they are not fresh receipts for this revision. No remaining D51 coverage contradiction from F3 was found.

## Regression scan and current freshness

Scanned the full fix diff: 35 Lean root/part files, three Python/shell tooling files, GUARDS.md, APPLICATIONS.md, the handoff, and the newly tracked historical audit-1 report. All Lean changes are the section append established above. Import lists, module ownership, Lake options and globs are unchanged.

```text
git diff --check ade92a4f 4edf977e
exit 0, no output

git diff --name-only ade92a4f 4edf977e -- KAM/Frozen manifest lakefile.lean scripts/build_roots.json scripts/abi_hashes.py scripts/lint_sources.sh scripts/kernel_replay.sh
exit 0, no output
```

The explicit `--lib` build path is unchanged; the obsolete `--since` landing selector is removed and its operational callers/docs now use `--check-all`. The new gate no longer depends on `members()` validation, but the landing still validates roots/mapping before the core build and application gate; fresh standalone generator checking also passes. No validation bypass follows in the reviewed landing path.

Fresh read-only application checks were run **after lint finished**, sequentially with `LEAN_NUM_THREADS=1`:

```text
lake build --no-build KAMLunarBand
exit 0: All targets up-to-date (5234 jobs).

lake build --no-build KAMLunarLock
exit 0: All targets up-to-date (3 jobs).
```

The band query replayed existing deprecation warnings. It built nothing. I did not invoke the real `--check-all` command, because that command is permitted to build stale light modules; its build paths were exercised only through mocked subprocesses.

For corroboration only, parsed the worker's historical `f2-core-build.log` and `f2-check-all.log`: the former has 27 built core root/part targets including KAM, and the latter has the seven band root/part targets plus KAMLunarLock. Both lists have zero built targets under `KAM.SpinOrbit.Data`. The handoff's “26 core root files” wording counts the 26 parts; the log also builds the core root. These are supplied logs, not builds run by this auditor.

## Closeout

F1, F2 and F3 are closed within this fix scope. No new blocking findings or suspected mathematical-source errata were identified. Only this report was created; no repair or implementation deviation was introduced. Fresh axiom printing, application ABI hashing, theorem/proof auditing and kernel replay were not performed, and this verdict makes no new claim about those receipts. Frozen files and manifest bytes are unchanged by the fix.
