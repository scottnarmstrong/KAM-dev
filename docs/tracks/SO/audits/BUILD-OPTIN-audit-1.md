# BUILD-OPTIN independent audit 1

**Verdict: FAIL.** Core coverage and reuse of the existing band builds pass. Landing detection fails for shared-core changes and Lake/options changes (F1). The generated application modules also omit the literal rule-3 `public section` (F2), and GUARDS.md retains claims inconsistent with D51 (F3). No repairs were made.

## Scope and frozen inputs

- Worktree: `/root/code/KAM-inp-buildoptin`, branch `inp-buildoptin`.
- Audited diff: `git diff 45a76023 ade92a4f`; HEAD verified as `ade92a4f4fb04210e86169a09ec3ac118b80bb08`.
- Authority: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md D51; both BUILD-OPTIN briefs under `/root/code/KAM-inp/.drafts/briefs/offload-main/`; BUILD-OPTIN-handoff.md and its points for the auditor.
- Evidence: current source, `.drafts/build-optin-logs/`, fresh lint and two fresh Lake `--no-build` checks.
- Snapshot fingerprint: SHA-256 `0f440839492dcf3a2d8980cdb6334122d8998921c0aa9faa567d646cd4aac251` of the sorted concatenation of `sha256 + "  " + path + "\n"` for the 29 existing files named by the audited diff. Deleted paths remain pinned by the two commits.
- Method: focused, refute-first audit; inventory and source inspection, then a separate refutation pass using dependency tracing and in-memory instrumentation. The manuscript-audit skill supplied the evidence/report structure. No subagents, network access, source mutations, commits, builds, kernel replays, or process termination were used. Only this report was created. Lean/Lake processes were serialized with `LEAN_NUM_THREADS=1`.

## Blocking findings

### F1 — HIGH: landing selection ignores application dependencies and build configuration

At the frozen HEAD, `scripts/prebuild_heavy.py:87–102` selects applications using:

```python
git diff --name-only BEFORE HEAD -- KAM
libs = sorted({roots.library_of(...) for changed_lean_path in out} - {core})
```

The actual source uses the equivalent comprehension at lines 91–92. Thus a changed core module is explicitly removed from consideration, and `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, and `scripts/build_roots.json` are outside the Git path filter. It computes no reverse import closure.

Concrete shared-core dependency, independently traced from imports:

```text
KAM.SpinOrbit.LunarFinalR2V2
 -> KAM.SpinOrbit.Data.Lower.Passes
 -> KAM.SpinOrbit.LunarAssemblyV2
 -> KAM.SpinOrbit.LunarAssemblySharpGen
 -> KAM.SpinOrbit.LunarAssemblySharp
 -> KAM.SpinOrbit.LunarAssembly
 -> KAM.SpinOrbit.Barrier
 -> KAM.SpinOrbit.Model
```

A change confined to `KAM/SpinOrbit/Model.lean` therefore selects no application, although that module is in the band's import closure. A change to `projectLeanOptions` in lakefile.lean also selects none.

**Executable refutation attempt:** loaded the actual Python file with `runpy.run_path(..., run_name='audit_readonly')`; called its actual `confirm_since` with the real configuration; mocked only `subprocess.run`, `stale`, and `capped_build`, with an intentionally stale band member. No files or builds were changed. Results:

| Changed paths returned by mocked Git | Application selection | Calls after Git | Return |
|---|---|---|---|
| `KAM/SpinOrbit/Data/Format.lean` | KAMLunarBand | stale check over 1,654 members | 3 |
| `KAM/SpinOrbit/Model.lean` | none | none | 0 |
| `lakefile.lean` | none | none | 0 |
| `scripts/build_roots.json` | none | none | 0 |

The real Git filter would return an empty list for the latter two; supplying those paths anyway still selected none. The application case confirms that the failure is selection, rather than failure to stop on a stale selected library.

**Attempted alternate-gate refutation:** `scripts/land-branch.sh:38–41` runs this selector, then default `lake build`, default lint, and push. Default build excludes the band; default ABI inspection excludes its two theorem anchors. Root classification checks source membership/import direction, not whether application proofs still elaborate against changed dependencies. Neither source lint nor the byte guard typechecks those omitted proofs. No later unconditional application freshness check exists. The explicit `--lib` driver does not help a landing that never selects the application.

**Consequence:** a core/options-only landing can be pushed while application proofs or traces are stale, including proofs that the previous default build would have checked. This is a gap in question 4(b) and 4(c), not an objection to D51's opt-in default build.

**Closeout requirement:** landing must detect affected applications through their dependency closures, with conservative invalidation for build configuration/toolchain/mapping changes, or conservatively check every application. An affected stale application must stop the landing or receive the authorized opt-in check. Regression evidence must include a shared-core-only change and an options-only change. No repair performed here.

### F2 — LOW, hard-rule compliance: generated application modules omit `public section`

AGENTS.md rule 3 literally requires “module docstring, `public section`.” All eight application files have copyright comments, `module`, module docstrings, and public imports where applicable, but none contains `public section`:

```text
KAMLunarBand.lean
KAMLunarLock.lean
KAMLunarBand/Frozen.lean
KAMLunarBand/Provider.lean
KAMLunarBand/SpinOrbit/Data/Lower.lean
KAMLunarBand/SpinOrbit/Data/Top.lean
KAMLunarBand/SpinOrbit/Data/Upper.lean
KAMLunarBand/SpinOrbit/Top.lean
```

**Refutation pass:** these are import-only modules, so this has no present declaration-visibility effect; the old generator already omitted the command in core roots. Nevertheless, neither D51 nor the supplied rules exempts new generated import-only modules from the explicit requirement. Fresh lint accepts them because its module check does not enforce that clause. This is a literal compliance issue, not a Lean soundness defect.

**Closeout requirement:** emit the required command through the generator, or obtain an explicit applicable rule exception. Do not hand-edit generated files. No repair performed.

### F3 — LOW, documentation acceptance: GUARDS.md still describes pre-D51 coverage

At this HEAD, `docs/campaign/GUARDS.md:14` says the core generated import list is “every module except `DRAFT_SORRY` anchors and their providers”; line 19 says kernel replay rechecks “every constant”; lines 24–27 advertise no `--lib` option. These descriptions now omit the application exclusion. Only the ABI row was amended in this diff.

**Refutation pass:** the page dates its historical measurements to October 29, but these rows are the current operational descriptions, and the same table contains the new D51 ABI behavior. APPLICATIONS.md correctly explains opt-in replay, but does not make the contradictory unqualified coverage statements true. Question 7 explicitly requires GUARDS.md to agree with D51.

**Closeout requirement:** qualify the core root and default replay coverage and document application selection. No repair performed.

## Answers to the seven audit questions

### 1. Core coverage — PASS

An independent read-only Python traversal enumerated `Path('KAM').rglob('*.lean')`, parsed module imports, and computed the closure from `KAM.lean`. It compared the complement with the actual output of `python3 -I scripts/gen_root_imports.py --modules KAMLunarBand`.

```text
all KAM/**/*.lean: 3505
core closure KAM modules: 1849
quarantine: KAM.Frozen.Wave.Theorems.Nlw2, KAM.Provider.Wave.Nlw2
band: 1654
missing minus band: []
band minus missing: []
core closure intersects band: []
```

Thus `3505 = 1849 + 2 + 1654`. The closure count includes generated core parts under KAM/Root. Lock currently has zero assigned KAM modules. lakefile.lean's generated `.one` globs contain exactly the two quarantined modules, preserving the old default build's coverage of those otherwise unimportable core modules. No difference remains.

### 2. No core → application import — PASS

The independently computed core closure has empty intersection with the band. The generator's `classify` checks every direct edge using comment/string-masked imports; rejecting the first core-to-application edge also prevents a transitive crossing. Lint additionally prohibits importing an application root/part from other modules.

Read `scripts/guard_mutation_suite.py:296–306` and the complete `guard-suite.log`. The mutations really introduce the claimed violations:

| Mutation | Actual mutation | Recorded rejecting layer |
|---|---|---|
| k22 | New `KAM/SpinOrbit/Data/MutK22.lean`, outside application prefixes | `gen_root_imports:build-roots` |
| k23 | Add `public import KAM.SpinOrbit.Data.Format` to a core module | `gen_root_imports:build-roots` |
| k24 | Add `import KAMLunarBand` to a core module | `lint:application-root` |

Log: `5 rejected, 0 ACCEPTED/CRASH/ERROR, 0 skipped; elapsed 663s`; `after restore: gate passes`. The five include k14/k15. k24 exercises lint, not the generator's direct module-ownership edge test. The mutation suite was inspected, not rerun, because the audit forbids source edits. Fresh `python3 -I scripts/gen_root_imports.py --check` returned 0.

### 3. Frozen anchors — PASS, with exact meaning of “file hash only”

Manifest inventory: 171 anchors; exactly `KAM.SpinOrbit.lunar_barriers` and `KAM.SpinOrbit.lunar_spin_confinement` belong to the band. KAMLunarBand/Frozen.lean imports their frozen modules. `KAM/Root/Frozen.lean:159` still imports `KAM.Frozen.SpinOrbit.Theorems.LunarWindow`, containing `lunarPLo_lt_lunarPHi`. Every frozen definition is reached from the core root. No core module needs the two moved theorem modules (empty closure intersection above).

`git diff --exit-code 45a76023 ade92a4f -- KAM/Frozen manifest` returned 0. Neither frozen bytes nor the manifest changed. The guard still iterates every manifest entry, regardless of application assignment. Definitions receive whole-file hashes; theorem prefix/suffix hashes cover all bytes outside the intentionally mutable proof region, whose short SEALED assembly is separately validated. This is not a new whole-file hash of theorem proofs.

Read-only in-memory calls to the actual `Guard.check_theorem_region` on both moved anchors gave:

```text
original: PASS
prefix comment edit: frozen prefix hash drift (all bytes before proof body changed)
proof-only export edit: SEALED body must be trivial assembly of exactly implementation.export
```

The confinement proof diagnostic also names its required binders `q₀ p₀ φ₀ hp`. No frozen file was modified. Arbitrary legal proof-region whitespace is intentionally not byte-frozen, as before.

The default **lint pipeline** catches statement/file drift because it runs the complete guard before ABI inspection. Standalone abi_hashes.py does not itself hash skipped application files: its “checked by file hash only” message relies on that preceding guard. It must not be interpreted as a standalone file-check receipt.

### 4. Landing soundness — FAIL

| Case | Result |
|---|---|
| (a) Application module changed | Selected; all member targets get `lake build --no-build`; stale list returns 3; landing aborts. If members are current, the root/parts are built under the cap. |
| (b) Shared core dependency changed | Not selected. F1: no application freshness check. |
| (c) Lakefile/options changed | Not selected. F1: no application freshness check. |

land-branch.sh converts any prebuild failure to its own exit 1 via `fail`; exit 3 is the driver's status. Its failure path resets the landing rather than proceeding to push. The present `--since` invocation is not itself `lake build --no-build <Lib>`: it checks the full member list and then builds the generated root. This is adequate for selected applications, but cannot cover an unselected one.

### 5. Lake semantics and build reuse — PASS

Inspected the installed pinned Lake source, `Lake/Config/LeanLibConfig.lean:135–137`:

```lean
self.roots.any (fun root => root.isPrefixOf mod) ||
  self.globs.any (fun glob => glob.matches mod)
```

`KAM` is a Lean name prefix of `KAM.SpinOrbit.Data.*`; `KAMLunarBand` is not. Thus existing data modules remain local to library KAM, sharing its options and traces. The application roots and parts are new modules.

Fresh checks, run sequentially with `LEAN_NUM_THREADS=1`:

```text
lake build --no-build $(python3 -I scripts/gen_root_imports.py --modules KAMLunarBand)
exit 0: All targets up-to-date (5226 jobs).
lake build --no-build KAMLunarBand
exit 0: All targets up-to-date (5234 jobs).
```

Existing deprecation warnings were replayed; neither command built anything. Historical log inspection independently confirmed:

| Log | Relevant output |
|---|---|
| baseline-final-nobuild.log | `All targets up-to-date (12559 jobs).` |
| band-members-nobuild.log | `All targets up-to-date (5226 jobs).` |
| core-nobuild.log | Failure list contains only `KAM.Root.SpinOrbit`, `KAM.Root.Frozen`, `KAM.Root.Provider` |
| core-build.log | Built those three parts and KAM; `Build completed successfully (10899 jobs).` |
| core-build2.log | Built only KAM; `Build completed successfully (10899 jobs).` |
| band-build.log | Built six application parts and its root; `Build completed successfully (5234 jobs).` |
| band-nobuild-final.log | `All targets up-to-date (5234 jobs).` |

The two core build logs contain **zero** occurrences matching `KAM.SpinOrbit.(Data|LunarFinalR2V2)`. Historical lock-nobuild.log predates its root build and lists KAMLunarLock as stale; lock-build.log records the later root build. Historical logs are supplied evidence, not builds reproduced during this audit.

### 6. Tool changes — core checks retained; landing exception F1

- **kernel_replay.sh:** default expected set removes exactly application KAM modules and explicitly reports the omitted count. Core closure replay and quarantine replay remain. `--lib` first requires successful application `--no-build`, then adds its member modules. Replay was not run.
- **abi_hashes.py:** default selects 169 core anchors, retaining the same elaborated hash comparison. Application names are explicitly listed as file-only; `--lib` checks application freshness before elaborated inspection. The current handoff reports the separate two-anchor ABI check and standard axioms; those application checks were not rerun in this audit.
- **lint_sources.sh:** file-based scans still cover applications and core. Generated application roots receive the existing root/provider-import exemptions; exact generated-file checking prevents arbitrary extra declarations in those files from passing as generated output. Root-import prohibitions were extended. Fresh lint exited 0 (output below). F2 is a literal requirement its existing module check does not test.
- **hq-update.sh:** stages application roots/parts with core roots and extends conflict handling for generated paths. It does not add an application validation gate. The relaxed generated-path conflict filter is broader than the mapping, but an unresolved nongenerated conflict still prevents committing; no current check-skipping counterexample found from this change.
- **hq-status.py:** adds per-library module/theorem counts and separates application hand-written lines from generated-data lines. Existing area counts remain. This is reporting, not a build or validation receipt.
- **lint-width-allow.txt:** independently loaded all eight old path/digest entries with `git show 45a76023:scripts/lint-width-allow.txt` and hashed every current line in the referenced CsegSupport file. Output: `removed width entries: 8 still matching: []`. Removing them weakens no current check; loader remains.

Fresh command:

```text
LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
exit 0
check_lean_modules: PASS (3525 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (169 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

### 7. Hygiene and documentation — FAIL on F2/F3; remaining checks pass

All new application roots/parts have the required copyright and `module` headers, public interface imports where present, and module docstrings. They are 25, 18, 18, 18, 841, 21, 835, and 17 lines respectively; none exceeds 1500. An independent scan of all KAM/**/*.lean likewise found no file over 1500 lines. Fresh lint found no heartbeat, recursion-depth, or synthesis-heartbeat overrides, forbidden proof escapes, or width violations. F2 records the missing `public section` precisely.

AGENTS.md rules 8/10, README static rule 7, APPLICATIONS.md, and D51 agree on core-only defaults, deliberate capped application builds, generated roots, and unchanged module paths. APPLICATIONS.md describes the current selector accurately but does not remedy F1. GUARDS.md's ABI row agrees; its root/replay descriptions do not (F3).

## Closeout and limits

Only this report was written. No Lean declaration or mathematical source was changed or re-audited. The handoff reports `#print axioms` for both band anchors as `[propext, Classical.choice, Quot.sound]`; this audit does not claim a fresh axiom receipt, kernel replay, application ABI run, or new elaboration/build result. No suspected mathematical-source erratum was found in this tooling scope. F1–F3 are package implementation/documentation findings, with no repair introduced by the auditor.

All seven requested questions have been answered. The positive coverage, guard, lint, and reuse evidence does not close the landing gap. Landing approval remains blocked on F1 and the explicit compliance/documentation items F2/F3.
