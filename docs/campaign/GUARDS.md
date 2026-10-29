# Freeze guards: what they check, how to run them, latest results

Release requirements (skill `lean-orchestrator`, `references/landing-guards.md`): every landing runs the
source-level gate and a build; a release or seal claim additionally needs a whole-library kernel replay and a
passing guard mutation suite. This page records the layers, the two scripts added by package I-GUARDS and their
measured behaviour. Last measured 2026-10-29 on branch `inp-iguards` (main at `23a055ed`), on a shared 8-core,
30 GB machine under heavy load (load average 8-15, swap full), so the times below are pessimistic.

## The layers

| layer | script | checks |
|---|---|---|
| source lint | `scripts/lint_sources.sh` (also `lake lint`) | outside `KAM/Frozen`: `sorry`, `admit`, `axiom`, `unsafe`, `opaque`; `set_option maxHeartbeats / maxRecDepth / synthInstance.maxHeartbeats` anywhere on a line; `EuclideanSpace` in code (comments masked); lines over 100 characters; files over 1500 lines |
| root imports | `scripts/gen_root_imports.py --check` | `KAM.lean` equals the generated import list (every module except `DRAFT_SORRY` anchors and their providers) |
| errata | `scripts/render_errata.py --check` | `docs/ERRATA-AND-DEVIATIONS.md` matches `docs/errata/ledger.json` |
| module system | `scripts/check_lean_modules.py` | every `.lean` file is a module (`module` first token), no symlinked `.lean`, line limit 10 000, comparator configs |
| frozen anchors | `scripts/check_frozen_anchors.py` against `manifest/frozen-anchors.json` | manifest schema; whole-file hash of definition anchors; prefix and suffix hashes and marker order of theorem anchors; `DRAFT_SORRY` body is exactly `by sorry`; `SEALED` body is a short assembly of the provider export; one declaration per frozen file, not private, name matches export; implementation modules; definition closure hashes; the `DRAFT_SORRY` quarantine (no other module imports or names a `DRAFT_SORRY` anchor or its provider, directly or transitively); no `sorry`/`admit` anywhere except the authorized body; no `axiom` command |
| ABI hashes | `scripts/abi_hashes.py --check` (needs the build) | sha256 of `#print` (definitions) or `#check @` (theorems) under `pp.all`, against `abi_sha256` |
| kernel replay | `scripts/kernel_replay.sh` (new) | every constant is re-checked by the kernel, so a declaration added with `debug.skipKernelTC`, `addDecl` or a custom elaborator is caught |

`scripts/land-branch.sh` runs `gen_root_imports`, `lake build` and `lint_sources.sh` (which includes the anchor guard and
the ABI hashes); the kernel replay and the mutation suite are not yet part of it.

## `scripts/kernel_replay.sh`

```
scripts/kernel_replay.sh [--full | --fast] [--timeout MIN=90] [--mem-gb GB=40] [--batch N=4] [--log FILE]
```

Tool choice. `leanchecker` (ships with the toolchain) runs `Lean.Kernel.Environment.replay` over the olean contents:
it needs no export step and is the tool the guard reference prescribes. It uses the same C++ kernel as the build, so it
detects declarations that bypassed kernel checking, not a kernel bug. `leanchecker-paranoid` is the same binary
family, `lean4lean` needs `lake exe` from its own package, and `nanoda_bin` needs a `lean4export` dump plus a JSON
config; the genuinely independent kernels (`nanoda`, `lean4lean`) are not wired up (see Open points). `leanchecker`
has no `--help`; its flags are `--fresh` (replay the whole import closure, single module only), `--verbose` and
`--silent`. A module argument is a prefix (`KAM.Frozen.Defs` replays all its submodules); the root `KAM` itself has
no constants, so a plain `leanchecker KAM` would not check the library (`--fresh` does).

* `--full` (default): `leanchecker --fresh KAM` (the root's whole import closure: Mathlib and all KAM modules the
  root reaches) in one process, followed by non-fresh replay of the modules outside that closure (the `DRAFT_SORRY`
  anchor and its provider). The set outside the closure is computed from the sources.
* `--fast`: the frozen anchors, their implementation modules and every module under `KAM/Provider` (166 modules),
  non-fresh, in batches of 4 (imports are trusted; run `--full` for a release).
* Fails (exit 1) on: non-zero leanchecker exit, a timeout, any output other than `replaying ...` progress lines, or
  any expected module missing from the progress lines. One niced process at a time; `ulimit -v` cap; stops after
  90 minutes. Prints wall time, CPU and peak RSS of the largest process.
* Why batches: non-fresh replay costs about 1.5 GB of resident memory per module in a process (1 module 2.1 GB,
  2 modules 3.3 GB, 12 modules 18 GB, which got the process killed by the host's memory-pressure reaper), so the
  default batch is 4.

Measured:

| mode | result | wall | peak RSS | notes |
|---|---|---|---|---|
| `--fast` | OK, 166/166 modules, 42 batches | 1358 s (22.6 min) | 18.1 GB (largest batch) | CPU 1703 s |
| `--fresh KAM` alone | rc 0 | 2193 s (36.5 min) | 9.7 GB | CPU 2163 s; the whole closure |
| `--full` | OK (`--fresh KAM` + 2 modules outside the root closure: the `DRAFT_SORRY` anchor and its provider) | 1898 s (31.6 min) | 8.6 GB | CPU 1889 s; exit 0, all expected modules reported |

## `scripts/guard_mutation_suite.sh`

```
scripts/guard_mutation_suite.sh [--with-abi] [--only ID,ID] [--keep] [--scratch DIR] [--json FILE]
```

Copies the working tree (tracked and untracked files) to a throwaway directory under `$TMPDIR` or `/tmp` (never under
`.drafts/` or `.lake/`: the guards skip those directories, which makes every mutation invisible). The baseline copy
must pass the gate with the marker lines `FROZEN-ANCHOR GUARD OK` and `check_lean_modules: PASS`. Each mutation is
applied alone, `scripts/lint_sources.sh` of the copy is run, the mutation is undone. A mutation is **rejected**
when the gate exits non-zero (a guard that dies on an exception counts, marked "via crash": it fails closed). The
layer(s) that fired are read from the gate's output. After the last mutation the restored copy must pass again.
Exit 1 if any mutation is accepted. By default the Lean-dependent ABI step of `lint_sources.sh` is stubbed out in the
copy (the suite then needs no build); `--with-abi` keeps it (symlinks `.lake` of the real tree) and enables
mutation j2. The suite only reports; it never fixes a guard. Runtime: about 26-60 s per mutation (the gate scans
1337 files), 33 min for all 72 mutations under load.

### Latest result (72 mutations; 54 rejected, 18 accepted)

Run 2026-10-29 (the three mutations whose setup was corrected, j5/k16/k18, were rerun alone, as was j2 with `--with-abi`: rejected by `abi_hashes`, 120 s for the pair).

| id | mutation | guard layer(s) that fired | rejected |
|---|---|---|---|
| a1 | one byte of a frozen theorem statement (digit in the saturn box) | check_frozen_anchors | yes |
| a2 | one byte of a frozen definition body (whole-file hash) | check_frozen_anchors | yes |
| a3 | one byte of a frozen theorem's docstring | check_frozen_anchors | yes |
| a4 | trailing byte appended to a frozen theorem file (suffix hash) | check_frozen_anchors | yes |
| a5 | SEALED proof body replaced by `by sorry` | check_frozen_anchors | yes |
| a6 | SEALED proof body is a non-assembly tactic block | check_frozen_anchors | yes |
| a7 | DRAFT_SORRY body replaced by a real term | check_frozen_anchors | yes |
| a8 | second declaration added to a frozen theorem file | check_frozen_anchors | yes |
| a9 | frozen theorem made `private` | check_frozen_anchors | yes |
| a10 | frozen proof-region marker removed | check_frozen_anchors | yes |
| a11 | extra import added to the frozen prefix | check_frozen_anchors | yes |
| a12 | frozen file deleted from the tree (manifest still lists it) | gen_root_imports,check_frozen_anchors | yes |
| b1 | `sorry` in a non-frozen module | lint:sorry,check_frozen_anchors | yes |
| b2 | `sorry` in a provider module | lint:sorry,check_frozen_anchors | yes |
| b3 | `admit` in a non-frozen module | lint:admit,check_frozen_anchors | yes |
| b4 | `sorry` after a string containing `--` | lint:sorry,check_frozen_anchors | yes |
| b5 | `sorry` in an untracked new file under KAM/Frozen | gen_root_imports,check_frozen_anchors | yes |
| c1 | `axiom` in a non-frozen module | lint:axiom,check_frozen_anchors | yes |
| c2 | `private axiom` | lint:axiom,check_frozen_anchors | yes |
| c3 | `opaque` constant | lint:opaque | yes |
| c4 | `unsafe def` | lint:unsafe | yes |
| d1 | non-anchor module imports a sealed provider | - | NO (ACCEPTED) |
| d2 | non-anchor module `public import`s a DRAFT provider | check_frozen_anchors | yes |
| d3 | transitive: new module imports a provider, plain module imports the new one | gen_root_imports,check_frozen_anchors | yes |
| e1 | non-anchor module imports a DRAFT_SORRY anchor | check_frozen_anchors | yes |
| e2 | transitive import of a DRAFT_SORRY anchor through a new module | gen_root_imports,check_frozen_anchors | yes |
| e3 | DRAFT_SORRY export used by name without an import | check_frozen_anchors | yes |
| f1 | `native_decide` | - | NO (ACCEPTED) |
| f2 | `decide +native` | - | NO (ACCEPTED) |
| f3 | `Lean.ofReduceBool` use | - | NO (ACCEPTED) |
| g1 | `set_option maxHeartbeats` | lint:resource-limit | yes |
| g2 | `set_option maxHeartbeats ... in` before a theorem | lint:resource-limit | yes |
| g3 | `set_option maxRecDepth` | lint:resource-limit | yes |
| g4 | `set_option synthInstance.maxHeartbeats` | lint:resource-limit | yes |
| g5 | `set_option  maxHeartbeats` with extra spaces mid-line | lint:resource-limit | yes |
| g6 | `set_option maxHeartbeats` in a lakefile-style option array | lint:resource-limit,gen_root_imports | yes |
| h1 | Lean file of 1501+ lines | lint:file-size,gen_root_imports | yes |
| h2 | Lean line over 100 characters | lint:line-length | yes |
| i1 | non-module `.lean` file | gen_root_imports,check_lean_modules | yes |
| i2 | `module` keyword after a doc comment (not first token) | gen_root_imports,check_lean_modules | yes |
| i3 | symlinked `.lean` file | gen_root_imports,check_lean_modules | yes |
| i4 | existing module loses its `module` header | check_lean_modules | yes |
| j1 | manifest full_file_sha256 edited | check_frozen_anchors | yes |
| j2 | manifest abi_sha256 edited (needs Lean: --with-abi) | abi_hashes | yes |
| j3 | anchor removed from the manifest (its file stays) | check_frozen_anchors | yes |
| j4 | manifest state SEALED -> DRAFT_SORRY for a sealed theorem | gen_root_imports,check_frozen_anchors | yes |
| j5 | manifest is invalid JSON | lint:empty-manifest | yes (via crash) |
| j6 | manifest anchors emptied | gen_root_imports,lint:empty-manifest | yes |
| j7 | manifest seal limit raised | - | NO (ACCEPTED) |
| j8 | manifest author approval field dropped | check_frozen_anchors | yes |
| j9 | manifest definition_closure hash edited for a theorem's dependency | check_frozen_anchors | yes |
| k1 | `open ... in elab` (elaborator mid-line) | - | NO (ACCEPTED) |
| k2 | `macro` | - | NO (ACCEPTED) |
| k3 | `macro_rules` | - | NO (ACCEPTED) |
| k4 | `syntax` command | - | NO (ACCEPTED) |
| k5 | `elab_rules` | - | NO (ACCEPTED) |
| k6 | `run_cmd` | - | NO (ACCEPTED) |
| k7 | `run_elab`/`run_meta` | - | NO (ACCEPTED) |
| k8 | `addDecl` in a user-defined command body | - | NO (ACCEPTED) |
| k9 | `set_option debug.skipKernelTC` | - | NO (ACCEPTED) |
| k10 | `attribute [command_elab ...]` | - | NO (ACCEPTED) |
| k11 | `@[term_elab ...]` attribute | - | NO (ACCEPTED) |
| k12 | `by_elab` | - | NO (ACCEPTED) |
| k13 | `EuclideanSpace` in code | lint:EuclideanSpace | yes |
| k14 | new module not imported by KAM.lean (stale root) | gen_root_imports | yes |
| k15 | module imports the root `KAM` | check_frozen_anchors | yes |
| k16 | errata ledger edited without re-rendering | render_errata | yes |
| k17 | import cycle between two plain modules | gen_root_imports | yes |
| k18 | BOM / non-UTF-8 junk before `module` | - | yes (via crash) |
| k19 | `sorry` hidden in a docstring-adjacent nested comment close | lint:sorry,check_frozen_anchors | yes |
| k20 | `sorryAx` used explicitly | - | NO (ACCEPTED) |
| k21 | Challenge-style `comparator.json` with Challenge imported | check_lean_modules,check_frozen_anchors | yes |

### Guard gaps found (accepted mutations: real guard bugs, reported not fixed)

1. **No lint for `native_decide` / `decide +native` / `Lean.ofReduceBool`** (f1-f3). Nothing in the source guards
   names them; only a kernel replay with an axiom check would show `Lean.ofReduceBool`.
2. **No metaprogramming lint** (k1-k12): `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `run_cmd`, `run_elab`,
   `run_meta`, `by_elab`, `addDecl`, `set_option debug.*`, `@[command_elab]`/`@[term_elab]`/`attribute [...]` are all
   accepted anywhere on a line. landing-guards.md section 2 requires these on masked code; `lint_sources.sh` has no
   such rule. This leaves `debug.skipKernelTC` unguarded at source level; only the kernel replay covers it.
3. **`sorryAx` written explicitly is accepted** (k20): the `sorry` pattern is word-bounded.
4. **Sealed provider imported from a non-anchor module is accepted** (d1): AGENTS.md rule 9 forbids it, but the
   quarantine implementation only covers providers of `DRAFT_SORRY` anchors (d2 is rejected).
5. **Manifest `seal_limits` raised is accepted** (j7): the manifest is the trust root and any value is accepted;
   such a change is visible only in review.

Layer attribution (landing-guards.md section 6): every rejected mutation is caught by the layer meant for it, except
that k14 (a module missing from `KAM.lean`) and k17 (an import cycle) are caught only by `gen_root_imports`, and j5
(invalid manifest JSON) and k18 (non-UTF-8 bytes) only by a Python exception that makes the gate exit non-zero (fail
closed, but no designed message). New files in the mutations (b5, d3, e2, g6, h1, i1-i3) are additionally flagged by
`gen_root_imports` because they are not in `KAM.lean`, in addition to their own layer. The ABI layer cannot be exercised
without rebuilding a mutated frozen module; only its manifest-edit side (j2, `--with-abi`) is tested.

## Open points

* `nanoda_bin` and `lean4lean` are not wired up: both need either a `lean4export` dump of all of Mathlib plus KAM or a
  `lake exe` build of the checker; `leanchecker` is not an independent kernel. A nanoda run on the frozen anchors only
  would still need Mathlib's closure.
* The kernel replay and the mutation suite are not yet gates of `scripts/land-branch.sh`.
