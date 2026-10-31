# Certificate applications: opt-in builds (decision D51)

A **certificate application** is a numerical certificate of a physical system checked by the Lean kernel: the
Moon's spin–orbit band (SO-2), the Moon's synchronous lock (SO-3), LG00, and later ones. Their data modules carry
`decide +kernel` checks of several GB each and take CPU-hours in total, so they are not part of the default build.

- A plain `lake build` builds the **core** library `KAM`: the import closure of the generated root `KAM.lean`,
  which imports every core module, plus the quarantined `DRAFT_SORRY` anchors and their providers. So it still
  covers every core theorem, and never compiles certificate data.
- Each application is built only on purpose, with `lake build <Lib>`, through the serial capped driver
  `scripts/prebuild_heavy.py --lib <Lib>` (one heavy module at a time, 10 GB cap, kernel-probe lock).

## New applications: a separate Lake package (preferred)

A new application should start as its own Lake package that requires the core:

```
applications/<name>/
  lakefile.lean        -- package «kam-<name>»; require kam from "../.."; one default lean_lib
  lean-toolchain       -- the core's toolchain, byte for byte
  <Name>.lean          -- the application's root
  <Name>/...           -- its data and assembly modules, named <Name>.*, never KAM.*
```

- Its modules live in their own namespace and file tree, so the core's root, lint and kernel replay never see them,
  and nothing in the core can import them by accident.
- Where its frozen headline is anchored (the core manifest, or a manifest of the package) is not settled: it needs
  an owner ruling for the first such package.
- Build it from its directory (`cd applications/<name> && lake build`) through the capped driver; the core's builds
  are reused through the path dependency.
- The package must pass the core's rules: modules, the 1500-line cap, no heartbeat overrides, no proof escapes, and
  `scripts/lint_sources.sh` (which scans every `.lean` file outside `.lake` and `.drafts`).

## Existing applications: opt-in libraries inside the core package

The band and the lock were written under `KAM.SpinOrbit.Data.*` before D51. Renaming them would recompile every
data module, so they stay where they are and become **opt-in libraries** of the core package instead:

- `scripts/build_roots.json` assigns each module to exactly one library: an application owns the modules that
  equal or extend one of its prefixes; everything else is core. `KAMLunarBand` owns the N = 65 band data under
  `KAM/SpinOrbit/Data` (`Upper`, `Lower`, `Cseg*`, `Format`), `KAM.SpinOrbit.LunarFinalR2V2`, and the sealed frozen
  theorems `lunar_barriers` and `lunar_spin_confinement` with their providers (their proofs import the data;
  every frozen definition, and `lunarPLo_lt_lunarPHi`, stays in core). `KAMLunarLock` owns
  `KAM.SpinOrbit.Data.LockN65.*` (empty until the lock data land).
- `lakefile.lean` declares each application as a non-default `lean_lib «<Lib>»` with `roots := #[`<Lib>]`,
  `globs := libGlobs `<Lib>` and the core's `leanOptions`. The default library `KAM` has `roots := #[`KAM]` and no
  submodule glob. Every `KAM.*` module stays local to the library `KAM` (Lake's prefix rule), so it is built with
  the same options and the same trace whichever root reaches it: switching to opt-in recompiled nothing (verified
  with `lake build --no-build` before and after, BUILD-OPTIN handoff).
- `scripts/gen_root_imports.py` writes `KAM.lean` with its parts `KAM/Root/*.lean`, and each `<Lib>.lean` with its
  parts `<Lib>/**.lean` (at most 1000 imports per part), plus the generated block of `lakefile.lean` that lists
  the quarantined `DRAFT_SORRY` anchors and providers of each library (built as extra `.one` globs, since no
  module, root included, may import them).
- `scripts/gen_root_imports.py --check` (part of `scripts/lint_sources.sh`) fails when a module is claimed by two
  applications; when a module under an `application_only` prefix (`KAM.SpinOrbit.Data`) is claimed by none, so new
  certificate data can never fall into the core silently; when a core module imports an application module; when an
  application imports another application it does not `require`; when the lakefile's libraries disagree with the
  mapping; or when any generated file is stale.

### Adding an opt-in library (only when existing builds must be kept)

1. Add an entry to `scripts/build_roots.json`: `lib` (`KAM<Name>`), `title`, `track`, `requires`, `prefixes`.
2. Copy the commented template at the end of `lakefile.lean` into a `lean_lib «KAM<Name>»` declaration.
3. Run `python3 -I scripts/gen_root_imports.py`, then `--check`.
4. Before building anything heavy: `lake build --no-build <every module of the library>`
   (`python3 -I scripts/gen_root_imports.py --modules KAM<Name>`) must report the existing modules up to date.
5. Build it with `python3 -I scripts/prebuild_heavy.py --lib KAM<Name>`.

## Checks and tools

| Tool | Default (core only) | Application |
|---|---|---|
| `lake build` | the core library | `lake build <Lib>` via `prebuild_heavy.py --lib <Lib>` |
| `scripts/lint_sources.sh` | everything file-based, every library | (same; never builds) |
| `scripts/check_frozen_anchors.py` | every frozen file and the manifest (file-based) | (same) |
| `scripts/abi_hashes.py --check` | core anchors; application anchors listed as "checked by file hash only" | `--lib <Lib>` (or `all`); refuses unless `lake build --no-build <Lib>` passes |
| `scripts/kernel_replay.sh` | core modules; application modules left out (counted) | `--lib <Lib>`; refuses unless built |
| `scripts/prebuild_heavy.py` | — | `--lib <Lib>` builds serially; `--check-all` is the landing check of every application |
| `scripts/land-branch.sh` | builds the core | then checks every application, whatever changed (`lake build --no-build <Lib>`): builds stale light modules (roots, parts, assemblies) one at a time under the cap; stops (exit 3) if a certificate-data module would rebuild |
| `scripts/hq-status.py` | — | one row per library: modules, hand-written lines, generated-data lines |

The lint, the guard and the root check cover every library, because they read files, not builds. Only the checks
that need elaborated declarations (ABI hashes, axioms, kernel replay) run per library, on purpose.
