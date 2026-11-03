# B-GUARD audit 1: frozen-file ownership guard (refute-first)

- Target: branch `inp-bguard` at `dd654c805`, diff `git diff inp...HEAD` (base `e3ec5e94e`).
- Scope: tooling only. `scripts/check_frozen_anchors.py` (`check_frozen_ownership`), `scripts/test_frozen_anchors.py` (+4 tests),
  `scripts/guard_mutation_suite.py` (mutation `a13`).
- Date: 2026-11-03. Python 3.12.3.

## Verdict: PASS WITH NOTES

The new rule closes seal audit HH-1 N1: a `.lean` file under a `Frozen` directory with no manifest anchor is now rejected,
and the rejection comes from this check alone. No false positives on the real tree. Notes N1 to N3 are scope limits the
change shares with every other `project_files()`-based check; none is exploitable in the current tree, and none blocks.

## Checks run (all in the foreground)

| check | result |
|---|---|
| `git diff --stat inp...HEAD` | 3 files, all under `scripts/` (+52 lines); `git diff inp...HEAD -- KAM manifest` empty |
| `python3 -I scripts/test_frozen_anchors.py` | `Ran 29 tests ... OK` |
| `python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json` | `FROZEN-ANCHOR GUARD OK` |
| independent recount (own script) | 319 anchors, 319 distinct `path`s, 319 `.lean` files with a `Frozen` directory component; sets equal, no duplicate; 314 SEALED + 5 DRAFT_SORRY; 243 definitions + 76 theorems; all paths under `KAM/` |
| `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 scripts/guard_mutation_suite.sh --only a13` | baseline gate passes; `a13 yes check_frozen_anchors`; after restore gate passes; `1 rejected, 0 ACCEPTED/CRASH/ERROR, 0 skipped; elapsed 555s` |
| counterfactual: guard copy with the new call replaced by `pass`, on the unit fixture plus an orphan `Fixture/Frozen/Orphan.lean` | `FROZEN-ANCHOR GUARD OK` (rc 0); the real guard rejects with `frozen file has no manifest owner` (rc 1) |

## (1) Bypass probes

Probes ran the guard as a subprocess on the test suite's `Fixture` in a `TemporaryDirectory` (outside the checkout).

| probe | result | assessment |
|---|---|---|
| symlinked `.lean` file inside `Fixture/Frozen/` | rejected (unowned) | in scope, caught |
| `Frozen` directory outside `KAM/` (`applications/Frozen/A.lean`) | rejected | in scope, caught (the scan is the whole root) |
| `Frozen` as file stem (`Fixture/Frozen.lean`) or substring (`FrozenThing/`) | accepted | correctly out of scope: `parts[:-1]` matches whole directory names only; `KAM/Root/Frozen.lean` must not need an owner |
| non-`.lean` files in `Frozen/` (`A.lean.txt`, `B.LEAN`) | accepted | out of scope and harmless: Lake builds only `.lean` modules. The real `docs/tracks/LP/freeze/draft{7,8}/KAM/Frozen/**.lean.txt` drafts are correctly ignored |
| manifest `path` spelled `./Fixture/Frozen/Value.lean` | rejected (file unowned) | fail-closed; exact posix-string matching, the same key the duplicate-path check uses |
| symlinked directory inside a frozen tree (`Fixture/Frozen/Link -> ../../Outside`), or a symlink named `Frozen` | accepted | **N1** |
| lowercase `frozen/` directory | accepted | **N2** |
| `.drafts` component under a frozen tree (`Fixture/Frozen/.drafts/A.lean`) | accepted | **N3** |

- **N1 (symlinked directories).** `Path.rglob` in Python 3.12 does not descend into symlinked directories, so a Lean file reached
  through a directory symlink under `KAM/Frozen` is invisible to this check, and equally to every other `project_files()` check
  (sorry scan, axiom scan, import graph). Pre-existing blind spot, not introduced here. The tree has no symlinks outside
  `.lake/.git/.drafts` (`find -type l` empty). Optional hardening: reject any symlink under the root outside `.lake/.git/.drafts`.
- **N2 (case).** Matching is exact-case `Frozen`, the same convention as `draft_allowlist` (marker `"Frozen"`) and
  `lint_sources.sh` (`KAM/Frozen`). On the Linux box `KAM/frozen` is a distinct, non-frozen namespace; on a case-insensitive
  filesystem it would alias, but the guard reads relative paths as stored. Acceptable; not worth a rule.
- **N3 (`.drafts` exclusion).** Inherited from `project_files()`. A `.drafts` path component is not a valid Lean module name
  component, so such a file cannot be imported as part of the frozen tree. Harmless.

## (2) False positives

None. All 319 frozen `.lean` files are owned exactly once (recount above), including the 5 DRAFT_SORRY anchors and the
application-facing anchors (their anchors also live under `KAM/Frozen`; no other `Frozen` directory holds a `.lean` file).
The scan also covers untracked working-tree files: a stray untracked file under `KAM/Frozen` in a worktree fails the gate.
That is fail-closed and intended.

## (3) Duplicate case

Consistent with `check_entry`: both key on the raw `path` string; `check_entry` reports `anchor[N].path: duplicate P` and the
new check additionally reports `P: frozen file has 2 manifest owners`. The test `test_frozen_file_with_two_owners_is_rejected`
asserts rc 1 and the new message (the old one is also emitted). The redundancy is documented in the docstring; harmless.
Non-dict anchors and non-string paths are skipped by the counter and already rejected by `check_entry`.

## (4) Tests

Black-box: the new tests reuse the existing `Fixture` (independent manifest in `TemporaryDirectory`) and run the guard as a
subprocess; no production code is imported. They cover unowned top-level, unowned nested, two owners, and a non-frozen file
needing no owner (negative control). No test covers a non-`.lean` file or a `Frozen` file stem; optional additions.

## (5) Nothing else changed

`git diff inp...HEAD -- KAM manifest` is empty; no frozen file, manifest entry, root, or generated file is touched.
Mutation `a13` writes only into the suite's throwaway copy (`/tmp/guard-mutation-*`), edits the generated root there to model
regenerated roots, and the restored copy passes.

## Errata / deviations

None found. No edits besides this report.
