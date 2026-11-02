283bfbad5b072600729293a66d3ef1e2fce6e3ab

Verdict: **PASS** (DELTA ONLY).

Reviewed commit `283bfbad5` against its parent, previously audited HEAD
`3fabe89f2f819dd39e0c740bec8e24cb7b237df9`. This report checks only the requested F1/F2
repairs, commit scope, restored declaration equality to main, and remaining deleted-name
references outside `KAM/`. It does not repeat the full audit or adjudicate audit-1's F3/F4 notes.

| Check | Result | Evidence |
|---|---|---|
| F1: restore the used declaration | PASS | `KAM/Planetary/StrongAMD/PlanarDictionary.lean:59` restores `lpChart_isOpen_dom`. The application use at `applications/hd11964/HD11964/HoloG2.lean:120` now has its original declaration again. |
| Restored statement and proof equal main | PASS | The full declaration line from `git show main:KAM/Planetary/StrongAMD/PlanarDictionary.lean` equals HEAD byte for byte: `theorem lpChart_isOpen_dom (n : ℕ) : IsOpen (poincareProdDom n) := isOpen_poincareProdDom n`. Only a new explanatory docstring accompanies it. |
| F2: correct source locator | PASS | `KAM/Planetary/StrongAMD/PlanarSafety/Constants.lean:17` changes only `L15` to `T15 (502–506)` in the source comment. |
| Commit scope | PASS | `git show 283bfbad5` changes exactly the two repair files and `docs/tracks/LP/audits/LP-CLEANUP1-audit-1.md`. No other path changes. Full repair hunks contain only the restored declaration/docstring and locator correction. |
| Remaining deleted-name consumers outside KAM | PASS | Reconstructed the remaining 96 deleted declaration names from `git diff main...HEAD`; `lpChart_isOpen_dom` is no longer among them. Searching all tracked text outside `KAM/` finds no occurrence in `applications/`, `scripts/`, or any tracked Lean file outside KAM. All 257 matching lines are in `docs/`, including historical reports, proposals, archived statement snapshots and the errata record. These documentation mentions are not executable consumers. |

Checks performed, all read-only:

- `git status --short`: initially empty.
- `git rev-parse HEAD`: audited hash on the first line; `git rev-parse HEAD^`: previous audited hash above.
- `git show --stat --oneline 283bfbad5` and full hunks for both repaired Lean files: exactly the changes described above.
- Inline Python extracted the restored declaration from `git show main:<path>` and `git show HEAD:<path>`:
  `STATEMENT_AND_PROOF_BYTE_EQUAL True`.
- Inline Python extracted named declaration removals from `git diff --unified=0 main...HEAD -- '*.lean'`,
  subtracting declaration additions: `DELETED_NAMES 96`, `RESTORED_NOT_DELETED True`.
- The deleted names were searched with `git grep -n -I -w -E <name-alternation> HEAD -- . ':(exclude)KAM/**'`.
  Identifier matching includes names preceded by a dot, so qualification/dot notation, simp lists and
  attribute references are included. Output classification: `OUTSIDE_KAM_HIT_COUNTS {'docs': 257}`;
  `APPLICATION_SCRIPT_OR_LEAN_HITS []`; `OTHER_NON_DOC_HITS []`.
- `git diff --check HEAD^ HEAD`: exit 0, no output.

No build, lint, Lean invocation or axiom probe was run. The orchestrator's build and lint receipts are
not independently reproduced here. Only this report was written; no state-changing git command was used.
