# P6-3 independent audit 2 — hygiene addendum

**Overall package verdict: PASS WITH NOTES.** Audit 1's sole blocking finding H1 is
closed. All seven mathematical/signature PASS verdicts remain applicable; its
nonblocking blueprint note B1 remains open. No frozen anchor is proved or sealed
by this helper-package audit.

Audited on 2026-10-28 in `/root/code/KAM-inp-p63b`, at input HEAD
`aa7bc3032445629c67c936f11d85cf4b09c9a07e`, against audit 1's pinned revision
`fe7908fc7586c7230baa59b3afe928970eec4605`. This is a bounded verification
addendum, not a fresh source-correspondence audit. Read the repository rules,
plan, decisions, package brief, handoff and `P6-3-audit-1.md`. The user's request
authorizes this report and its commit, overriding the generic brief's no-commit
rule and destination. No production source or generated file was edited.

## Unchanged mathematics

- The original package commit touches exactly one file:
  `KAM/Planetary/Newtonian/Reconstruction.lean`. It is byte-identical to audit 1,
  SHA-256 `e29f80ba99b581db2aaf40df3b345e252d90a8ed87f9349a29842f079ca0facb`.
  All 50 recursively reachable project modules are also byte-identical, checked
  by following project imports and comparing each file with `git show` at the
  pinned revision. Thus neither statements, proofs nor project dependencies
  changed.
- `blueprint-P/parts/p6-newtonian-models.tex` and
  `docs/tracks/P/statement.md` have no diff against that revision. The design
  document has unrelated edits, but none changes the P6-3 signatures or scope.
- The retained PASS verdicts cover `KAM.Planetary.reconstruction`,
  `reconstruction_all_time`, `isNewtonSolutionOn_of_isMovingSolutionOn`,
  `reconstruction_fixed`, `reconstruction_fixed_all_time`,
  `orbit_transfer_moving` and `orbit_transfer_fixed`. The original definition,
  premise, normalization and valid-strengthening assessments remain applicable.

## Fresh verification

All Lean activity was sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`;
the build wrapper supplies the latter. No resource override or clean was used.

```text
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p63b KAM.Planetary.Newtonian.Reconstruction
[inp-gate] slot 2 acquired 05:15:06 for KAM.Planetary.Newtonian.Reconstruction
✔ [9091/9096] Built KAM.Planetary.Newtonian.Barycentric (23s)
✔ [9096/9096] Built KAM.Planetary.Newtonian.Reconstruction (23s)
Build completed successfully (9096 jobs).
exit 0
```

The build also replayed the same inherited `KAM.Kepler.Energy` warnings as
audit 1: unused `hm` at 106:35 and `hκ` at 106:48. Repetitive hints are omitted.

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Newtonian.Reconstruction
replaying KAM.Planetary.Newtonian.Reconstruction
exit 0
```

This single invocation covers the sole P6-3 module identified by audit 1.
A fresh scratch probe importing that module ran with
`env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P63AddendumAxioms.lean`
and exited 0. For each of the seven declarations listed above, `#print axioms`
reported exactly `[propext, Classical.choice, Quot.sound]`. The probe was removed.

Complete source-lint output:

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
check_lean_modules: PASS (413 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 0
```

No exception was needed, including the permitted stale-root notice. An additional
Python Unicode-character scan, without import/URL exemptions, found no line over
100 characters in the package's sole touched file (329 lines, maximum 99) or
`KAM/Kepler/Orbit.lean` (377 lines, maximum 100). The Orbit diff against audit 1
only wraps the four offending lines. **H1 is resolved.**

## Retained note and limits

**B1 remains nonblocking:** at the input revision,
`blueprint-P/parts/p6-newtonian-models.tex:165` still says “for $G=1$” before
using `actualMasses 1 m μ`. It should say “for $G=m_0=1$”, or retain `m0` in
the mass array. The Lean normalization helper already uses the correct joint
specialization. This addendum introduces no deviation and identifies no new
pinned-source erratum; literature sources were not re-audited.

Audit 1's broad-comparison provenance qualifications remain in force. This
addendum certifies the requested P6-3 hygiene/build/replay checks and preservation
of its mathematical verdicts, not other packages or downstream headline closure.
The only deliverable is this report; `git diff --check` passed before commit.
