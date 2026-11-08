# B2-POLY independent package audit 2 — delta

**Verdict: PASS WITH NOTES. F1 is closed; no remaining blocking finding.**
The round-1 mathematical PASS WITH NOTES is retained, including N1/N2. This is a
delta audit, not a repeated mathematical review or a frozen-anchor seal audit.

## Scope and revision evidence

Worktree and report destination: `/root/code/KAM-inp-b2poly` (the user's explicit
destination overrides the generic brief's main-worktree destination).

- Round-1 audited HEAD: `168b370456fd6ad3a2518d48ba314755e800f961`.
- Round-2 audited HEAD: `1ebd75288107ee734e17681bcb0e86aabbbc49b5`.
- `inp`: `a8005126dc3cb9ad964977b2c575184ab9034b9c`.
- Merge base with `inp`: `9aff52db9dd863219109b3e6d738965f36b2bca0`.
- Initial working tree: clean. Only this report is authored by this audit.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the specified package audit brief,
the handoff including AUDIT FOCUS, and B2-POLY-audit-1.md. The user's round-2 delta
restriction controls the extent of this review; no full declaration/source review
or fresh package axiom/kernel-replay probes were performed.

`git diff inp...HEAD --stat` lists the five Poly Lean modules, the handoff and
the round-1 report (7 files, 1468 insertions). The full package remains the
round-1 package with the following exact two-path delta:

```text
$ git diff --name-status 168b37045 HEAD
M KAM/EffectiveStability/Poly.lean
A docs/tracks/B/audits/B2-POLY-audit-1.md
$ git diff --numstat 168b37045 HEAD
3   3   KAM/EffectiveStability/Poly.lean
239 0   docs/tracks/B/audits/B2-POLY-audit-1.md
```

Inspection of `git diff 168b37045 HEAD` verifies that the only source change is
rewrapping the three docstring lines at Poly.lean:16–18. Python assertions
comparing `git show 168b37045:<path>` with current bytes additionally establish:

```text
DELTA PATH ALLOWLIST: PASS
FACADE: identical outside module docstring; docstring differs only in whitespace: PASS
KAM/EffectiveStability/Poly/Basic.lean: byte-identical to round 1
KAM/EffectiveStability/Poly/Bound.lean: byte-identical to round 1
KAM/EffectiveStability/Poly/Bracket.lean: byte-identical to round 1
KAM/EffectiveStability/Poly/Deriv.lean: byte-identical to round 1
```

`git diff --check 168b37045 HEAD` exits 0 with no output.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
No imports, declarations, definitions, theorem statements, proof bodies, frozen
files, manifest data or generated roots changed in this delta.

## Finding disposition

| Node / declaration | Verdict | Reason |
|---|---|---|
| F1, Poly.lean facade docstring | PASS, closed | Only whitespace rewrap; facade maximum width is now 88 characters. |
| Basic, Deriv, Bracket, Bound public declarations | PASS WITH NOTES, carried forward | Byte-identical to the round-1 reviewed files; retain its 118-row classification and N1/N2. |
| Round-1 report addition | PASS | Records the audited baseline and its sole blocking finding; no Lean declarations. |

No new definitions require classification. Retain the round-1 classification of
33 definitions/abbreviations/structures and 85 public theorems. In particular,
N1's structural CartFits guard remains typing data; its executable decision
procedure is not supplied by this package. N2's stronger interfaces and the
soundness-only scope of cartEqCheck remain unchanged.

## Fresh mechanical checks

A recursive, exception-free Unicode-character scan used
`Path('KAM/EffectiveStability').rglob('*.lean')`, `read_text().splitlines()` and
`len(line) > 100`. It checked all 15 Lean files in that directory, including
existing modules, and found **0 violations**. Maximum width across the directory
is 100. Package file measurements:

| File | Lines | Maximum characters per line |
|---|---:|---:|
| Poly.lean | 21 | 88 |
| Poly/Basic.lean | 421 | 100 |
| Poly/Deriv.lean | 236 | 99 |
| Poly/Bracket.lean | 276 | 100 |
| Poly/Bound.lean | 150 | 99 |

The targeted facade build imports all four package implementation modules.
Exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-b2poly KAM.EffectiveStability.Poly
```

Output, exit 0:

```text
[inp-gate] slot 1 acquired 01:04:52 for KAM.EffectiveStability.Poly
Build completed successfully (2889 jobs).
```

The driver invokes `nice -n 5 lake build` through its compile gate. This audit
started one targeted build and waited for completion before invoking lint.
Every Lean/Lake invocation initiated here, including lint's ABI subprocess,
inherits `LEAN_NUM_THREADS=1` and the 4 GiB/no-swap scope.

Lint command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
```

LINT_RESULT_PENDING

## Retained limits, axioms and errata

No new theorem or changed proof requires a new axiom probe. The handoff records
`#print axioms` for the main package results as only `propext`, `Classical.choice`
and `Quot.sound`; this is prior evidence, not a fresh round-2 axiom measurement.
No fresh `leanchecker` run was requested for this docstring-only delta; no new
kernel-replay exit code is claimed. Frozen/provider signature probes are
inapplicable to this unfrozen Track B infrastructure package.

Retain round-1 N1's reported design-brief defect: its unguarded bracket/bound
claims fail on exponents outside Fin n; the existing CartFits repair is
unchanged. No new suspected source/blueprint defect, uncertainty or implementation
deviation was introduced or discovered by this delta. No generated file was
regenerated and no repository source was edited. Future one-step soundness,
analytic tails and continuation remain outside this package audit's conclusion.
