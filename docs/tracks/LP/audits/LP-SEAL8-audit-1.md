Audited HEAD: `80df0a0905e7dcfd9b6c5a70780f0f72c78fc5a9`.
Initial static-audit HEAD: `4e48d05dc4cac76bc22aa83710f6c746f10b1f8c`.
Approval object: `6c168945` (`inp-lp-freeze8r`), D64 on live `main`.
Existing-manifest baseline: `inp@2bbacd66dc609df3a8eae9f64ab2f8bb555d2748` (307 entries).

# LP-SEAL8 audit 1

**PASS WITH NOTES.** All required D64 seal-delta checks pass at the audited HEAD. Both exact provider applications
and raw Expr-equality checks pass; all four axiom sets are exactly the standard three; all four independent kernel
replays pass; both ABI runs reproduce the installed hashes; final lint exits 0. No blocking finding or required
source change. The notes retain the existing closure, generated-root and source-facing scope boundaries.

Independent fresh session, refute-first, no delegation. Read worktree AGENTS.md, PLAN, DECISIONS, the full brief
at `/root/code/KAM-inp-lp/docs/tracks/LP/freeze/AUDIT-SEAL8-BRIEF.md`, the D62 ten-check brief/report and RUNBOOK
§§2/6 and closing rulings. Applied `/root/.claude/skills/lean-statement-audit/SKILL.md` without subagents.
Live main's D53/D58/D59/D62/D64 govern. D64 supersedes the D62 brief's exclusion of draft 8 and authorizes
one-pass SEALED installation. Only this report is a durable auditor edit; no commit.

## Findings

| ID | Class | Finding / disposition |
|---|---|---|
| N1 | NOTE | Preserve the approved closure convention: 79 planar / 96 spatial recursively imported frozen definition files. Every listed file is a SEALED definition and unchanged from inp. This is distinct from replaying the entire LP implementation graph; this delta requires four new module replays. |
| N2 | NOTE | Generated provider-root imports are authorized by the existing root exception (D43 and lint_sources.sh). No other non-anchor provider importer was found. |
| N3 | NOTE — resolved | Draft-8 N3 is corrected in both implementation docstrings: `LP:MAIN L15 (502–506)` becomes `LP:MAIN T15 (502–506)`. This is the complete implementation diff. Draft-8 C1's “best” wording is also corrected in the approval object. |

## Static check ledger

| Check | Evidence |
|---|---|
| Authority / identity | Both installed files equal `git show 6c168945:<draft path>` byte for byte after only `<APPROVAL-DATE>` → `2026-11-01`, `<DECISION>` → `D64`, and replacement of the marked proof body. Proposal and manifest draft blobs also equal the approved git objects. Independent byte reconstruction agrees with `lp_identity_check.py --pin`: 2 files, ALL IDENTICAL, exit 0. |
| Manifest | Exactly two new IDs; all 307 old entries JSON-equal to pinned inp; top-level configuration unchanged. Every approved non-hash field retained except the authorized approval/ruling/state fills. All 175 closure-hash fields reproduce with Guard.digest; Guard.check_theorem_region reproduces four prefix/suffix hashes and validates both bodies. |
| Bodies / providers | Both bodies normalize to `by exact <registered provider> hn ν hν hνmax hνle A hA hAord δ hδ`. Each full provider type text equals its anchor, including the let-bound horizon and entire final conclusion. Bodies are exactly `lp3_planar_strongAMD_safety_source hn ν hν hνmax hνle A hA hAord δ hδ` and its spatial counterpart. No extra hypothesis, forbidden token, provider-to-provider import or direct frozen-theorem import. |
| Scope / rebase | Relative to pinned inp, exactly four new Lean files, two added imports in each of KAM/Root/{Frozen,Provider}.lean, and the two authorized docstring substitutions. No pre-existing frozen/provider file changes; no other implementation change; all remaining changed paths are LP documentation or manifest/records. New anchor lengths 149/155 lines; no resource override. |
| Quarantine / roots | Independent code-masked import scan: zero unauthorized provider importers. gen_root_imports.py --check exits 0. check_frozen_anchors.py: FROZEN-ANCHOR GUARD OK, exit 0. Both new entries SEALED. |
| Records | Exactly two new MANIFEST-CHANGES rows cite D64; IDs, paths, exports, providers and seal applications agree with the installed files and FREEZE.md's D64 section. Final build/check receipts are present in commit B and agree with the handoff. |
| Carry-forward | The real imports preserve the D62 source carriers, source barycentric wrappers, sharp threshold, normalized orientation-free AMD, closed symmetric time interval, existence/overlap uniqueness, Newtonian reconstruction, canonical and actual-velocity annuli, element errors and half gaps. No claim of standalone L16 on arbitrary safe compact sets or geometric tangency is added. |

The complete statement delta was independently reconstructed from the actual D62 LP1/LP2 frozen files:
remove γ/τ and hγ/hτ, delete exactly one complete IsDiophantine premise, replace exactly one time power and
three sqrt drift factors, and rename the export. The resulting full type equals each installed declaration
modulo whitespace. All other clauses are unchanged. The exponents use n planets, not the physical phase dimension:
`a_n = 2/(6n²−3n+14)`, `b_n = 3/(6n²−3n+14)`. No new meaning-carrying definition is introduced.
The three source hashes in each entry reproduce from MAIN, AMENDMENTS and LP3-PLAN.

## Expanded binder ledger

Rows apply separately to both installed anchors. Source is MAIN §1 (6)–(9), T15/T19 and L16 as amended;
LP3-PLAN §1–§2 supplies the approved removal of arithmetic premises and the alternate drift supplier.
The chamber and canonical-carrier predicates are expanded below. Universal finite index variables are typing
indices of their displayed bounded formulas. No implicit instance premises are added.

| Expanded input | Bin | Source / ruling |
|---|---|---|
| n : ℕ | TYPING | MAIN §1 |
| hn : 2 ≤ n | SOURCE | MAIN §1; LP3-PLAN §1.1 |
| ν : Fin n → ℝ | TYPING | MAIN §1 mass vector |
| hν : ∀ i, 0 < ν i | SOURCE | MAIN §1 |
| hνmax : ∃ i, ν i = 1 | RULED | D59 OD-3 |
| hνle : ∀ i, ν i ≤ 1 | RULED | D59 OD-3 |
| A : Set (Fin n → ℝ) | TYPING | MAIN §1 axes |
| hA : IsCompact A | SOURCE | MAIN §1; empty permitted |
| hAord: all axes positive on A | SOURCE | MAIN §1 |
| hAord: all axes strictly ordered on A | SOURCE | MAIN §1 |
| δ : ℝ | TYPING | MAIN §1 |
| hδ : 0 < δ | SOURCE | MAIN §1 |
| μ : ℝ | TYPING | MAIN §1 |
| 0 < μ (hμ spatially) | SOURCE | MAIN (6); L1 |
| μ ≤ μ₀ | SOURCE | MAIN (6)–(7) |
| z₀ : Phase (n*2) / Phase (n*3) | TYPING | T15 / T19 |
| physical premise: all initial star distances positive | SOURCE | MAIN (6) |
| physical premise: all initial Kepler energies negative | SOURCE | MAIN (6) |
| initial axis vector ∈ A | SOURCE | MAIN (6) |
| hch: all initial actions positive | TYPING | D59 OD-11(b); frozen chamber |
| hch: action axes strictly ordered | TYPING | D59 OD-11(b); frozen chamber |
| h₀: all masses positive | TYPING | D59 OD-11(b); source canonical carrier |
| h₀: all star distances positive | TYPING | Same source canonical carrier |
| h₀: all Kepler energies negative | TYPING | Same source canonical carrier |
| initial source AMD ≤ orderedStrongThreshold − δ | SOURCE | MAIN (6); amendment N8; D59 OD-1 |

Per anchor: SOURCE 12, STANDING 0, TYPING 11, RULED 2, EXCESS 0. No conclusion-shaped input.
Spatial h₀ precedes initial-axis membership; named hμ is passed to both frozen barycentric maps.
All nine existential constants precede μ and z₀, hence depend only on (n,ν,A,δ) and their proof data.
Their positivity, the N10 inequalities, z, hs, hcht, ho and all orbit estimates are outputs.
The reused frozen exponent definitions are literal unchanged formulas: BODY_MATCH OK; PUBLIC_CARRIER OK;
WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A;
DEFINITION_VERDICT PASS within this unchanged-definition delta.

## Commands and outputs

All commands run from `/root/code/KAM-inp-lp-seal8aud`. Every Lean/Lake invocation, including subprocesses of
ABI/lint tools, must run serially inside this exact wrapper (abbreviated W below):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

MemAvailable must be at least 8 GiB before each Lean/Lake launch. No application build, clean, root regeneration,
heartbeat/depth override or source change is part of this audit.

```sh
git checkout --detach inp-lp-freeze8x
PYTHONDONTWRITEBYTECODE=1 python3 -I -B docs/tracks/LP/freeze/lp_identity_check.py \
  --root /root/code/KAM-inp-lp-seal8aud \
  --approved 6c168945:docs/tracks/LP/freeze/draft8 --date 2026-11-01 --decision D64 --pin
# 2 files checked; ALL IDENTICAL; exit 0
PYTHONDONTWRITEBYTECODE=1 python3 -I -B scripts/gen_root_imports.py --check
# no output; exit 0
PYTHONDONTWRITEBYTECODE=1 python3 -I -B scripts/check_frozen_anchors.py \
  --root /root/code/KAM-inp-lp-seal8aud --manifest manifest/frozen-anchors.json
# FROZEN-ANCHOR GUARD OK; exit 0
git diff --check
# no output; exit 0
```

Independent Python checks read the approved blobs with subprocess.check_output(['git','show',revision+':'+path]),
compare the filled bytes outside the marked body, compare old manifest dictionaries by ID and all top-level fields,
strip only hash/approval/state/ruling fields from new entries before comparison, and walk all recursive frozen
Defs imports. Guard.digest checks closure hashes; Guard.check_theorem_region checks the two regions/bodies.
A full-tree Guard.code_mask scan checks imports; the complete changed-path set is compared with the four new
files, the two roots, and the sole authorized implementation path. Independent statement transformation is
specified above. Outputs:

```text
307 OLD ENTRIES JSON-EQUAL; TOP-LEVEL CONFIG UNCHANGED; EXACTLY 2 NEW ENTRIES
GUARD REGION ERRORS []
NON-HASH FIELDS APPROVED; CLOSURE EXACT 79 SEALED DEFINITIONS
NON-HASH FIELDS APPROVED; CLOSURE EXACT 96 SEALED DEFINITIONS
PROVIDER FULL TYPE TEXT EQUAL (2/2); ONE-LINE BODY (2/2)
SOURCE PINS MATCH (2/2)
SCOPE EXACT: 4 NEW LEAN FILES; TWO DOCSTRING SUBSTITUTIONS; TWO GENERATED ROOTS
NO D62 CHANGES; NO QUARANTINE VIOLATIONS
FULL STATEMENT DELTA EXACT (2/2); NO EXTRA PREMISES; ALL OTHER CLAUSES UNCHANGED
TWO D64 ROWS MATCH INSTALLED EXPORTS AND PROVIDERS
```

Approved raw SHA-256 values (independent git-object reconstruction and identity script agree):

| Object | SHA-256 |
|---|---|
| Planar draft | 77c6bb5ee337d2c6b96bed50a06e5ca835acb33d3b9ee0813498df8b5be6cff8 |
| Spatial draft | ba6087a8953f445bb8dcea8f8a7ea074caf1d95442c80e27121f464efeea1374 |
| Manifest-entry draft | 9b8e3ffc6c5404c81bcd1cc5623f609c5ddd2976521b142a8d48aae9c4805669 |
| Approved proposal | ea8fe9918ea897f727a25dd4a8ab315c88a27dc691d1b6bef05bd919b699e6ce |
| Planar provider | 956c7e7648eb1c74468344d90038811202ef1738a5ac33f054ad93c1eed9304e |
| Spatial provider | 34e337b7af0e90f8e6472acdf2093e68b0add2f2e476e7552c2cc58fe60b0904 |

## Final Lean checks and handoff

The orchestrator confirmed the completed build was synced before any Lean call. Updated with
`git checkout --detach inp-lp-freeze8x` to the audited HEAD. Commit B changes seven files: only two ABI fields
in the manifest plus FREEZE.md, the handoff and four receipt/list files. No KAM bytes change. Rechecked the full
manifest against pinned inp: 307 old entries unchanged. Repeated identity and generated-root checks: exit 0.
The handoff's targeted build receipt is `Build completed successfully (11094 jobs)`, rc 0. The auditor authored
no production Lean module and compiled only the transient probe; no whole-branch/application build was run.

Fresh independently generated `.lake/abi-scratch/Seal8AudProbe.lean` imported the two actual installed anchors.
For each registered X/Pv pair it used:

```lean
example : type_of% @X := @Pv
run_cmd do
  let env ← getEnv
  let some a := env.find? ``X | throwError "missing anchor"
  let some b := env.find? ``Pv | throwError "missing provider"
  unless a.type.eqv b.type do throwError "EXPR_MISMATCH"
  unless a.type == b.type do throwError "RAW_EXPR_MISMATCH"
  logInfo "EXPR_EQV_AND_RAW_EQUAL"
#print axioms X
#print axioms Pv
```

X/Pv above stand for the full exports, not substitute declarations. A second read-only loop starts from each
actual anchor type and follows project constants through their types and definition values (theorems contribute
only types). Every reachable project definition's real defining module must occur in that entry's closure.
It uses env.getModuleIdxFor? and Expr.getUsedConstantsAsSet; no declaration or environment mutation. Output:

```text
EXPR_EQV_AND_RAW_EQUAL KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith
EXPR_EQV_AND_RAW_EQUAL KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith
SEMANTIC_CLOSURE_OK planar_strongAMD_exponentialSafety_noArith: 57 project definitions
SEMANTIC_CLOSURE_OK spatial_strongAMD_exponentialSafety_noArith: 64 project definitions
```

All four `#print axioms` outputs are exactly `[propext, Classical.choice, Quot.sound]`.
Command: `W lake env lean .lake/abi-scratch/Seal8AudProbe.lean`; exit 0, no warnings/errors.

Two independent serial calls of
`W python3 -B -I scripts/abi_hashes.py /root/code/KAM-inp-lp-seal8aud .lake/abi-scratch/Seal8AudManifest.json`
reproduced the two final hashes (the transient manifest contains exactly the two installed D64 entries):

```text
ABI_RUN 1 EXIT 0
ABI_RUN 2 EXIT 0
TWO_ABI_RUNS_IDENTICAL; 2/2 MATCH INSTALLED MANIFEST
planar:  b29ff03f40dc5f47b2ba0fae11d168ed7e2b83919b143d9d51cba0f1795d16f4
spatial: 387059c68796b425889eee542afbb9b3989ebf833cec9afaae08be7faa931966
```

Independent serial kernel replay used `W lake env leanchecker <Module>` for each row, always from the audit
worktree and after the 8 GiB gate. No diagnostics; all completed:

| Module | Exit | Seconds |
|---|---|---|
| KAM.Frozen.Planetary.StrongAMD.Theorems.PlanarStrongAMDExponentialSafetyNoArith | 0 | 15.1 |
| KAM.Frozen.Planetary.Spatial.Theorems.SpatialStrongAMDExponentialSafetyNoArith | 0 | 14.9 |
| KAM.Provider.Planetary.StrongAMD.PlanarStrongAMDExponentialSafetyNoArith | 0 | 15.0 |
| KAM.Provider.Planetary.Spatial.SpatialStrongAMDExponentialSafetyNoArith | 0 | 14.6 |

`KERNEL_REPLAY_TOTAL 4/4 OK`. The author's separate five-module receipt also includes the docstring-edited
Source module; it is reported as author evidence, not an independent fifth replay.

Final lint ran only through the prescribed wrapper:

```sh
PYTHONDONTWRITEBYTECODE=1 /root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-seal8aud
```

That script invokes the exact D53 systemd wrapper above around scripts/lint_sources.sh, including its internal
ABI Lean subprocess. No other Lean/Lake process was running in this audit. Complete substantive output:

```text
check_lean_modules: PASS (4235 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (307 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
exit 0
```

BLOCKING: 0. CHANGE-RECOMMENDED: 0. No new suspected pinned-source erratum, mathematical deviation, excess
premise, frozen-byte mismatch, kernel failure or default-heartbeat design signal. Existing source scope remains
as recorded above; this is a two-anchor seal delta, not a re-audit of the Nekhoroshev supplier or all LP proofs.
The new D64 row script and post-build ABI fill are disclosed producer procedural adjustments, consistent with
D64 and the runbook. There was no auditor execution deviation.

Final acceptance: the two installed D64 anchors, their two providers, manifest entries and installation records
at `80df0a0905e7dcfd9b6c5a70780f0f72c78fc5a9`. The branch tip still equals that HEAD. Both transient auditor
scratch files were deleted. Final git diff --check exits 0; git status --short lists only this untracked report.
No commit was made and no other source/report file was edited.



