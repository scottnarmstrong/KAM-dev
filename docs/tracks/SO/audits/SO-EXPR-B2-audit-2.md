# SO-EXPR-B2 independent audit 2 — Ball integration delta

Verdict: **PASS WITH NOTES** overall; **PASS** for the round-2 proof, signed declarations, completeness of the requested delta, and merge integrity. The sole note is the brief-permitted stale generated root (receipt below). No frozen anchor is sealed by this infrastructure package; provider/frozen-type and seal-body probes are inapplicable.

Audited HEAD: `1463ed15881dd2fc3e41d7c57ac35fbd6c427956`. Observed `inp`: `c97c960083d7c8900659d434e5c759ebff9e1a3e`; merge base: `9fd72f92acceab80b1cb91ba74de449c0ea8b697`. The user's exact report destination overrides the generic brief's MAIN-worktree destination.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the complete local B2 handoff and audit 1, the SO campaign plan, and the SO design/signature contracts. The handoff's final **ROUND 2 FOCUS** controls: audit only `git diff 3627099d -- KAM/Certificate/Expr/Ball.lean` and merge integrity. SO has no local `statement.md`; the signed SO declarations, rather than unrelated I/N/P anchors, govern this infrastructure slice.

Compared `git diff inp...HEAD`: five Lean files plus the two B2 audit/handoff documents. Ball contributes 11 insertions and 25 deletions; the four Diff files are the original B2 implementation. Every one of those four files is byte-identical to the audit-1 source at `c1f58948`. This report does not repeat the original mathematical B2 audit: its unchanged source is covered by audit 1, with fresh build and kernel checks here.

Merge `3627099d` has parents `7134973c` and `9fd72f92`. Its complete tree difference from its inp parent consists only of the four original B2 Lean files and the two B2 documents. Each of these six files is byte-identical to its B2 first-parent version. Consequently the merge imports inp's other content without incidental modifications, including Ball. After that merge, HEAD changes only Ball and the round-2 handoff. The protected-path comparison against inp is empty.

## Declaration review

All names below are in `KAM.Certificate`; locators refer to `KAM/Certificate/Expr/Ball.lean`.

| Node / locator | Declaration | Verdict | Reason |
|---|---|---|---|
| Integration / 409 | `slpMulO_prefix_self` | PASS | Exhausts both optional operands; multiplication either emits an appended operation or retains the input program. No premises. |
| Integration / 412 | `slpInvPre_emit_prefix` | PASS | Composes exactly three multiplication-prefix facts after the inverse emission, covering the added fourth-power slot. No soundness/nonvanishing premise. |
| Integration / 417 | `slpInvNode_emit_prefix` | PASS | Original statement unchanged; derives every power witness from `slpInvPre_spec hA`, then the tail prefix from `slpInvTail_sound`, and composes prefixes. |
| Signed Ball / 34 | `cexpHalvings` | PASS | Header and implementation match the current signature file, including its namespace; untouched by the fix. |
| Signed Ball / 49 | `certCExpReduced_cexpHalvings_isSome` | PASS | Signed header byte-identical; fresh copied-signature application elaborates. |
| Signed Ball / 197 | `Slp.balls` | PASS | Signed header byte-identical; fresh copied-signature definition elaborates. Implementation untouched by the fix. |
| Signed Ball / 336 | `Slp.val_mem_ball` | PASS | Signed header byte-identical; fresh copied-signature application elaborates. |
| Signed Ball / 497 | `HamExpr.nonvanishingOn_of_balls` | PASS | Signed header byte-identical; fresh copied-signature application elaborates. No caller-supplied nonvanishing premise. |

The handoff says “four signed Ball declarations”; the current signature source also explicitly contains the completeness theorem. I checked all five named entries above, rather than using that count to omit an entry. Source headers through the conclusion, excluding `:=`, are character-for-character identical both to the merge version and to `/root/code/KAM-inp/.drafts/design/SOSignatures.lean` (the halving subsection and §D). Fully qualified names remain under `namespace KAM.Certificate`. The original `slpInvNode_emit_prefix` header was also copied from `3627099d`, renamed, and elaborated against the current theorem with exactly `hS hf h0 hA`.

The proof does not assume the fourth-power witness externally: `slpInvPre_spec` computes it using the third multiplication. Its prefix and value facts are carried to the new tail; the final prefix begins at `s ++ [SlpOp.inv A.v]`, not merely at `s`. This is precisely what the unchanged division branch of `HamExpr.nonvanishingOn_of_inv_good` needs to locate the denominator-validation operation. Its use of an empty auxiliary soundness domain establishes program-prefix facts; actual divisor nonvanishing is recovered on the certified domain through `SlpInvGood`, not inferred from emptiness. No conclusion-shaped or extra premise was introduced.

## Definition classification and hygiene

The round-2 delta introduces no `def`, `abbrev`, `structure`, class, or instance. It adds two theorems and replaces one proof body. Thus no new carrier, junk value, fallback, norm, or constant dependence requires classification. The reused `slpInvPre` is the already-audited B2 program builder emitting inverse powers through four; it remains unchanged.

Both new handwritten leaf names occur exactly once as declarations across `KAM/**/*.lean` and `.lake/packages/mathlib/Mathlib/**/*.lean`, at Ball lines 409 and 412. Neither introduces a root declaration or `_root_` escape. The namespace is `KAM.Certificate` throughout.

| Changed Lean file relative to inp | Physical lines | Maximum characters |
|---|---:|---:|
| `Expr/Ball.lean` | 506 | 99 |
| `Expr/Diff.lean` | 445 | 100 |
| `Expr/DiffBuild.lean` | 343 | 100 |
| `Expr/DiffCalculus3.lean` | 236 | 99 |
| `Expr/DiffNode.lean` | 669 | 100 |

All five files have copyright, `module`, public imports, module documentation and a public section. Direct scans found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, or `set_option`. The Ball transitive KAM import closure has 46 modules, no provider, and no frozen theorem. Its 11 frozen definitions were read and individually checked against manifest state `SEALED`: `complexStrip`, `dotℂ`, `gramMatrix`, `hamiltonianVectorFieldℂ`, `invarianceError`, `IsPrimaryOnStrip`, `IsRealOnReals`, `normalFrame`, `omegaZero`, `torsion`, `torsionAverage`.

## Independent verification

All commands ran in `/root/code/KAM-inp-soexprc`, serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`. No resource overrides, clean, update, cache-fetch, source edits, generated-root edits, or state-changing git commands were used.

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soexprc KAM.Certificate.Expr.Ball KAM.Certificate.Tests.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Expr.Diff
```

Exit 0. Gate receipt: `[inp-gate] slot 2 acquired 15:15:15 for KAM.Certificate.Expr.Ball KAM.Certificate.Tests.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Expr.Diff`.

Final output: `Build completed successfully (2952 jobs).` Replayed existing warnings only: unused `Nat.succ_eq_add_one` simp argument in `Arith/PiHigh.lean:218:8`, and unused variable `hS` in `Expr/Basic.lean:85:5`. The Ball tests include successful division with denominator action ball `[2] ± [1]`, and fail-closed division with `[2] ± [2]`, exercising the updated inverse program in kernel computation.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOExprB2Round2.lean
```

Exit 0. The probe imports Ball and reconstructs the three signed theorem headers and the signed `Slp.balls` definition header, applying current exports; it also reconstructs the pre-fix inverse-prefix statement. Exact axiom output:

```text
'KAM.Certificate.slpMulO_prefix_self' depends on axioms: [propext]
'KAM.Certificate.slpInvPre_emit_prefix' depends on axioms: [propext]
'KAM.Certificate.slpInvNode_emit_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpReduced_cexpHalvings_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first scratch invocation failed solely because `open KAM CertArith` attempted to resolve the second namespace before opening the first. Removing the unnecessary second name produced the clean exit-0 invocation above; no package source was changed. The failed scratch invocation is not a passing receipt.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.Ball KAM.Certificate.Expr.Diff KAM.Certificate.Expr.DiffNode KAM.Certificate.Expr.DiffBuild KAM.Certificate.Expr.DiffCalculus3 KAM.Certificate.Tests.Ball KAM.Certificate.Tests.ComplexExp
```

Exit 0. Exact output:

```text
replaying KAM.Certificate.Tests.ComplexExp
replaying KAM.Certificate.Tests.Ball
replaying KAM.Certificate.Expr.DiffCalculus3
replaying KAM.Certificate.Expr.DiffBuild
replaying KAM.Certificate.Expr.DiffNode
replaying KAM.Certificate.Expr.Diff
replaying KAM.Certificate.Expr.Ball
```


```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the generated-root staleness expressly allowed by the brief. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1318 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated root remains untouched. Module hygiene, frozen-anchor protection, and all 144 ABI hashes pass independently of that permitted note.

```sh
git diff --check inp...HEAD
git diff --check
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Each exits 0 with no output. The merge-to-inp protected-path comparison is also empty.

## Source defects, deviations, and limits

No suspected source, blueprint, signed-statement, or frozen-definition defect was found in the round-2 slice. There is no new premise, numerical constant, changed carrier, or mathematical deviation. Replacing the old inverse-case proof is required because B2 added the fourth inverse power; the replacement discharges that witness internally. The complete delta contains exactly the two new helpers and this proof replacement. No additional Ball consumer repair is missing: both the public nonvanishing theorem and the division success/failure tests compile with the extended program.

This is integration readiness of the requested package delta, with audit 1 retained for the unchanged B2 mathematical implementation. It does not claim a sealed KAM anchor, complete checker soundness, a lunar confinement result, or measured large-certificate replay performance. No external source was needed: the relevant contracts and implementations are local, and this delta changes no source-derived mathematical statement.

Final workspace verification: the only untracked or modified repository path is this report. The auditor-owned `.lake/abi-scratch/SOExprB2Round2.lean` was removed. No production file or git state was changed.
