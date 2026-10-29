# SO-BALL independent audit 1

Overall verdict: **FAIL — required test slice incomplete (F1)**. The five signed SO-BALL declarations and five signed range-reduction tests match; the implemented soundness results pass independent elaboration, axiom inspection and kernel replay. F1 is a test-deliverable gap, not a counterexample to those results.

Audited HEAD: `c0e606b10b24990f8056c40b5e2af8384e5ad85a`; comparison ref `inp`: `f8405551c09bb7baf63ad01547cc2ecb8d372bbc`. Audit date: 2026-10-29 UTC.

Scope: only `KAM/Certificate/Expr/Ball.lean`, `KAM/Certificate/Tests/Ball.lean`, and `KAM/Certificate/Tests/ComplexExp.lean`. Read AGENTS.md, PLAN, DECISIONS, the package audit brief, SO-BALL handoff/AUDIT FOCUS, Revision 4 SO-LEAN-DESIGN and SOSignatures.lean. The SO design/signatures supply the statement authority for this package; there are no SO frozen theorem anchors or providers to seal here. The generic frozen-provider type/seal-body tests are therefore inapplicable; fresh copies of the signed declarations were elaborated instead. Per the explicit user instruction, this report is in the package worktree, overriding the generic brief's output-directory instruction.

`git diff inp...HEAD` reports multiple merge bases and selects `6cad95806f4dbeafc1933f733daf875fdb3b097a`. Its eight-file, 2203-line diff includes the five inherited SO-EXPR files Diff, DiffBuild, DiffCalculus, DiffNode and Slp. A direct `git diff inp HEAD --` on those five files is empty. They are dependencies, not independently audited deliverables here. The three scoped files are the package additions. The initial untracked handoff was preserved.

## F1 — required soundness pairings are absent

Design `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md:518` requires: “Each success is paired with `certCExpReduced_sound` (radius contains `exp`).” Tests/ComplexExp.lean:23–37 supplies three successes (`cexpTest_zero_small`, `cexpTest_two_reduced`, `cexpTest_large_pin`) and two rejection controls, but no successful output is paired with a containment theorem or an application of `certCExpReduced_sound`.

The same design at lines 519–521 requires the three ball scenarios to return `some` “and its `exp`-slot ball contains the exact value.” Tests/Ball.lean:33 proves this for exp 2 (indeed all slots), but lines 42–50 supply only `.isSome = true` for exp of a cosine mode and cosine of a large action. There is no corresponding containment corollary for either. The module docstring at Tests/Ball.lean:16 claims “Each success is paired with `Slp.val_mem_ball`,” which overstates the implemented coverage.

Required repair: retain the signed tests and add soundness pairings for the three direct complex-exponential successes and the two remaining required ball scenarios. The existing general soundness theorems make these routine corollaries, but their availability does not itself complete the explicitly required paired tests. This audit does not edit implementation files.

## Contract and proof assessment

All ten signed declaration headers compare equal after whitespace normalization, including names, namespaces, implicit/explicit binders, premise order and conclusions. `cexpHalvings` also has the exact signed body. Fresh declarations copied from SOSignatures.lean and discharged by the production exports elaborate successfully. No signed result acquires a new hypothesis, instance or bundled proof obligation.

The fold invariant proves containment for arbitrary programs using the same zero defaults as `Slp.vals`. An out-of-range action denotes zero in both evaluators. Missing centre/radius entries follow certDomain's existing getD semantics; nonpositive radii can make the domain empty, but the theorem covers that case literally rather than replacing the domain. Extra key entries enlarge the character bound conservatively. Every exp operation calls `certCExpReduced` with its own computed count, and Option.bind propagates rejection. Compiled sin/cos share this exp path. Rational constants incorporate the necessary π enclosure; negative powers use reversed positive endpoints. The inverse bound uses max of component magnitudes as a lower bound for the complex norm and rejects equality r = m.

For denominator certification, `ballsAux_prefix_inv` preserves every actual inverse check. `Slp.invGood_of_balls` proves its internal predicate from successful balls and slot soundness. The expression induction retains nested divisors even through multiplication and powers. Empty-set compiler invocations establish structural prefixes only; the actual denominator value on D is identified after the inductive nonvanishing proof for that denominator. This is not circular and does not assume the target conclusion. No source mathematical defect was found.

Per-export verdict: `cexpHalvings`, completeness, `Slp.balls`, `Slp.val_mem_ball`, and `HamExpr.nonvanishingOn_of_balls`: **PASS**. Test slice: **FAIL** for F1. Package hygiene: **PASS WITH NOTES** for the explicitly permitted stale generated root.

## Declaration inventory and definition classification

All names below are in `KAM.Certificate`; locations refer to the three scoped source files. Auxiliary declarations support the signed nodes and do not purport to prove additional blueprint nodes. Each definition's classification describes its complete carrier semantics; no junk fallback is used to evade a proof obligation.

| Node / file:line | Declaration | Verdict | Meaning / reason |
|---|---|---|---|
| Expr/Ball.lean:34 | `cexpHalvings` (def) | PASS | Exact signed body; finite log2/ceiling count, no caller size premise. |
| Expr/Ball.lean:37 | `certCExpSmall_reduced` (theorem) | PASS | Exact rational scaling identity; valid for all rational radii. |
| Expr/Ball.lean:49 | `certCExpReduced_cexpHalvings_isSome` (theorem) | PASS | Exact signed type; nonnegative radius is precisely the signed completeness premise. |
| Expr/Ball.lean:70 | `ballPiLo` (def) | PASS | Integer-power lower enclosure, reversed endpoints for negative degrees. |
| Expr/Ball.lean:73 | `ballPiHi` (def) | PASS | Integer-power upper enclosure, reversed endpoints for negative degrees. |
| Expr/Ball.lean:75 | `ball_two_pi_zpow_mem` (theorem) | PASS | Both enclosure directions, including negative degrees. |
| Expr/Ball.lean:92 | `constBall` (def) | PASS | Product of exact complex rational coefficient and enclosed power of 2π. |
| Expr/Ball.lean:96 | `mem_constBall` (theorem) | PASS | Contains the actual complex constant; accounts for π enclosure. |
| Expr/Ball.lean:119 | `inv_ball_bound` (theorem) | PASS | Derives nonzero operand and inverse enclosure from strict separation. |
| Expr/Ball.lean:149 | `ballZero` (def) | PASS | Exact zero default, agrees with unwritten-slot semantics. |
| Expr/Ball.lean:152 | `ballOf` (def) | PASS | Lossless pair-to-ball wrapper. |
| Expr/Ball.lean:155 | `ballStep` (def) | PASS | All seven operations; exp uses computed reduction; inverse rejects insufficient separation. |
| Expr/Ball.lean:184 | `ballsAux` (def) | PASS | Sequential option fold; none propagates without replacement. |
| Expr/Ball.lean:197 | `Slp.balls` (def) | PASS | Exact signed header; evaluates the whole operation list. |
| Expr/Ball.lean:204 | `BallRel` (def) | PASS | Length equality plus containment at every index, including defaults. |
| Expr/Ball.lean:208 | `toC_zero_rat` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| Expr/Ball.lean:211 | `toC_ratCast` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| Expr/Ball.lean:214 | `ballZero_mem` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| Expr/Ball.lean:219 | `BallRel.ballRel_nil` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| Expr/Ball.lean:221 | `BallRel.ballRel_snoc` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| Expr/Ball.lean:239 | `ballStep_sound` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| Expr/Ball.lean:318 | `ballsAux_sound` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| Expr/Ball.lean:336 | `Slp.val_mem_ball` (theorem) | PASS | Exact signed type; domain-wide containment; hi is redundant but retained. |
| Expr/Ball.lean:347 | `ballsAux_prefix_inv` (theorem) | PASS | Strict separation for each inverse operand is preserved in the final prefix. |
| Expr/Ball.lean:380 | `SlpInvGood` (def) | PASS | Internal predicate proved from ball success, not assumed by the signed result. |
| Expr/Ball.lean:384 | `Slp.invGood_of_balls` (theorem) | PASS | Successful balls imply every inverse operand is nonzero on the domain. |
| Expr/Ball.lean:407 | `jetSmoothOn_empty` (theorem) | PASS | Empty-set smoothness used only for structural compiler-prefix facts. |
| Expr/Ball.lean:409 | `slpInvNode_emit_prefix` (theorem) | PASS | Proves the denominator-validation inverse node survives compilation. |
| Expr/Ball.lean:438 | `HamExpr.nonvanishingOn_of_inv_good` (theorem) | PASS | Structural induction; proves child nonvanishing before using compiler soundness on D. |
| Expr/Ball.lean:511 | `HamExpr.nonvanishingOn_of_balls` (theorem) | PASS | Exact signed type; all recursive denominators certified, no extra premise. |
| Tests/Ball.lean:24 | `testWeight` (def) | PASS | Concrete rational test fixture (rho = 1/4, w = 5). |
| Tests/Ball.lean:26 | `ballTest_weight` (theorem) | PASS | Kernel-decided valid weight. |
| Tests/Ball.lean:28 | `ballTest_exp_const` (theorem) | PASS | Kernel-decided success; paired with the following containment theorem. |
| Tests/Ball.lean:33 | `ballTest_exp_const_mem` (theorem) | PASS | Containment of every returned slot for the exp-constant case. |
| Tests/Ball.lean:42 | `ballTest_exp_cos_mode` (theorem) | PASS (test gap F1) | Kernel-decided success; required scenario-specific containment pairing missing (F1). |
| Tests/Ball.lean:47 | `ballTest_cos_large_action` (theorem) | PASS (test gap F1) | Kernel-decided success; required scenario-specific containment pairing missing (F1). |
| Tests/Ball.lean:52 | `ballTest_div_ok` (theorem) | PASS | Kernel-decided separated-denominator success. |
| Tests/Ball.lean:57 | `ballTest_div_fails_closed` (theorem) | PASS | Kernel-decided boundary rejection (r = m). |
| Tests/ComplexExp.lean:23 | `cexpTest_zero_small` (theorem) | PASS (test gap F1) | Exact signed type; kernel-decided success; soundness pairing missing (F1). |
| Tests/ComplexExp.lean:26 | `cexpTest_zero_large` (theorem) | PASS | Exact signed type; kernel-decided negative control. |
| Tests/ComplexExp.lean:29 | `cexpTest_two_rejected` (theorem) | PASS | Exact signed type; kernel-decided negative control. |
| Tests/ComplexExp.lean:32 | `cexpTest_two_reduced` (theorem) | PASS (test gap F1) | Exact signed type; kernel-decided success; soundness pairing missing (F1). |
| Tests/ComplexExp.lean:35 | `cexpTest_large_pin` (theorem) | PASS (test gap F1) | Exact signed type; kernel-decided success; soundness pairing missing (F1). |

There are 12 definitions and 31 public theorems, no new structures/abbreviations. All twelve definitions are classified in the table: arithmetic bounds, wrappers/default, evaluator/fold, relational invariant/internal predicate, or test data. `SlpInvGood` is an intermediate proved property, not a hidden source hypothesis.

## Independent checks

All Lean/Lake commands ran serially with `LEAN_NUM_THREADS=1`; direct Lean and replay commands used `nice -n 5`, and the compile gate itself invokes `nice -n 5 lake build`. No resource override, package mutation, root regeneration or state-changing git command was used.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soball KAM.Certificate.Expr.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Tests.Ball
[inp-gate] slot 1 acquired 14:45:17 for KAM.Certificate.Expr.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Tests.Ball
Build completed successfully (2951 jobs).
exit 0
```

Replayed dependency warnings: Arith/PiHigh.lean:218 unused simp argument `Nat.succ_eq_add_one`; Expr/Basic.lean:85 unused variable `hS`. No warning in the three audited files.

2. Signature/axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOBallAudit.lean
exit 0
```

The scratch probe reproduced all five SO-BALL declarations and all five range-reduction declarations from the signature file under fresh names with production-export bodies. It printed axioms for every theorem in the inventory (all 31). The exact axiom output was:

```text
'KAM.Certificate.certCExpSmall_reduced' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpReduced_cexpHalvings_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ball_two_pi_zpow_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.mem_constBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.inv_ball_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toC_zero_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toC_ratCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballZero_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.BallRel.ballRel_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.BallRel.ballRel_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.invGood_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetSmoothOn_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpInvNode_emit_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_inv_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_exp_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_exp_const_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_exp_cos_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_cos_large_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_div_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_div_fails_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_zero_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_zero_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_two_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_two_reduced' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_large_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or additional axiom appeared. The probe was deleted after validation.

3. Single kernel-replay invocation:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Tests.Ball
replaying KAM.Certificate.Tests.Ball
replaying KAM.Certificate.Tests.ComplexExp
replaying KAM.Certificate.Expr.Ball
exit 0
```

4. Lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1311 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1 (only the explicitly permitted generated-root discrepancy)
```

The generated root was left untouched as required.

5. Static checks: source scans found no forbidden token, `native_decide`, EuclideanSpace or option override in scope. All files have copyright/module/import/docstring/public-section headers. Ball.lean has 520 lines (maximum width 99); Tests/Ball.lean 62 (100); Tests/ComplexExp.lean 39 (97). All ten boolean/option test controls use `decide +kernel`; `ballTest_weight` also does. The single containment test uses the proved soundness theorem.

A declaration-name scan of KAM and Mathlib (excluding the audited files) found no duplicate public declaration short names from this package. All declarations remain inside `KAM.Certificate`; no harmful root shadow was found. The renamed `ballRel_nil`/`ballRel_snoc` avoid the earlier generic short names.

Transitive KAM import traversal found 47 modules, no provider imports and no frozen theorem imports. Its eleven frozen imports are definitions only, all manifest state SEALED: ComplexStrip, DotC, GramMatrix, HamiltonianVectorFieldC, InvarianceError, IsPrimaryOnStrip, IsRealOnReals, NormalFrame, OmegaZero, Torsion, TorsionAverage. Thus there is no DRAFT_SORRY dependency.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no diff; only the multiple-merge-base warning)
```

## Errata, deviations and limits

No pinned-source mathematical erratum or frozen-statement defect was found; this package implements the SO design rather than a new pinned-source theorem. F1 is an implementation/test coverage deviation, and the Tests/Ball docstring should be corrected or made true by the missing pairings. The prover's test-file split is harmless and preserves the lighter Tests/ComplexExp import boundary. The signed Slp.balls docstring says “Constants exact”; for nonzero powers of 2π the implementation correctly encloses π as the handoff explains. This is imprecise signed documentation, not a false soundness theorem or an exact-constant implementation claim.

This audit establishes scoped kernel validity and signed interface fidelity; it does not seal a frozen anchor, audit the five inherited SO-EXPR modules, or establish downstream checkHamBounds/checkTorusCertificate closure. No timing benchmark was independently rerun. The only repository edit is this report; generated files and pre-existing handoff are untouched.
