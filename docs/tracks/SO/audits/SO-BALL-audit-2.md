# SO-BALL independent audit 2

Overall verdict: **PASS WITH NOTES**. **F1 is closed.** The five SO-BALL exports and five signed range-reduction tests match the authoritative signatures. The three complex-exponential successes and all three required ball scenarios now have soundness pairings. No new mathematical, signature, or coverage failure was found. The sole hygiene exception is the explicitly permitted stale generated `KAM.lean`.

Audited HEAD: `db517b8fd041fb769d89e33a4beebfe6066cd2e8`; comparison `inp`: `f8405551c09bb7baf63ad01547cc2ecb8d372bbc`. Audit date: 2026-10-29 UTC. Round-2 implementation repair: `527aead5`. Independent reruns below were performed in `/root/code/KAM-inp-soball`.

Scope: only `KAM/Certificate/Expr/Ball.lean`, `KAM/Certificate/Tests/Ball.lean`, and `KAM/Certificate/Tests/ComplexExp.lean`. Read the repository rules, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, handoff including ROUND 2 FOCUS, audit 1, and the authoritative SO design/signature sections. The current external design has advanced beyond the handoff's Revision 4 description; its applicable F10 and SO-BALL contracts remain consistent with the signature file. Current design locators are used below. There is no SO statement.md in this checkout, and no SO-BALL frozen anchor/provider: signed SO declarations are the applicable contract. Frozen-provider equality and seal-body tests are inapplicable; independent signed-declaration copies replace them. This is package acceptance, not a frozen seal or downstream certificate closure.

The exact user-specified report path overrides the generic brief's main-worktree destination. Only this report is edited; probes and audit working files are under this worktree's `.lake/abi-scratch/` and are deleted after checks.

## Comparison and F1 closure

`git diff inp...HEAD` has multiple merge bases; git selects `6cad95806f4dbeafc1933f733daf875fdb3b097a`. Its ten-file diff includes the three audited sources, five inherited SO-EXPR dependency modules (Diff, DiffBuild, DiffCalculus, DiffNode, Slp), and the previous audit/handoff. Those five dependency modules have no direct `git diff inp HEAD -- <paths>` difference. Their presence in the three-dot comparison does not enlarge this audit's implementation scope.

`git diff c0e606b1..HEAD -- KAM/Certificate` changes only the two test modules: five containment corollaries and their docstrings. `Expr/Ball.lean` is byte-unchanged. A textual comparison confirmed every original test declaration, including its proof body, is unchanged. Ten signed headers compare exactly after whitespace normalization, with fully qualified names and binder order preserved; the signed cexpHalvings body also passes a definitional-equality probe.

The current design `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md:681` requires: “Each success is paired with `certCExpReduced_sound` (radius contains `exp`).” Tests/ComplexExp.lean:42,50,58 now prove that each actual successful call returns an output enclosing `Complex.exp w` for every w in precisely its input ball. The existence is derived from the original success test, not assumed. The radius-zero input assumptions select the exact centres 1/2 and 2; the third covers the whole radius-1/1000 ball about 19i. These are input-domain premises, not conclusion-shaped hypotheses.

The design at lines 682–684 requires the three ball scenarios to succeed with containment of their exact exp-slot values. Tests/Ball.lean:49,64 add the two missing pairings, alongside the existing exp-constant pairing at line 34. Each obtains the list from its original success theorem and applies Slp.val_mem_ball using the proved test weight. The same expression, dimension, centre, radius and Taylor order occur in success and containment. Every returned slot is covered, which includes all exp slots and is stronger than the requested pairing. These concrete domains are nonempty (zero angles and the stated action centre satisfy them); the slot fold preserves length, so coverage is not achieved by an empty replacement list. Negative controls remain unchanged. **F1: CLOSED.**

## Soundness and definitions

No added premise, instance or bundled field carries the target soundness result. The general ball theorem retains its exact signed hypotheses and original whole certified domain. The fold mirrors the exact evaluator, including zero defaults for unavailable slots and out-of-range actions. Centre/radius defaults agree with certDomain; nonpositive action radii can make the domain empty, as the original definition specifies. Character bounds conservatively include extra key entries. Every exp step uses certCExpReduced with its computed halving count; Option.bind propagates none. Compiled sin/cos use that exp path. No caller-side size condition was introduced.

Constants enclose the actual power of 2π (including reversed endpoints for negative exponents). Inversion derives nonzero operands from strict radius separation and the component-max lower bound for the complex norm. The strict boundary r = m rejects. The successful fold proves SlpInvGood; it is not assumed by the exported theorem. The structural nonvanishing induction keeps nested denominators, including beneath multiplication and powers. Empty-domain compiler calls provide prefix structure only; actual denominator values on D are identified only after the inductive nonvanishing result for the denominator. No circular analytic premise is used.

There are 12 definitions and 36 public theorems, with no new structures/abbreviations. Definition classification on the whole carrier: cexpHalvings is a total arithmetic count; ballPiLo/ballPiHi are integer-power endpoint enclosures; constBall encloses the actual constant; ballZero is the evaluator's exact zero default; ballOf is a lossless wrapper; ballStep is the seven-operation partial certified evaluator; ballsAux is its sequential option fold; Slp.balls starts that fold empty; BallRel is a length-and-containment invariant, including default slots; SlpInvGood is the internal proved inverse-operand predicate; testWeight is concrete rational fixture data. No fallback changes the intended object to evade a proof obligation. The helpers implement these arithmetic/fold/compiler obligations and claim no separate blueprint theorem.

## Declaration inventory

All verdicts below concern the scoped mathematical declaration; the permitted generated-root note applies to package hygiene only.

| Node / location | Declaration | Verdict | Reason / classification |
|---|---|---|---|
| SO-BALL; KAM/Certificate/Expr/Ball.lean:34 | `KAM.Certificate.cexpHalvings` (def) | PASS | Exact signed body; finite log2/ceiling count, no caller size premise. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:37 | `KAM.Certificate.certCExpSmall_reduced` (theorem) | PASS | Exact rational scaling identity; valid for all rational radii. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:49 | `KAM.Certificate.certCExpReduced_cexpHalvings_isSome` (theorem) | PASS | Exact signed type; nonnegative radius is precisely the signed completeness premise. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:70 | `KAM.Certificate.ballPiLo` (def) | PASS | Integer-power lower enclosure, reversed endpoints for negative degrees. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:73 | `KAM.Certificate.ballPiHi` (def) | PASS | Integer-power upper enclosure, reversed endpoints for negative degrees. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:75 | `KAM.Certificate.ball_two_pi_zpow_mem` (theorem) | PASS | Both enclosure directions, including negative degrees. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:92 | `KAM.Certificate.constBall` (def) | PASS | Product of exact complex rational coefficient and enclosed power of 2π. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:96 | `KAM.Certificate.mem_constBall` (theorem) | PASS | Contains the actual complex constant; accounts for π enclosure. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:119 | `KAM.Certificate.inv_ball_bound` (theorem) | PASS | Derives nonzero operand and inverse enclosure from strict separation. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:149 | `KAM.Certificate.ballZero` (def) | PASS | Exact zero default, agrees with unwritten-slot semantics. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:152 | `KAM.Certificate.ballOf` (def) | PASS | Lossless pair-to-ball wrapper. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:155 | `KAM.Certificate.ballStep` (def) | PASS | All seven operations; exp uses computed reduction; inverse rejects insufficient separation. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:184 | `KAM.Certificate.ballsAux` (def) | PASS | Sequential option fold; none propagates without replacement. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:197 | `KAM.Certificate.Slp.balls` (def) | PASS | Exact signed header; evaluates the whole operation list. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:204 | `KAM.Certificate.BallRel` (def) | PASS | Length equality plus containment at every index, including defaults. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:208 | `KAM.Certificate.toC_zero_rat` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:211 | `KAM.Certificate.toC_ratCast` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:214 | `KAM.Certificate.ballZero_mem` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:219 | `KAM.Certificate.BallRel.ballRel_nil` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:221 | `KAM.Certificate.BallRel.ballRel_snoc` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:239 | `KAM.Certificate.ballStep_sound` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:318 | `KAM.Certificate.ballsAux_sound` (theorem) | PASS | Exact zero/coercion or invariant-extension helper, proved without additional assumptions. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:336 | `KAM.Certificate.Slp.val_mem_ball` (theorem) | PASS | Exact signed type; domain-wide containment; hi is redundant but retained. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:347 | `KAM.Certificate.ballsAux_prefix_inv` (theorem) | PASS | Strict separation for each inverse operand is preserved in the final prefix. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:380 | `KAM.Certificate.SlpInvGood` (def) | PASS | Internal predicate proved from ball success, not assumed by the signed result. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:384 | `KAM.Certificate.Slp.invGood_of_balls` (theorem) | PASS | Successful balls imply every inverse operand is nonzero on the domain. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:407 | `KAM.Certificate.jetSmoothOn_empty` (theorem) | PASS | Empty-set smoothness used only for structural compiler-prefix facts. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:409 | `KAM.Certificate.slpInvNode_emit_prefix` (theorem) | PASS | Proves the denominator-validation inverse node survives compilation. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:438 | `KAM.Certificate.HamExpr.nonvanishingOn_of_inv_good` (theorem) | PASS | Structural induction; proves child nonvanishing before using compiler soundness on D. |
| SO-BALL; KAM/Certificate/Expr/Ball.lean:511 | `KAM.Certificate.HamExpr.nonvanishingOn_of_balls` (theorem) | PASS | Exact signed type; all recursive denominators certified, no extra premise. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:25 | `KAM.Certificate.testWeight` (def) | PASS | Concrete rational test fixture (rho = 1/4, w = 5). |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:27 | `KAM.Certificate.ballTest_weight` (theorem) | PASS | Kernel-decided valid weight. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:29 | `KAM.Certificate.ballTest_exp_const` (theorem) | PASS | Kernel-decided success; paired with the following containment theorem. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:34 | `KAM.Certificate.ballTest_exp_const_mem` (theorem) | PASS | Containment of every returned slot for the exp-constant case. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:43 | `KAM.Certificate.ballTest_exp_cos_mode` (theorem) | PASS | Unchanged kernel-decided success; now paired with ballTest_exp_cos_mode_mem. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:49 | `KAM.Certificate.ballTest_exp_cos_mode_mem` (theorem) | PASS | F1 repair: actual successful list exists; every returned slot encloses its exact program value throughout the identical certified domain; applies Slp.val_mem_ball. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:58 | `KAM.Certificate.ballTest_cos_large_action` (theorem) | PASS | Unchanged kernel-decided success; now paired with ballTest_cos_large_action_mem. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:64 | `KAM.Certificate.ballTest_cos_large_action_mem` (theorem) | PASS | F1 repair: actual successful list exists; every returned slot encloses its exact program value throughout the identical certified domain; applies Slp.val_mem_ball. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:74 | `KAM.Certificate.ballTest_div_ok` (theorem) | PASS | Kernel-decided separated-denominator success. |
| F10 / ball test 11; KAM/Certificate/Tests/Ball.lean:79 | `KAM.Certificate.ballTest_div_fails_closed` (theorem) | PASS | Kernel-decided boundary rejection (r = m). |
| F10 / range reduction; KAM/Certificate/Tests/ComplexExp.lean:25 | `KAM.Certificate.cexpTest_zero_small` (theorem) | PASS | Exact signed type and unchanged kernel-decided success; now paired with cexpTest_zero_small_mem. |
| F10 / range reduction; KAM/Certificate/Tests/ComplexExp.lean:28 | `KAM.Certificate.cexpTest_zero_large` (theorem) | PASS | Exact signed type; kernel-decided negative control. |
| F10 / range reduction; KAM/Certificate/Tests/ComplexExp.lean:31 | `KAM.Certificate.cexpTest_two_rejected` (theorem) | PASS | Exact signed type; kernel-decided negative control. |
| F10 / range reduction; KAM/Certificate/Tests/ComplexExp.lean:34 | `KAM.Certificate.cexpTest_two_reduced` (theorem) | PASS | Exact signed type and unchanged kernel-decided success; now paired with cexpTest_two_reduced_mem. |
| F10 / range reduction; KAM/Certificate/Tests/ComplexExp.lean:37 | `KAM.Certificate.cexpTest_large_pin` (theorem) | PASS | Exact signed type and unchanged kernel-decided success; now paired with cexpTest_large_pin_mem. |
| F10 / range reduction; KAM/Certificate/Tests/ComplexExp.lean:42 | `KAM.Certificate.cexpTest_zero_small_mem` (theorem) | PASS | F1 repair: actual successful output exists and encloses exp w for every w in the identical input ball; applies certCExpReduced_sound. |
| F10 / range reduction; KAM/Certificate/Tests/ComplexExp.lean:50 | `KAM.Certificate.cexpTest_two_reduced_mem` (theorem) | PASS | F1 repair: actual successful output exists and encloses exp w for every w in the identical input ball; applies certCExpReduced_sound. |
| F10 / range reduction; KAM/Certificate/Tests/ComplexExp.lean:58 | `KAM.Certificate.cexpTest_large_pin_mem` (theorem) | PASS | F1 repair: actual successful output exists and encloses exp w for every w in the identical input ball; applies certCExpReduced_sound. |

## Independent verification

All commands below were serialized for this audit with `LEAN_NUM_THREADS=1`; the gate invokes `nice -n 5 lake build`. No resource override or generated-root regeneration was used.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soball KAM.Certificate.Expr.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Tests.Ball
[inp-gate] slot 1 acquired 15:01:00 for KAM.Certificate.Expr.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Tests.Ball
Build completed successfully (2951 jobs).
exit 0
```

Only inherited warnings replayed: Arith/PiHigh.lean:218 unused simp argument Nat.succ_eq_add_one; Expr/Basic.lean:85 unused variable hS. No warning in the audited modules.

2. Independent signature and axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOBallAuditTwo.lean
exit 0
```

The probe copied all ten signed declaration headers from `/root/code/KAM-inp/.drafts/design/SOSignatures.lean` under fresh names and discharged them with the production exports. It checked the halving-count body by rfl and printed axioms for every one of the 36 public theorems, including all five repairs. Exact output:

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
'KAM.Certificate.ballTest_exp_cos_mode_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_cos_large_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_cos_large_action_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_div_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballTest_div_fails_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_zero_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_zero_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_two_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_two_reduced' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_large_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_zero_small_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_two_reduced_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_large_pin_mem' depends on axioms: [propext, Classical.choice, Quot.sound]

```

No sorryAx or additional axiom appears.

3. One kernel-replay invocation:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Tests.Ball
replaying KAM.Certificate.Tests.Ball
replaying KAM.Certificate.Tests.ComplexExp
replaying KAM.Certificate.Expr.Ball
exit 0
```

4. Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1311 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1 (only the permitted stale generated-root discrepancy)
```

5. Static checks: no forbidden proof escapes, native_decide, EuclideanSpace or option overrides in scope. Module headers and public sections are present; the executable ball definitions are in an exposed section. Expr/Ball.lean: 520 lines, maximum width 99; Tests/Ball.lean: 84 lines, maximum width 100; Tests/ComplexExp.lean: 65 lines, maximum width 98. All computational success/rejection controls and the test weight use decide +kernel. A declaration scan of KAM and Mathlib found no reused public short name; all declarations are under KAM.Certificate, with no harmful root shadow.

The transitive KAM import graph contains 47 modules, no providers and no frozen theorems. Eleven frozen definition modules are imported: ComplexStrip, DotC, GramMatrix, HamiltonianVectorFieldC, InvarianceError, IsPrimaryOnStrip, IsRealOnReals, NormalFrame, OmegaZero, Torsion, TorsionAverage. Every corresponding manifest entry was independently checked SEALED. No DRAFT_SORRY dependency occurs.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no diff; multiple-merge-base warning only)
git diff --check inp...HEAD
exit 0 (multiple-merge-base warning only)
```

## Errata, deviations and limits

No new suspected source, blueprint or frozen-statement defect was found. F1 and the previously overstated Tests/Ball docstring are repaired. The signed Slp.balls documentation at SOSignatures.lean:493 says “Constants exact”; constants with nonzero 2π-degree require the implemented π enclosure. This remains an inherited documentation imprecision, already noted in audit 1, rather than a false theorem. Keeping ball tests in a separate module preserves the lighter ComplexExp import boundary and does not change the contract.

Per-export verdicts for cexpHalvings, certCExpReduced_cexpHalvings_isSome, Slp.balls, Slp.val_mem_ball and HamExpr.nonvanishingOn_of_balls: **PASS**. Required test slice: **PASS**. Overall: **PASS WITH NOTES** solely for the permitted stale generated root. No frozen anchor is sealed by this report, no inherited SO-EXPR package is independently accepted here, and no downstream checkHamBounds/checkTorusCertificate or lunar theorem closure is asserted. Timing claims from the handoff were not independently benchmarked. No implementation deviation was introduced by this audit.
