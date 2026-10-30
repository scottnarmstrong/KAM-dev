# LOCK-SQRT delta audit 2

**Overall verdict: PASS WITH NOTES. Item (6), exact sqrt-free checker values: PASS.** Audit-1 F1 is closed under the user-supplied `kam-inp-24` ruling authorizing the four test-statement migrations. The corrected public ABI receipt matches this auditor’s fresh full-type comparison. No additional handwritten statement change was found. The standing generated-root lint exception and the disclosed certificate-format/namespace deviations remain notes, not a proof or numerical compatibility failure.

Auditor: `maud-locksqrt-2`, 2026-10-30 UTC. Report-only, focused tier-2 delta audit using the same statement-audit and manuscript-audit procedures as round 1. No subagents, implementation repair, Git mutation or generated-file update. Temporary probes/logs are in this worktree’s `.lake/abi-scratch/` and removed after recording their evidence. This report is the only retained edit.

## Fixed scope and authority

- Baseline: `1316016668e558526520a7820d3f6c94afaa2d96`.
- Implementation audited: `a12b69cb0f35e3e57fa76f5b793c44269f855f68`.
- Current package HEAD / corrected receipt: `775696902ccfe97e43b0e71a314491687d96cbd0`.
- `git show 77569690` adds the round-1 report and corrected handoff only. `git diff --exit-code a12b69cb HEAD -- KAM scripts manifest README.md KAM.lean` is empty (exit 0). Every one of the 24 implementation files is unchanged from round 1.
- Reviewed `git diff 13160166 a12b69cb` including **all 16 edited landed Lean modules, six new Lean modules, nine test/data migrations and both Python emitters**, not just new primitive files. The implementation diff is 1231 insertions and 62 deletions.
- Read the supplied package audit brief, repository rules/PLAN/DECISIONS, the full corrected handoff and namespace note, LOCK-SQRT implementation brief, design §4 and design audits 2–3. Design/signatures have the same hashes as round 1: design `7785225bb6f3d3985ae7719f3aecf107eb33302530147bbff5672935eb170c6d`; `SOLockSignatures.lean` `aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d`.
- The exact declaration ledger, expanded signed-binder table, definition classification and scalar/jet/witness proof review of [audit 1](LOCK-SQRT-audit-1.md) apply to the identical implementation. This report supersedes its F1 disposition only; it does not rewrite the historical FAIL. The authoritative new ruling is supplied explicitly in this user request, and is also identified in commit `77569690` and handoff:46–47; it extends the exception to precisely `composeTest_noChar`, `composeTest_noExp`, `composeTest_noInv`, `composeTest_n2`.
- No frozen theorem or provider is introduced or sealed. This is a trusted checker-extension audit, not a seal-ready I/N/P or lunar headline theorem claim.

## 1. Corrected ABI receipt: PASS; audit-1 F1 closed

The corrected receipt says the first run used abbreviated single-line output and missed the four test statements. This agrees with this auditor’s independent round-1 observation and the fresh comparison below. Probes use `pp.all true`, `pp.oneline false`, `pp.fullNames true`; no resource override. The baseline checkout used for read-only elaboration was `/root/code/KAM-inp` at `4a46fd6476e6cef375650b0ff949c4f74c735aaa`. A source comparison against `13160166` over the relevant checker paths is empty, so its pre-extension oleans supply the same comparison surface. Scratch files and logs stay in the package worktree.

A fresh environment enumeration prints each constant’s complete type, restricted by its defining module to the 16 edited landed modules. Separately, source extraction identifies all 392 handwritten baseline declarations. Results:

| Surface | Identical retained | Changed | Removed | New |
|---|---:|---:|---:|---:|
| Handwritten baseline declarations | 387 | 4 authorized test propositions | 1 sanctioned helper | Replacement and new helpers as classified in audit 1 |
| Public, non-internal declarations (receipt’s surface, includes generated APIs) | — | **29** | **1** | **27** |
| All enumerated defining-module constants, including compiler-private/internal artifacts | 876 | 85 | 8 | 51 |

The full environment contains 969 baseline and 1012 new constants. The four handwritten changes are exactly the fourth empty `Witnesses` field inside the four authorized composition-test propositions. All other retained handwritten types agree. The old helper is removed; `HamExpr.nonvanishingOn_of_program_good` has exactly the approved extra `SlpSqrtGood` premise. No old production theorem acquires an additional premise or weakened conclusion.

**Counting clarification:** the receipt’s 29/1/27 is exact on the public non-internal surface, not a count of every compiler implementation artifact. Filtering names with an underscore-prefixed component removes private proofs, match splitters, `_sparseCasesOn` and `_flat_ctor` auxiliaries. The additional changes in the raw dump are all generated, not further handwritten drift. In particular, the five non-private but internal changed names are `HamExpr.NonvanishingOn._sparseCasesOn_1` and its `.else_eq`, `Witnesses.mk._flat_ctor`, and `opDeps._sparseCasesOn_1` and its `.else_eq`; new `Witnesses.sqrtWit._default` is also internal. Thus interpreting “every declaration” as literally every environment artifact would overstate the receipt’s coverage. This clarification does not reopen F1 or require another statement exception.

The complete 29-name public changed list is:

```text
KAM.Certificate.HamExpr.NonvanishingOn.eq_8
KAM.Certificate.HamExpr.NonvanishingOn.eq_def
KAM.Certificate.HamExpr.NonvanishingOn.match_1
KAM.Certificate.HamExpr.casesOn
KAM.Certificate.HamExpr.eval.eq_def
KAM.Certificate.HamExpr.eval.match_1
KAM.Certificate.HamExpr.rec
KAM.Certificate.HamExpr.recOn
KAM.Certificate.SlpOp.casesOn
KAM.Certificate.SlpOp.rec
KAM.Certificate.SlpOp.recOn
KAM.Certificate.SlpOp.step.match_1
KAM.Certificate.Witnesses.casesOn
KAM.Certificate.Witnesses.mk
KAM.Certificate.Witnesses.mk.inj
KAM.Certificate.Witnesses.mk.injEq
KAM.Certificate.Witnesses.mk.noConfusion
KAM.Certificate.Witnesses.mk.sizeOf_spec
KAM.Certificate.Witnesses.rec
KAM.Certificate.Witnesses.recOn
KAM.Certificate.ballStepG.match_5
KAM.Certificate.composeStep.match_7
KAM.Certificate.composeTest_n2
KAM.Certificate.composeTest_noChar
KAM.Certificate.composeTest_noExp
KAM.Certificate.composeTest_noInv
KAM.Certificate.slpCompile.match_1
KAM.CertificateSharp.opDeps.eq_5
KAM.CertificateSharp.opDeps.match_1
```

The only removed public declaration is `KAM.Certificate.HamExpr.nonvanishingOn_of_inv_good`. The 27 new public declarations are:

```text
KAM.Certificate.HamExpr.NonvanishingOn.eq_9
KAM.Certificate.HamExpr.eval.eq_13
KAM.Certificate.HamExpr.nonvanishingOn_of_program_good
KAM.Certificate.HamExpr.sqrt
KAM.Certificate.HamExpr.sqrt.elim
KAM.Certificate.HamExpr.sqrt.inj
KAM.Certificate.HamExpr.sqrt.injEq
KAM.Certificate.HamExpr.sqrt.noConfusion
KAM.Certificate.HamExpr.sqrt.sizeOf_spec
KAM.Certificate.Slp.sqrtGood_of_balls
KAM.Certificate.SlpOp.sqrt
KAM.Certificate.SlpOp.sqrt.elim
KAM.Certificate.SlpOp.sqrt.inj
KAM.Certificate.SlpOp.sqrt.injEq
KAM.Certificate.SlpOp.sqrt.noConfusion
KAM.Certificate.SlpOp.sqrt.sizeOf_spec
KAM.Certificate.SlpSqrtGood
KAM.Certificate.Witnesses.sqrtWit
KAM.Certificate.ballStepG.eq_8
KAM.Certificate.ballStep_sqrt_lt
KAM.Certificate.ballsAux_prefix_sqrt
KAM.Certificate.ballsSpec_prefix_sqrt
KAM.Certificate.composeStep.eq_8
KAM.Certificate.composeStep.match_9
KAM.CertificateSharp.ballsAuxT_prefix_sqrt
KAM.CertificateSharp.opDeps.eq_6
KAM.CertificateSharp.sqrtGood_of_ballsTrig
```

`checkHamBounds_sound` and `KAM.CertificateSharp.V2.checkTorusCertificateV2_sound` were also explicitly printed in both environments: full elaborated type **and axiom output are identical**. Their files are byte-identical to the baseline. Both depend on precisely `propext`, `Classical.choice`, `Quot.sound`, with no project axiom or `sorryAx`.

## 2. Definite verdict for SO-DATA3: PASS, bit-exact sqrt-free values

The comparison is between the same pre-existing input data and backend/engine, with the evident constructor-preserving inclusion of the old expression/program language and the empty-field migration

`⟨expWit, invWit, charWit⟩ ↦ ⟨expWit, invWit, charWit, []⟩`.

“Sqrt-free” means **no `.sqrt` anywhere in the expression/program**, including dead subexpressions/operations. For Bool, rational slot-ball and model results, the verdict is equality of the values themselves, not merely equivalent enclosure validity or equal pass/fail implications. For `prune`’s program/witness result, it is equality after this necessary data-type inclusion: old fields and opcode/slot lists agree exactly and the extra field is `[]`. The changed record arity is not a claim of identical record memory layout or identical generated Lean source text.

### Argument covering every requested function

| Function / layer | Exact preservation argument | Verdict |
|---|---|---|
| `HamExpr.eval`, domain predicate | Existing cases unchanged; structural induction on old syntax. The new root case is unreachable. | PASS |
| `SlpOp.step`, `Slp.vals` | All seven old opcode arms identical. Same default `getD … 0`, action indexing and constants. Induct on the unchanged fold over the same opcode list. | PASS |
| `ballStepG`, `ballStep` | Only a new root arm is added. Every old arithmetic expression and guard is unchanged; `ballForce`, `ballZero`, precision, rounding and operand reader are unchanged. | PASS |
| `ballsRev`, `ballsAux`, `Slp.balls`, `ballsSpec` | Identical definitions. Induct on old opcode list and accumulator: equal old-arm balls give the same next accumulator, same early `none`, and same final reverse. | PASS, same entire rational ball list |
| `stepT`, `ballsAuxT`, `ballsTrig` | Executable definitions are unchanged. Same character tags, conjugate-pair/cosh detection, radii and fallback. Their calls to `ballStep` agree by the previous row. Induct on the shaped accumulator. | PASS, same shapes and slot balls |
| `slpCompile`, `HamExpr.jet` | Only new expression root arm; all old branches and node builders unchanged. Structural induction preserves emitted opcode sequence, folding, ordering, lengths and derivative slot tables. No extra root operation is emitted for an old expression. | PASS |
| `composeStep`, `composeOps`, `Slp.compose` | Every old arm is unchanged; only `.sqrt` reads `sqrtWit`. Same `ComposeState` fields/initial state, character cache, exp/inv counters, degree conversion, product keys, wanted-slot selection and failure order. Induction on the fold gives identical states/models and `none` decisions. | PASS, same degree/polynomial/radius values |
| `opDeps` | The four old dependency cases and old fallback are unchanged. Root arm unreachable. | PASS, same lists |
| `liveSet`, `liveClosed`, `pruneOk`, `pruneOps` | Definitions unchanged and old `opDeps` values equal, hence identical backward closure, validation Bool and retained/zeroed instructions. Zero instruction is unchanged and sqrt-free. | PASS |
| `prune`, `Slp.composePruned` | Same closure and flags retain exactly the same exp/inv witnesses and character table; new root-witness list is copied as `[]`. Rejected pruning returns the same original pair under inclusion. Pruned program remains sqrt-free, so the composition induction applies. | PASS |
| `checkHamBounds` | Definition unchanged: same compiled jet, same slot balls and same `hamBoundsOk` sums/comparisons with the same M. | PASS, same Bool |
| V2 landed base / `checkV2With` / `checkTorusCertificateV2` | Definitions unchanged: same ordered sub-check conjunction. All base sub-checks depend on the already-equal jet, composition models and unchanged arithmetic/data. | PASS, same Bool |
| Existing V2 engine tests | `sharpV2` uses unchanged sharp smallness; `routeAFrozen` reads unchanged params/box/witness in `frozenCore`; `routeARefined` reads unchanged `checkHamClaim` balls and frame/torsion models plus unchanged `refinedCore`. `routeAV2`/`orElse` keep the same Sum dispatch. | PASS, same Bool |

`EngineV2` and `BaseChecker` accept arbitrary user-supplied tests. As usual, comparing the same checker across revisions means transporting that existing test, not substituting an unrelated new one. The shipped base checkers and all listed engine variants were traced; no test, scalar bound, conjunction order or dispatch changed in this branch.

**Mechanical support for the general argument:** a comment/whitespace-insensitive extraction compared every one of the 69 existing definitions in the seven edited production modules. **61 are identical; seven differ only by the added `.sqrt` arm; `prune` differs only by copying the fourth field.** Erasing just that new arm/field makes every compared definition identical. All arithmetic/model/weight/π/rounding helpers, build/toolchain pins and V2 files are outside the implementation diff and unchanged. The extension adds no new numeric typeclass instance or rewriting attribute that changes old checker arithmetic.

No default changes: `slpBallPrec = 320`, `ballZero`, invalid action/slot defaults, reciprocal guard, exp range reduction, Taylor order, `dyDown`/`dyUp`, rational arithmetic, balanced traversals, advice selection and fallback are preserved. There is no new rounding call on an old branch. This proves conservation of each rational centre/radius and of each backend model value, not just approximate agreement. Invalid sqrt-free operands and early-failure paths are included because the defaults and Option branches are identical.

The field is unused on a sqrt-free program even if its new list is nonempty; legacy input migration chooses `[]`, which also makes the complete pruned witness record the direct inclusion of the old one.

### Independent exact-output regressions

The same scratch file was evaluated in the baseline and current environments. It exercises all seven old opcodes; plain and trig slot-ball lists; an out-of-range reciprocal failure; dependency lists; successful full and pruned composition including exp/character/inverse witnesses; failing pin composition; pruning witness counts/keys; positive and negative `checkHamBounds`; and a passing full V2 refined certificate.

Both runs exit 0, no diagnostics; their **31,616 output bytes are identical**, SHA256 `a0677dd3372259c3af87a1d539c5a92060c7a20088836727ed8e2e1d18e0890f`. The last three Bool results are `true`, `false`, `true`. Ball centres/radii and model degrees/terms/radii were printed explicitly as rational tuples. These evaluations support the source-induction argument; they are not substituted for a universal kernel conservativity theorem. No such new theorem is claimed by this report.

**Consequence for SO-DATA3:** this extension requires no numerical-value re-emission for sqrt-free certificates. Existing three-field anonymous Lean witness constructors do require `, []`, or equivalent named-field syntax. The Python mirrors’ existing sqrt-free arithmetic relation is preserved; this audit does not assert that an independently unverified mirror was correct before this change. The two emitters change only witness-literal syntax and, for the generated pruning mirror, the unreachable sqrt dependency arm and field copying; no old numerical payload changes. Both Python files parse successfully, and their ASTs are identical to baseline after replacing string-constant values by a marker: all changes are generated-text strings, not generator arithmetic or control flow.

## 3. Remaining requested soundness and deviation checks

| Obligation | Verdict | Evidence / refutation |
|---|---|---|
| Total root / signed declarations / namespace | PASS | Literal `sqrtE` body and all eight copied source theorem headers still elaborate, with no extra premise. `kam-inp-24` accepts the shared checker namespace; no frozen declaration is relocated. Full signed-binder audit remains in audit 1 on identical source. |
| `ballSqrt` | PASS | Original `r < re c` guard; positive anchor and `R < s²`; triangle bound `|re c-s²|+|im c|+r`; `sqrtE_ball` then outward `ballRound_mem`. Newton accuracy is untrusted and not a proof premise. All old rounding paths unchanged. |
| Jets through order three | PASS | Coefficients `1/2`, `-1/4`, `3/8`; three mixed cross terms; reciprocal-root powers computed by existing product/inverse rules; compiler and safety prefix use the actual emitted root instruction. No circular domain assumption. |
| Slot-keyed witness / F2 | PASS | Positive anchor/margin and residual model checks establish `re W ≥ s-d > 0`, radicand positivity and denominator ≥ `s-d`. Opposite-root and negative-anchor controls reject; missing/wrong-slot witness rejects. Fresh source-header/edge probe succeeds. |
| Ordinary/trig safety extraction | PASS | Each successful root operation certifies operand positivity, including prefix transport. Invalid references force impossible default-ball positivity. Both direct consumers provide inverse and root safety from their successful ball passes. |
| Two consumer soundness statements/axioms | PASS | Full type and standard-three axiom output independently identical in both environments; files unchanged. |
| Deviation 1: slot key instead of counter | ACCEPTED NOTE | Preserves `ComposeState` ABI and pruning alignment; no effect on old paths. |
| Deviation 2: fourth witness field | ACCEPTED NOTE | Changes constructor arity and the four now-authorized test propositions; preserves legacy numerical values under empty-field migration. No extra handwritten drift. |
| Deviation 3: reciprocal powers in jets | ACCEPTED NOTE | Same derivative formulas, derived and proved through third order. Only reached for a new root expression. |
| Deviation 4: explicit guard / slit-plane lemma | ACCEPTED NOTE | Conservative rejection and stronger analytic support; no extra premise on signed root contracts. |
| Deviation 5: product site `[3]` | ACCEPTED NOTE | Re-keyed by root slot; checked model multiplication/fallback pays all residual error. Site unused on old paths. |

Definition classification is unchanged from audit 1: 28 new literal/computational/data definitions/structures, no hidden proof field or arbitrary mathematical choice. `sqrtE`’s zero-on-cut clause is the explicit signed semantics; checker `none` denotes rejection. The six new modules have the identical hashes already audited and kernel-replayed in round 1. This delta additionally replays every edited landed module separately below, as requested.

## 4. Landed-file review ledger

| Edited landed file | Reviewed executable / statement delta | Verdict |
|---|---|---|
| `KAM/Certificate/Expr/Ball.lean` | New root arm and safety extraction; sanctioned helper replacement; old numerical definitions preserved | PASS |
| `KAM/Certificate/Expr/Basic.lean` | Append root constructor, eval/domain arms and proof cases; all old cases preserved | PASS |
| `KAM/Certificate/Expr/Compose.lean` | Append witness field and root arm; four authorized test propositions only in test module | PASS |
| `KAM/Certificate/Expr/Diff.lean` | New compiler root arm; old builders and emitted program order preserved | PASS |
| `KAM/Certificate/Expr/Slp.lean` | Append opcode and value arm; old opcode order and step arms preserved | PASS |
| `KAM/Certificate/Tests/Compose.lean` | Empty field migration; exactly four authorized handwritten proposition changes | PASS |
| `KAM/Certificate/Tests/Defs.lean` | Empty fourth witness-list migration only; old rational/model payload unchanged | PASS |
| `KAM/Certificate/Tests/Negative.lean` | Empty fourth witness-list migration only; old rational/model payload unchanged | PASS |
| `KAM/Certificate/Tests/RatData.lean` | Empty fourth witness-list migration only; old rational/model payload unchanged | PASS |
| `KAM/Certificate/Tests/Torsion.lean` | Empty fourth witness-list migration only; old rational/model payload unchanged | PASS |
| `KAM/Certificate/Tests/Toy2Data.lean` | Empty fourth witness-list migration only; old rational/model payload unchanged | PASS |
| `KAM/Certificate/Tests/Toy2dData.lean` | Empty fourth witness-list migration only; old rational/model payload unchanged | PASS |
| `KAM/Certificate/Tests/Toy3Data.lean` | Empty fourth witness-list migration only; old rational/model payload unchanged | PASS |
| `KAM/CertificateSharp/Ham/BallsTrig.lean` | Only proof/safety additions; executable trig evaluator unchanged | PASS |
| `KAM/CertificateSharp/Kernel/Prune.lean` | Append root dependency arm and copy keyed list; legacy closure and witness selection identical | PASS |
| `KAM/SpinOrbit/Tests/GraphCert.lean` | Empty fourth witness-list migration only; old rational/model payload unchanged | PASS |
| `scripts/spin_orbit/toy_lean_cert.py` | Emits the same witness payload plus `[]`; no numerical generator calculation changed | PASS |
| `scripts/sjs/kernel_probe_gen.py` | Same literal update; generated mirror adds root dependency arm/field copying only | PASS |

## 5. Verification evidence

All Lean/Lake operations in this audit are serial with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build wrapper supplies `nice`. No parallel audit Lean jobs, clean/update/cache fetch, frozen/generated edit or resource override. Fresh source probes initially omitted some test imports; only scratch unknown-name errors resulted. The imports were corrected and the complete probe rerun successfully; no production failure was hidden.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-locksqrt \
 KAM.Certificate.Tests.Sqrt KAM.Certificate.Tests.Compose KAM.Certificate.Tests.Defs \
 KAM.Certificate.Tests.Negative KAM.Certificate.Tests.RatData KAM.Certificate.Tests.Torsion \
 KAM.Certificate.Tests.Toy2Data KAM.Certificate.Tests.Toy2dData KAM.Certificate.Tests.Toy3Data \
 KAM.CertificateSharp.Ham.BallsTrig KAM.CertificateSharp.Kernel.Prune KAM.SpinOrbit.Tests.GraphCert \
 KAM.CertificateSharp.V2.Engine KAM.Certificate.Sound.Ham
```

Exit 0: `Build completed successfully (3408 jobs).` Replayed warnings are inherited; no new-file warning or default-heartbeat failure.

### Full ABI and consumer comparison

```sh
# Package worktree:
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/locksqrt2-dump.lean
# Baseline checkout, same absolute worktree scratch input:
LEAN_NUM_THREADS=1 nice -n 5 lake env lean /root/code/KAM-inp-locksqrt/.lake/abi-scratch/locksqrt2-dump.lean
```

Both exit 0, no diagnostics. Environment enumeration uses `env.getModuleIdxFor?` and the 16-module ownership list, so generated declarations and private compiler artifacts are classified rather than mistaken for source declarations. Full outputs are compared by qualified name; only the declared public differences and generated artifacts listed above occur. Current consumer axiom outputs (pretty-printed with universe arguments) are:

```text
KAM.Certificate.checkHamBounds_sound: [propext, Classical.choice, Quot.sound]
KAM.CertificateSharp.V2.checkTorusCertificateV2_sound: [propext, Classical.choice, Quot.sound]
```

### Signed headers and axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/locksqrt2-signed.lean
```

Final exit 0, no diagnostics. The eight signed source-header examples, literal definition checks, safety contract, positive/negative trig-ball tests and slot-keyed pruned composition probe from audit 1 are rerun on unchanged implementation. Every one of the 215 public theorems in changed source files is checked with `#print axioms`; the three main new soundness lemmas are additionally repeated. All use subsets of the standard three foundations; no `sorryAx` or project axiom. The two consumer checks above are separate.

### Exact-value regression

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/locksqrt2-values.lean
# Baseline checkout:
LEAN_NUM_THREADS=1 nice -n 5 lake env lean /root/code/KAM-inp-locksqrt/.lake/abi-scratch/locksqrt2-values.lean
```

Both exit 0, complete stdout byte-for-byte equal with the hash given in §2. The exact probe is recorded below for reproducibility:

```lean
import KAM.Certificate.Tests.Compose
import KAM.Certificate.Tests.Defs
import KAM.CertificateSharp.Ham.BallsTrig
import KAM.CertificateSharp.Kernel.Prune
import KAM.CertificateSharp.V2.Tests.Refined
open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2
private def encB (x : Option (List (CC ℚ × ℚ))) :=
  x.map fun bs => bs.map fun b => (b.1.re, b.1.im, b.2)
private def encM (x : Option (List (CertModel ℚ))) :=
  x.map fun ms => ms.map fun m => (m.deg, m.poly.terms.map (fun t => (t.1, t.2.re, t.2.im)), m.rad)
private def oldOps : List SlpOp :=
  [.const 1 0 0, .action 0, .char [1], .add 0 1, .mul 3 0, .exp 0, .inv 0]
#eval encB (Slp.balls 1 ⟨oldOps⟩ ⟨1 / 100, 11 / 10⟩ [1] [1 / 10] 8)
#eval encB (ballsTrig 1 ⟨oldOps⟩ ⟨1 / 100, 11 / 10⟩ [1] [1 / 10] 8)
#eval encB (Slp.balls 1 ⟨[.inv 8]⟩ ⟨1 / 100, 11 / 10⟩ [1] [1 / 10] 8)
#eval oldOps.map opDeps
#eval encM (composeTestRun 0 (composeTestWit 0) [0, 1, 2, 3, 4, 5, 6, 7, 8])
#eval encM (Slp.composePruned 1 composeTestProg (composeTestK 0) (composeTestWit 0)
  composeTestW composeTestCfg composeTestPi [0, 1, 2, 3, 4, 5, 6, 7, 8])
#eval encM (composeTestRun 3 (composeTestWit 0) [0])
#eval let r := prune composeTestProg (composeTestWit 0) [8];
  (r.1.ops.map opDeps, r.2.expWit.length, r.2.invWit.length, r.2.charWit.map Prod.fst)
#eval checkHamBounds (defsTestCert 2 2 (1 / 2) (1 / 2))
#eval checkHamBounds (defsTestCert 1 2 (1 / 2) (1 / 2))
#eval checkTorusCertificateV2 routeARefined toyCert2 toyRefinedWit
```

### Serial, individual-module kernel replay

For each module below, **one complete invocation was awaited before starting the next**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose MODULE
```

This is the user-requested per-module replay of all 16 edited landed modules, plus both consumer modules, rather than a concurrent or grouped replay. All 18 invocations exit 0. Exact output for each is `replaying MODULE`. No replay was skipped after a failure.

| Module | Exit | Wall seconds |
|---|---:|---:|
| `KAM.Certificate.Expr.Ball` | 0 | 16.55 |
| `KAM.Certificate.Expr.Basic` | 0 | 15.66 |
| `KAM.Certificate.Expr.Compose` | 0 | 17.11 |
| `KAM.Certificate.Expr.Diff` | 0 | 15.99 |
| `KAM.Certificate.Expr.Slp` | 0 | 13.85 |
| `KAM.Certificate.Tests.Compose` | 0 | 19.56 |
| `KAM.Certificate.Tests.Defs` | 0 | 25.58 |
| `KAM.Certificate.Tests.Negative` | 0 | 59.14 |
| `KAM.Certificate.Tests.RatData` | 0 | 13.32 |
| `KAM.Certificate.Tests.Torsion` | 0 | 28.21 |
| `KAM.Certificate.Tests.Toy2Data` | 0 | 12.56 |
| `KAM.Certificate.Tests.Toy2dData` | 0 | 12.18 |
| `KAM.Certificate.Tests.Toy3Data` | 0 | 9.09 |
| `KAM.CertificateSharp.Ham.BallsTrig` | 0 | 9.94 |
| `KAM.CertificateSharp.Kernel.Prune` | 0 | 9.6 |
| `KAM.SpinOrbit.Tests.GraphCert` | 0 | 11.03 |
| `KAM.Certificate.Sound.Ham` | 0 | 10.91 |
| `KAM.CertificateSharp.V2.Engine` | 0 | 12.4 |

The unchanged six new modules retain audit 1’s successful kernel replay on the same implementation hash; all source-header, edge and axiom probes were also rerun here.

### Evidence hashes

| Input / evidence | SHA256 |
|---|---|
| `docs/tracks/SO/audits/LOCK-SQRT-audit-1.md` | `627d55afd6266e99a3e67c7b2cb8b3ea9a511ed11d28d366887dd4928cdd2a1b` |
| `docs/tracks/SO/audits/LOCK-SQRT-handoff.md` | `82516bed8336414666012fb9e7fa64dfb72917e7a07251c8eb3e67e5ad5cadd1` |
| Temporary `locksqrt2-base.log` (removed after recording) | `331f34ef0efa20db7ae2323104fb1a052c44e73871be9256373dff6bc83914a1` |
| Temporary `locksqrt2-head.log` (removed after recording) | `89930e07c3af0001981649d302432d378159ca46464b47a69e103d22764dcc27` |
| Temporary `locksqrt2-signed.lean` (removed after recording) | `b121f18c8cd799e3b54a547c0961cad536a34a78cfc6473712c2cde70d268394` |
| Temporary `locksqrt2-signed.log` (removed after recording) | `a82599062368a8b4a64c4154171462651a797bf989e480d03138cd132f055ed8` |
| Temporary `locksqrt2-values.lean` (removed after recording) | `bde1ea8cff044cfd756318240584141ab4282e2604b24fbc6878c53a37514a32` |
| Temporary `locksqrt2-values-base.log` (removed after recording) | `a0677dd3372259c3af87a1d539c5a92060c7a20088836727ed8e2e1d18e0890f` |
| Temporary `locksqrt2-values-head.log` (removed after recording) | `a0677dd3372259c3af87a1d539c5a92060c7a20088836727ed8e2e1d18e0890f` |
| Temporary `locksqrt2-replay.json` (removed after recording) | `644a65925bf13695024aa9d08d38dea6edab8b599029bc356cfcba884b543030` |
