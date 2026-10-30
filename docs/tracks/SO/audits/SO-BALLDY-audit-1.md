# SO-BALLDY independent audit 1

Audit date: 2026-10-30. Worktree: `/root/code/KAM-inp-soballdyl`.
HEAD: `bd736e979438cc5d440b073dbbf5ef9a1f329c24`.
Comparison `inp` and merge base: `4a3de4ba771d9142935280c03fbb2e03842a1513`.

## Verdict

**PASS WITH NOTES** for the D39 checker implementation change. No mathematical soundness
failure was found; all independent builds, old-type probes, axiom checks and kernel replay pass.
Lint's only failure is the expressly permitted stale generated root. There are no frozen anchors
to seal. The literal source-header requirement has two named-binder presentation exceptions,
listed below, although all original types and theorem statements are preserved.

| Anchor / consumer | Verdict | Qualification |
|---|---|---|
| SO-BALLDY / D39 | PASS WITH NOTES | Implementation sound; source-header and documentation notes below. |
| `ballRound_mem`, `ballExp_sound` | PASS | General containment; no missing magnitude/exponent premise. |
| `checkHamBounds_sound` | PASS | Unchanged file, rebuilt and kernel-replayed. |
| `checkTorusCertificate_sound` | PASS | Rebuilt, replayed, allowed axioms only. |
| `checkTorusCertificateSharp_sound` | PASS | Rebuilt, replayed, allowed axioms only. |
| Frozen theorem sealing | N/A | No provider or frozen theorem changed/proved in this package. |

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` (especially D39),
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the full
`docs/tracks/SO/audits/SO-BALLDY-handoff.md`, and its AUDIT FOCUS. Reviewed the full
`git diff inp...HEAD`, SO design revision 7 (`docs/tracks/SO/design/SO-LEAN-DESIGN.md`),
relevant track I/N/P conventions, the unchanged Hamiltonian consumer, rational arithmetic backend,
and frozen complex-strip/vector-field/invariance-error definitions.

This is a checker implementation audit under D39, not a frozen-anchor provider package.
No frozen theorem is being sealed; provider/frozen-type and seal-body probes are consequently
not applicable. The changed modules import no frozen theorem or provider. The transitive
closure of the two certificate soundness consumers contains frozen definitions but no frozen
theorem or provider, and therefore no DRAFT_SORRY theorem dependency.

The three-dot diff has exactly two Lean files and the handoff:
`KAM/Certificate/Expr/Ball.lean` (+implementation/proof changes),
`KAM/Certificate/Expr/BallRound.lean` (new), and
`docs/tracks/SO/audits/SO-BALLDY-handoff.md`.
The prompt's explicit report destination inside this worktree overrides the generic brief's
main-worktree destination. Only this report is changed outside `.lake/abi-scratch/`.

## Findings and scope limitations

1. **Source-header presentation differs in two definitions.**
   At `KAM/Certificate/Expr/Ball.lean:206`, old `ballStep` ended in
   `(acc : List (CC ℚ × ℚ)) : SlpOp → Option (CC ℚ × ℚ)`; now it ends in
   `(acc : List (CC ℚ × ℚ)) (op : SlpOp) : Option (CC ℚ × ℚ)`.
   At line 228, old `ballsAux` ended in
   `: List (CC ℚ × ℚ) → List SlpOp → Option (List (CC ℚ × ℚ))`; now it names
   `(acc : List (CC ℚ × ℚ)) (ops : List SlpOp)`.
   These are the same curried types with named binders, but are not literally identical source
   headers. All other 30 pre-existing declaration headers are textually identical. In particular,
   every existing theorem statement and `Slp.balls`'s header and body are unchanged.
   The exact-header focus therefore has this explicit syntactic exception; no changed
   mathematical premise or conclusion was found.
2. **Two stale descriptions in the new module.**
   `BallRound.lean:14` says balls are rounded “after every operation”; lines 36–38 say
   “every slot ball is rounded”. `ballStepG` at `Ball.lean:167–195` actually rounds only
   multiplication, inverse and exponential, as correctly documented by the handoff.
   `BallRound.lean:155–156` says “grid `2^-P`”; the actual grid is
   `2^(ilog2Q (|re| + |im| + r) - P)`, recomputed for each intermediate ball.
   These comments should be corrected on landing; no source edit was made by the auditor.
3. **Older design describes the previous exponential implementation.**
   `SO-LEAN-DESIGN.md:162,237–239` names `certCExpReduced` directly for expression slots.
   D39 and the handoff supersede that implementation description with `ballExp`; enclosure,
   computed halving count, successful-call premise and fail-closed contracts remain intact.
4. **Performance receipt remains scoped.** The handoff's 91-second/8.98-GB lunar measurements,
   bit-for-bit Python comparisons, and old-pass OOM comparisons were not independently rerun.
   They concern the R1 data on the writer's other branch, not a new certified performance bound
   for all inputs. This audit independently checks proofs, regression builds, and kernel replay.

## Soundness and value preservation

`ballRound_mem_aux` (`BallRound.lean:80–99`) uses floor bounds for both centre coordinates,
then the complex triangle inequality and the sum of coordinate errors, followed by the upward
radius bound. No restriction on the exponent, magnitude, precision, centre sign, or radius is
introduced. `dyScale_pos` holds for every integer, including `negSucc`; `ballRound_mem` thus
covers negative grid exponents, zero magnitude, tiny and huge balls. A negative input radius
has no member, so the containment implication is vacuous there rather than an unsound
fallback. General containment does not require an accuracy theorem about `ilog2Q`.

`ballSqIter_mem` propagates the exponential enclosure through every rounded square.
`ballExp_sound` includes exact rational range reduction, the `certCExpSmall` guard, the Taylor
remainder, initial outward rounding, all subsequent roundings, and the identity restoring
`exp w`. Its only premises are a successful call and membership in the input ball.

`ballStepG` tests `r < max |re| |im|` on the stored operand before inverse construction.
Successful operand membership implies `r ≥ 0`, so the test excludes zero and guards both
`re² + im²` and `(m-r)m`; `inv_ball_bound` supplies the reciprocal bound before rounding.
`ballStep_inv_lt`, the prefix invariant and `Slp.invGood_of_balls` retain that exclusion.
Malformed forward references use the existing zero fallback: inverse of that fallback rejects.
Invalid action indices retain the existing zero semantics. No checker theorem gains a
conclusion-shaped premise. The operand enclosure premise of `ballStepG_sound` is the
inductive invariant, discharged from `BallRel` by `ballStep_sound`.

`plusQ_eq` and `timesQ_eq` prove equality to the old rational backend formulas, whose
arithmetic errors are zero. `revGet_reverse` holds for all indices, including out-of-range
indices. `ballsRev_eq` and `ballsAux_eq_spec` cover arbitrary starting accumulators, empty
programs, and both success and failure. These compare implementations of the **new rounded**
step; they do not claim rounded balls equal the old unrounded evaluator.

The exported `ballForce_eq_some` is only the implication from forced success to original
success. The additional audit probe establishes the stronger identity `ballForce o = o` for
every option, using positivity of rational denominators. Thus forcing introduces no rejection.

## Exact handoff-to-Lean rounding comparison

The handoff's `P = 320`, rational magnitude, numerator/denominator `Nat.log2` exponent,
signed dyadic scale, two floors, compensated radius and ceiling match `BallRound.lean:40–77`.
The zero case gives exponent zero. The negative integer branch uses the reciprocal natural
power, exactly `2^k`. Multiplication and inverse have one final `ballRound`; addition, constants,
actions and characters have none. Exponential first rounds the Taylor ball and then rounds
each square, with no extra final rounding. The handoff writes range reduction with `timesQ`,
where Lean uses `CertBall.times`; `timesQ_eq` proves these rational values identical.
The documented relative/selective-rounding deviations from the writer's original fixed-grid,
every-slot brief are explicit and compatible with D39's containment requirement.

## Kernel evaluation structure

The evaluated `ballsRev` recursion is tail position in the operation count; it conses one new
slot, increments the counter and uses `revGet`, with one final list reverse in `ballsAux`.
There is no append-to-accumulator or proof-only `ballsSpec` in the evaluator. Each operand is
pattern-matched once and `ballForce` forces all three rational denominators at slot creation.
List lookup remains linear, so total lookup work can still be quadratic; the change removes
quadratic copying, not all quadratic work. The exponential squaring recursion has depth in the
halving count `s`, as before, rather than in program length. These observations support the
claimed removal of a program-length deferred-arithmetic chain, without claiming a universal
constant-depth or resource guarantee. No recursion/heartbeat override was used.

## Definition classification and declaration table

All names below are in `KAM.Certificate` unless otherwise qualified. No new abbreviations,
structures, instances, hypotheses, or frozen anchors occur. Every definition is exposed through
`@[expose] public section`. New definitions and changed definitions are classified below;
pre-existing untouched definitions keep their previous meaning.

| Node / file | Declaration | Verdict | Classification / reason |
|---|---|---|---|
| BallRound | `slpBallPrec` | PASS | Policy constant 320; no fallback. |
| BallRound | `ilog2Q` | PASS | Total approximate binary exponent using normalized rational num/den; zero maps to zero. |
| BallRound | `dyScale` | PASS | Total positive rational signed power of two, including negative integers. |
| BallRound | `dyDown` | PASS | Floor-grid map; rounding contract requires S > 0. At S = 0 totalized division returns zero, never used by ballRound. |
| BallRound | `dyUp` | PASS | Ceiling-grid map; contract requires S > 0. Nonpositive scales are outside its stated rounding contract. |
| BallRound | `dyScale_pos` | PASS | Strictly positive for every integer exponent. |
| BallRound | `dyDown_le` | PASS | Floor bound for every positive rational scale. |
| BallRound | `le_dyUp` | PASS | Ceiling bound for every positive rational scale. |
| BallRound | `ballRound` | PASS | Total outward relative-grid enclosure; empty negative-radius balls cause no unsoundness. |
| BallRound | `ballRound_mem_aux` | PASS | Containment for arbitrary positive scale and all input balls. |
| BallRound | `ballRound_mem` | PASS | Containment for all P and all balls; no exponent side condition. |
| BallRound | `plusQ` | PASS | Exact rational ball addition; equality to backend proved. |
| BallRound | `timesQ` | PASS | Exact rational ball product; equality to backend proved. |
| BallRound | `plusQ_eq` | PASS | Exact equality for every pair of rational balls. |
| BallRound | `timesQ_eq` | PASS | Exact equality for every pair of rational balls. |
| BallRound | `ballSqIter` | PASS | Rounded repeated squaring, structural recursion in s. |
| BallRound | `ballSqIter_mem` | PASS | Exponential enclosure after all rounded squares. |
| BallRound | `ballExp` | PASS | Guarded range-reduced exponential enclosure; none means guard failure. |
| BallRound | `ballExp_sound` | PASS | Successful rounded exponential encloses exp of every input member. |
| Ball | `cexpHalvings` | PASS | Existing header and body unchanged. |
| Ball | `certCExpSmall_reduced` | PASS | Existing header and body unchanged. |
| Ball | `certCExpReduced_cexpHalvings_isSome` | PASS | Existing header and body unchanged. |
| Ball | `ballPiLo` | PASS | Existing header and body unchanged. |
| Ball | `ballPiHi` | PASS | Existing header and body unchanged. |
| Ball | `ball_two_pi_zpow_mem` | PASS | Existing header and body unchanged. |
| Ball | `constBall` | PASS | Existing header and body unchanged. |
| Ball | `mem_constBall` | PASS | Existing header and body unchanged. |
| Ball | `inv_ball_bound` | PASS | Existing header and body unchanged. |
| Ball | `ballZero` | PASS | Existing header and body unchanged. |
| Ball | `ballOf` | PASS | Existing header and body unchanged. |
| Ball | `ballStepG` | PASS | Total guarded operation evaluator; parameterized precision and getter. |
| Ball | `ballForce` | PASS | Identity option transformation with evaluation-forcing positive denominator test. |
| Ball | `ballStep` | PASS WITH NOTES | Changed implementation; same curried type, named op presentation differs. |
| Ball | `revGet` | PASS | Reverse lookup, zero fallback out of k or actual list bounds; valid representation invariant proved. |
| Ball | `ballsRev` | PASS | Tail-recursive reverse-accumulator evaluator; k records logical slot count. |
| Ball | `ballsAux` | PASS WITH NOTES | Changed evaluator; same curried type, names previously anonymous accumulator/ops. |
| Ball | `Slp.balls` | PASS | Exact header and body retained; delegates to changed ballsAux. |
| Ball | `ballsSpec` | PASS | In-order rounded reference evaluator; proof object, not runtime slot path. |
| Ball | `revGet_reverse` | PASS | All-index lookup identity, including fallback. |
| Ball | `ballsRev_eq` | PASS | Reverse evaluator equals reversed reference output, including none. |
| Ball | `ballsAux_eq_spec` | PASS | Same in-order output as rounded reference. |
| Ball | `BallRel` | PASS | Existing header and body unchanged. |
| Ball | `toC_zero_rat` | PASS | Existing header and body unchanged. |
| Ball | `toC_ratCast` | PASS | Existing header and body unchanged. |
| Ball | `ballZero_mem` | PASS | Existing header and body unchanged. |
| Ball | `BallRel.ballRel_nil` | PASS | Existing header and body unchanged. |
| Ball | `BallRel.ballRel_snoc` | PASS | Existing header and body unchanged. |
| Ball | `ballForce_eq_some` | PASS WITH NOTES | Success implication only; audit also proves full identity. |
| Ball | `ballStepG_sound` | PASS | Enclosure from operand enclosures, checked weight, domain membership and successful step. |
| Ball | `ballStep_sound` | PASS | Exact existing theorem header retained; proof rebuilt through rounded reference. |
| Ball | `ballsSpec_sound` | PASS | Induction over in-order reference with BallRel. |
| Ball | `ballsAux_sound` | PASS | Exact existing theorem header retained; proof rebuilt through rounded reference. |
| Ball | `Slp.val_mem_ball` | PASS | Existing header and body unchanged. |
| Ball | `ballStep_inv_lt` | PASS | Successful inverse entails stored operand exclusion guard. |
| Ball | `ballsSpec_prefix_inv` | PASS | Preserves accumulator and all successful inverse guards. |
| Ball | `ballsAux_prefix_inv` | PASS | Exact existing theorem header retained; proof rebuilt through rounded reference. |
| Ball | `SlpInvGood` | PASS | Existing header and body unchanged. |
| Ball | `Slp.invGood_of_balls` | PASS | Existing header and body unchanged. |
| Ball | `jetSmoothOn_empty` | PASS | Existing header and body unchanged. |
| Ball | `slpMulO_prefix_self` | PASS | Existing header and body unchanged. |
| Ball | `slpInvPre_emit_prefix` | PASS | Existing header and body unchanged. |
| Ball | `slpInvNode_emit_prefix` | PASS | Existing header and body unchanged. |
| Ball | `HamExpr.nonvanishingOn_of_inv_good` | PASS | Existing header and body unchanged. |
| Ball | `HamExpr.nonvanishingOn_of_balls` | PASS | Existing header and body unchanged. |
| Hamiltonian consumer | `checkHamBounds_sound` | PASS | Entire Sound/Ham.lean unchanged; consumes rounded enclosure soundness. |
| Standard consumer | `checkTorusCertificate_sound` | PASS | Statement and source unchanged. |
| Sharp consumer | `KAM.CertificateSharp.checkTorusCertificateSharp_sound` | PASS | Statement and source unchanged. |

## Independent validation

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1`, using `nice -n 5`.
Builds used the prescribed gate, one target per invocation. No clean, package update, cache
fetch, generated-root repair, source repair, or git mutation was performed.

### Targeted build receipts

Command form (for each module, sequentially):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soballdyl MODULE
```

The gate invokes `nice -n 5 lake build MODULE`.
`KAM.Certificate.Expr.BallRound` and `KAM.Certificate.Expr.Ball`: exit 0;
output ends `Build completed successfully (2845 jobs).` and
`Build completed successfully (2951 jobs).`, respectively.
Remaining independent results:

```text
KAM.Certificate.Sound.Ham rc=0
KAM.Certificate.Soundness rc=0
KAM.CertificateSharp.Sound rc=0
KAM.Certificate.Tests.Ball rc=0
KAM.Certificate.Tests.ComplexExp rc=0
KAM.Certificate.Tests.Compose rc=0
KAM.Certificate.Tests.Defs rc=0
KAM.Certificate.Tests.Gram rc=0
KAM.Certificate.Tests.Model rc=0
KAM.Certificate.Tests.Negative rc=0
KAM.Certificate.Tests.Packed rc=0
KAM.Certificate.Tests.Positivity rc=0
KAM.Certificate.Tests.Rat rc=0
KAM.Certificate.Tests.RatData rc=0
KAM.Certificate.Tests.Torsion rc=0
KAM.Certificate.Tests.Toy2 rc=0
KAM.Certificate.Tests.Toy2Data rc=0
KAM.Certificate.Tests.Toy2d rc=0
KAM.Certificate.Tests.Toy2dData rc=0
KAM.Certificate.Tests.Toy3 rc=0
KAM.Certificate.Tests.Toy3Data rc=0
KAM.Certificate.Tests.ToyLit rc=0
KAM.Certificate.Tests.Witness rc=0
KAM.CertificateSharp.Tests.Margin rc=0
```

Every command ended in `Build completed successfully` (some dependency targets already
up to date). Existing unused-argument/simp warnings were replayed from dependencies and
unchanged consumers/tests; none was a compile error in either changed module. This includes
all 20 files under `Certificate/Tests`, all three toy certificate checks and their data modules,
and the only `CertificateSharp/Tests` module. `Tests/Ball` checks the rounded exponential and
cosine paths, successful division, and a denominator ball containing zero returning `none`.
`Tests/Toy2d` verifies the tiny reciprocal intermediate that failed the writer's fixed-grid
prototype, including `toyCert2d_hamBounds` and the complete passing-certificate result.

### Original-type, edge-case and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOBallAudit.lean
```

Final exit **0**, no errors. The probe imports `KAM.Certificate.Soundness` and
`KAM.CertificateSharp.Sound`, copies each of the **32** original declaration headers from
`git show inp:KAM/Certificate/Expr/Ball.lean` to an `example`, and supplies the corresponding
current declaration with all original explicit binders in order. Local `n`/phase notation is
restored for the original section-scoped declarations. This checks the old written types,
including the anonymous-arrow forms of `ballStep` and `ballsAux`; it does not establish
body equality to the old evaluator, which is deliberately false after rounding.

Additional successful proofs/computations:

```lean
example (o : Option (CC ℚ × ℚ)) : ballForce o = o := by
  cases o with
  | none => rfl
  | some b =>
    simp only [ballForce]
    have h : 0 < b.2.den + b.1.re.den + b.1.im.den := by
      have := b.2.den_pos
      omega
    simp [h]
example : dyScale (-3) = (1 / 8 : ℚ) := by decide +kernel
example : ilog2Q 0 = 0 := by decide +kernel
```

The same probe checks, by `decide +kernel`, each coordinate and radius of the zero ball at
precision 0, the exact real ball centred at `2^400`, and that centred at `1/2^400`, both at
precision 320. The huge case exercises negative `k`; the tiny case exercises a grid much
finer than `2^-320`. All pass. The first version of the audit harness had a header-extraction
error at a nested named argument `α := ℚ`, and tried to decide structure equality without a
`DecidableEq CC` instance. The harness was corrected to detect the top-level body separator
and compare rational projections; these were scratch-probe issues, not package failures.

`#print axioms` output for all **17 new public theorems**, the re-proved public interface,
and requested consumers:

```text
'KAM.Certificate.revGet_reverse' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.ballsRev_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballForce_eq_some' depends on axioms: [propext]
'KAM.Certificate.ballStepG_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsSpec_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStep_inv_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsSpec_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dyScale_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dyDown_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.le_dyUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballRound_mem_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballRound_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.plusQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.timesQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballSqIter_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballExp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.invGood_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkHamBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.checkTorusCertificateSharp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only `propext`, `Classical.choice`, and `Quot.sound` occur (some lemmas use subsets).
No `sorryAx` or extra assumption appears in the three requested soundness results.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.BallRound KAM.Certificate.Expr.Ball KAM.Certificate.Sound.Ham KAM.Certificate.Soundness KAM.CertificateSharp.Sound
```

One invocation, exit **0**. Complete output:

```text
replaying KAM.CertificateSharp.Sound
replaying KAM.Certificate.Soundness
replaying KAM.Certificate.Sound.Ham
replaying KAM.Certificate.Expr.Ball
replaying KAM.Certificate.Expr.BallRound
```

### Source and protected-path hygiene

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit **0** with empty output. Protected files are untouched. Changed-file scans find no
`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, forbidden ambient type, or resource-budget override.
Both changed files have the copyright/module/public imports/docstring/public section structure;
`wc -l` gives **658** (`Ball.lean`) and **188** (`BallRound.lean`), below 1500.


### Repository lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1478 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

The only failure is `KAM.lean is out of date`, explicitly allowed by the audit brief. There
are no scratch-module or forbidden-token failures in this checkout. Module structure,
frozen-anchor guard and all 158 elaborated ABI hashes pass. The generated root was left
untouched under rule 10. The handoff's older 144/146-anchor receipts are branch-specific;
158 is the independently verified count in this audit checkout.

## Errata, deviations, and handoff

No suspected defect in a pinned mathematical source, frozen definition, frozen statement,
or mathematical blueprint contract was found. The local documentation defects and the
D39-authorized replacement of the older design's exact exponential implementation are
located and quoted above. The writer's selective/relative-grid deviations remain explicitly
recorded, with no silent substitution in the mirror rule. The two changed source-header
presentations should be recorded if the orchestrator requires literal textual header identity;
this audit establishes type compatibility and does not claim those source strings are identical.

No claim is made about completion of the I/N/P theorem campaigns, final lunar certificate
acceptance, or a universal memory bound. The report is the only repository file edited by the
auditor; temporary probes and logs in `.lake/abi-scratch/` were removed after their results were
transcribed here. No source fixes, staging, commits, or generated-file changes were made.

Final validation: `git diff --check inp...HEAD` and protected-path comparison remain clean;
`git diff --no-index --check /dev/null /root/code/KAM-inp-soballdyl/docs/tracks/SO/audits/SO-BALLDY-audit-1.md`
emits no whitespace diagnostics (exit 1 because the new file differs from `/dev/null`).
`inp` and HEAD remained at the pins above throughout the audit.
