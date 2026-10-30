# SO-BALLFIX independent audit 1

**PASS WITH NOTES** for SO-BALLFIX under D39. The compatibility repair is sound, the sharp-v2
statements and definitions are preserved, and all independent targeted builds, original-type probes,
axiom checks and kernel replay pass. The only lint failure is the permitted stale generated root.
There is no frozen anchor or provider to seal in this package.

Audit date: 2026-10-30. Worktree: `/root/code/KAM-inp-soballfix`.
Snapshot: HEAD `ff7a031738e263202f20e4efc7544d98851f84cf`; comparison ref `inp` `003c5a3a04b09690bc03ab763b69e159641da2b4`;
merge base `7ffcd5283c21a1f3e34cdf38d6536be704036b71`. All locators below refer to this HEAD unless otherwise stated.
The independent auditor did not author the package and changed no source or git state.
The shared `inp` ref advanced during the audit from
`1283e0b62faa278f2f95162fea6c67b1577a3ee2` to the ref above. Its merge base and the
three-dot package diff stayed unchanged; a direct comparison of the three audited Lean paths
between those two inp revisions is empty. HEAD and all pinned source hashes remained stable.

| Anchor / consumer | Verdict | Scope |
|---|---|---|
| SO-BALLFIX / D39 implementation | PASS WITH NOTES | Two additive helper lemmas and two sharp-v2 proof repairs. |
| `KAM.Certificate.ballForce_some` | PASS | No premise; forcing preserves every rational ball. |
| `KAM.Certificate.ballStep_char` | PASS | Exact, unrounded character ball for every key and accumulator. |
| `KAM.CertificateSharp.stepT_sound` | PASS | Original type and definition context retained. |
| `KAM.CertificateSharp.ballsAuxT_prefix_inv` | PASS | Original type; uses the existing inverse-success characterization. |
| `checkHamBounds_sound` | PASS | Existing checker implication; allowed axioms only. |
| `checkTorusCertificate_sound` | PASS | Existing black-box result; no theorem scope enlarged. |
| `checkTorusCertificateSharp_sound` | PASS | Existing sharp result preserved. |
| `V2.checkTorusCertificateV2_sound` | PASS | Existing engine-parametric result preserved. |
| Frozen-anchor sealing | N/A | No frozen theorem proved or changed here. |

## Authority, scope and method

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` (in particular D39), the requested
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the SO-BALLFIX handoff including all five
AUDIT FOCUS items, the BALLDY handoff/audit, and the applicable SO design amendment. Track I's
statement conventions and the frozen strip, vector-field and invariance-error definitions were
checked for the consumer interface. No SO `statement.md` exists; this implementation's controlling
source is D39 plus `docs/tracks/SO/design/SO-LEAN-DESIGN.md`, not an I/N/P blueprint theorem.
No frozen-anchor correspondence or campaign closure is asserted.

This is a focused tier-2, refute-first audit: snapshot and diff inventory, independent statement/body
review, adversarial checks of the suspected semantic changes, then mechanical verification. The
user already authorized report/scratch edits and targeted checks; the user's exact worktree report
path overrides the generic brief's main-worktree destination. No additional approval was needed.
Only this report is created outside `.lake/abi-scratch/`; temporary Lean probes were deleted after
recording their results. No subagents, source repairs, commits, root regeneration or network use.

The full `git diff inp...HEAD` contains three Lean files plus the two BALLDY reports, the BALLFIX
handoff and the SO design amendment. The inherited BALLDY changes were reviewed in addition to
the immediate BALLFIX delta. Findings distinguish these scopes:

- `git diff 22f20b9c HEAD -- KAM/Certificate/Expr/Ball.lean`: exactly 16 additions, zero removals;
  the only additions are the two documented helpers.
- `git diff 86089b36 HEAD -- KAM/CertificateSharp`: only `Ham/BallsTrig.lean`, two added and three
  removed proof lines. Same result against current `main` during this audit. All headers,
  definition bodies and docstrings are unchanged. This follows from the complete diff, not merely
  a matching declaration-name census.
- `BallRound.lean` is identical to `22f20b9c`; no BALLFIX definition changes.
- All pre-existing Ball theorem source headers remain identical to `inp`. Two inherited definition
  headers name formerly anonymous arguments (`ballStep`, `ballsAux`); their curried types remain
  equal. All Ball headers are unchanged relative to `22f20b9c`.

### Frozen input hashes

| File | SHA-256 |
|---|---|
| `KAM/Certificate/Expr/Ball.lean` | `7adf31cb14a18c948b3849295f61e489e57a74ae0834179c102c3d24cf0cb521` |
| `KAM/Certificate/Expr/BallRound.lean` | `b5b5edbaa7a397d16e5e891fb964c0b9167c4c1072a529d3d099c27e9ca09576` |
| `KAM/CertificateSharp/Ham/BallsTrig.lean` | `a89cea902b4c303910ce0d84dbb9e3f04c0525af7195a6561e8034c986010bc0` |
| `docs/tracks/SO/audits/SO-BALLFIX-handoff.md` | `20e95015a85022c8d8b75f7a99fd40b2b9572941a8621cd83ec447d08837d0f2` |

## Statement and proof review

`ballForce_some` uses positivity of the radius denominator. Since rational denominators are positive
and the two other denominator summands are naturals, the failure branch is impossible. A separate
probe proves the stronger identity `ballForce o = o` for every option, including `none`.

`ballStep_char` unfolds only the wrapper and generic step, then applies that identity. In the
character branch `ballStepG` returns exactly `(0, WH.w ^ sum |k|)`; it does not call `ballRound`.
No weight-validity, dimensionality, sign, accumulator-validity or nonempty-key premise is needed.
The repaired `stepT_sound` supplies this exact equation to its existing `plain` function, which
applies the proved `ballStep_sound`. Thus the theorem does not assume its own enclosure.

For the inverse proof, `ballStep_inv_lt hr` extracts the test on the stored, original operand
before inverse rounding. Its accumulator is exactly `acc.map Prod.fst`. The unchanged prefix
argument transfers that operand to the final list. If the index is out of range, `ballZero` would
force `0 < 0`; the original contradiction excludes this case. This preserves the nonvanishing
contract, including malformed references, with no extra premise or circular use.

The inherited rounding proof uses downward centre bounds, the complex triangle inequality and an
upward radius bound. Its containment theorem holds for every precision and input ball; a negative
radius has no members. No accuracy assumption about `ilog2Q` is needed for containment. `ballExp`
keeps the reduction guard and Taylor enclosure and applies containment after the initial Taylor
ball and every squaring. `plusQ_eq` and `timesQ_eq` identify the specialized rational operations
with the old backend. Reverse lookup, accumulator equivalence and the soundness induction cover
arbitrary initial accumulators, out-of-range reads, empty programs, `some` and `none`; they compare
the new rounded step with its reference pass, not with the old exact evaluator.

### Binder classification of the two BALLFIX exports

No logical hypotheses, typeclass premises, existential constants or new assumptions occur.
Each data binder is listed below. Counts: SOURCE=0, STANDING=0, TYPING=8, RULED=0, EXCESS=0.
D39 authorizes the implementation; it is not a theorem premise.

| Export | Binder | Bin | Meaning / authority |
|---|---|---|---|
| `ballForce_some` | `b : CC ℚ × ℚ` | TYPING | Entire rational-ball carrier of `ballForce`. |
| `ballStep_char` | `{n : ℕ}` | TYPING | Dimension of the existing evaluator. |
| `ballStep_char` | `{WH : CertWeight}` | TYPING | Existing weight data, no validity assumed. |
| `ballStep_char` | `{centre : List ℚ}` | TYPING | Existing centre data. |
| `ballStep_char` | `{radius : List ℚ}` | TYPING | Existing radius data. |
| `ballStep_char` | `{taylorN : ℕ}` | TYPING | Existing Taylor-order data. |
| `ballStep_char` | `acc : List (CC ℚ × ℚ)` | TYPING | Arbitrary operand accumulator. |
| `ballStep_char` | `k : CertKey` | TYPING | Arbitrary character key. |

### Declaration ledger

`C` means `KAM.Certificate`; `S` means `KAM.CertificateSharp`. Inherited rows are included
because they occur in the required three-dot comparison. These are implementation lemmas under
D39, not replacements for source-facing frozen anchors.

| Node / provenance | Declaration | Verdict | Reason |
|---|---|---|---|
| BALLDY inherited | `C.slpBallPrec` | PASS | Literal 320-bit policy, independent of runtime data. |
| BALLDY inherited | `C.ilog2Q` | PASS | Literal binary numerator/denominator exponent estimate. |
| BALLDY inherited | `C.dyScale` | PASS | Positive power of two for every integer exponent. |
| BALLDY inherited | `C.dyDown` | PASS | Literal floor-grid operation; inequalities require positive scale. |
| BALLDY inherited | `C.dyUp` | PASS | Literal ceiling-grid operation; inequalities require positive scale. |
| BALLDY inherited | `C.dyScale_pos` | PASS | All integer exponents; no extra hypothesis. |
| BALLDY inherited | `C.dyDown_le` | PASS | Only the defining positive-scale premise. |
| BALLDY inherited | `C.le_dyUp` | PASS | Only the defining positive-scale premise. |
| BALLDY inherited | `C.ballRound` | PASS | Outward dyadic centre/radius formula on the whole carrier. |
| BALLDY inherited | `C.ballRound_mem_aux` | PASS | Positive-scale enclosure, all centres and radii. |
| BALLDY inherited | `C.ballRound_mem` | PASS | All precisions; no hidden magnitude premise. |
| BALLDY inherited | `C.plusQ` | PASS | Literal exact rational sum backend. |
| BALLDY inherited | `C.timesQ` | PASS | Literal exact rational product backend. |
| BALLDY inherited | `C.plusQ_eq` | PASS | Equality to CertBall.plus, no side conditions. |
| BALLDY inherited | `C.timesQ_eq` | PASS | Equality to CertBall.times, no side conditions. |
| BALLDY inherited | `C.ballSqIter` | PASS | Rounded square iteration; zero case is the input. |
| BALLDY inherited | `C.ballSqIter_mem` | PASS | Induction proves every rounded squaring enclosure. |
| BALLDY inherited | `C.ballExp` | PASS | Guarded reduction, initial rounding and rounded squarings. |
| BALLDY inherited | `C.ballExp_sound` | PASS | Only successful call and input membership; all orders/counts. |
| BALLDY inherited | `C.ballStepG` | PASS | Generic operand lookup; rounded mul/inv/exp, other branches exact. |
| BALLDY inherited | `C.ballForce` | PASS | Semantically identity on Option; denominator test cannot reject some. |
| BALLDY inherited | `C.revGet` | PASS | Reverse lookup with existing zero semantics outside range. |
| BALLDY inherited | `C.ballsRev` | PASS | Cons accumulator with explicit length; tail-recursive operations. |
| BALLDY inherited | `C.ballsSpec` | PASS | In-order reference of the same rounded step. |
| BALLDY inherited | `C.revGet_reverse` | PASS | All indices, including missing operands. |
| BALLDY inherited | `C.ballsRev_eq` | PASS | Arbitrary starting accumulators; Option reverse equality. |
| BALLDY inherited | `C.ballsAux_eq_spec` | PASS | Full success/failure equality with reference pass. |
| BALLDY inherited | `C.ballForce_eq_some` | PASS | Forced success implies the same original result. |
| BALLFIX | `C.ballForce_some` | PASS | BALLFIX: total forcing identity, no hypothesis. |
| BALLFIX | `C.ballStep_char` | PASS | BALLFIX: exact unrounded character equation. |
| BALLDY inherited | `C.ballStepG_sound` | PASS | Operand enclosure is an inductive invariant, supplied by BallRel. |
| BALLDY inherited | `C.ballsSpec_sound` | PASS | Reference induction discharges all step invariants. |
| BALLDY inherited | `C.ballStep_inv_lt` | PASS | Successful rounded inverse retains the original strict exclusion. |
| BALLDY inherited | `C.ballsSpec_prefix_inv` | PASS | Reference prefix and inverse-exclusion invariant. |
| BALLDY reimplementation | `C.ballStep` | PASS | Existing curried type, guarded rounded implementation. |
| BALLDY reimplementation | `C.ballsAux` | PASS | Existing curried type; reverse-cons implementation equals reference. |
| BALLDY reimplementation | `C.ballStep_sound` | PASS | Original type; applies generic enclosure proof. |
| BALLDY reimplementation | `C.ballsAux_sound` | PASS | Original type; transfers reference soundness. |
| BALLDY reimplementation | `C.ballsAux_prefix_inv` | PASS | Original type; transfers reference exclusion. |
| sharp-v2 compatibility | `S.stepT_sound` | PASS | Only char proof repaired; original statement and stepT body. |
| sharp-v2 compatibility | `S.ballsAuxT_prefix_inv` | PASS | Only inverse proof repaired; original statement and ballsAuxT body. |
| sharp-v2 compatibility | `S.ballsAuxT_sound` | PASS | Unchanged propagation of ball and shape invariants. |
| sharp-v2 compatibility | `S.val_mem_ballsTrig` | PASS | Unchanged slot enclosure. |
| sharp-v2 compatibility | `S.norm_val_le_slotMagQ_trig` | PASS | Unchanged magnitude conclusion. |
| sharp-v2 compatibility | `S.invGood_of_ballsTrig` | PASS | Unchanged denominator nonvanishing. |
| sharp-v2 compatibility | `S.nonvanishingOn_of_ballsTrig` | PASS | Unchanged Hamiltonian nonvanishing wrapper. |

### Definition classification

There are no new or changed BALLFIX definitions, abbreviations, structures or inductives.
Inherited new definitions are literal computational objects: `slpBallPrec`, `ilog2Q`, `dyScale`,
`dyDown`, `dyUp`, `ballRound`, `plusQ`, `timesQ`, `ballSqIter`, `ballExp`, `ballStepG`,
`ballForce`, `revGet`, `ballsRev`, `ballsSpec`. The changed definitions `ballStep` and
`ballsAux` use the new implementation; `Slp.balls` retains its literal wrapper and calls the changed
`ballsAux`. No new choice-defined object or deferred characterization is involved.

The zero/default cases agree with the existing SLP semantics (missing action/operand indices),
not an invented valid-locus fallback. `revGet` is characterized for the invariant `k = length`
used by callers. `dyDown`/`dyUp` at a nonpositive scale remain their literal rational formulas;
all uses requiring rounding inequalities supply `dyScale_pos`. Negative-radius balls contain
no points. None of these total cases is used to manufacture an enclosure.

BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL;
CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS.
The explicit reference-equivalence and enclosure theorems are proved, not deferred.

## AUDIT FOCUS: evaluator routing and mirror correction

| Checker / consumer | Exact source | Evaluator | Rounded ball operations | Reverse-cons accumulator |
|---|---|---|---|---|
| `checkHamBounds`, `V2.landedBase` | `Certificate/Defs.lean:237-240`, `V2/Engine.lean:101-110` | `Slp.balls` | mul/inv/exp | Yes |
| `V2.checkHamClaim`, `V2.refinedTest` | `V2/HamClaim.lean:42`, `V2/RouteARefinedEngine.lean:34-36` | `Slp.balls` | mul/inv/exp | Yes |
| `checkHamBoundsSplit` | `Ham/SplitBounds.lean:178` | `Slp.balls` | mul/inv/exp | Yes |
| `checkHamBoundsTrig` | `Ham/SplitBounds.lean:164` | `ballsTrig` | Delegated ball operations only | No |
| `checkHamBoundsTrigSplit` | `Ham/SplitBounds.lean:171` | `ballsTrig` | Delegated ball operations only | No |

`V2/BaseTrig.lean` and `Ham/TrigCertifier.lean` select the cosh route. `V2/HamTrig.lean:28-36`
converts its split bounds to `HamFacts`. `Ham/TrigBound.lean` provides scalar bounds, not a
separate evaluator.

**Confirmed existing performance limitation, not a proof defect:** `BallsTrig.lean:91-96` still
uses `acc ++ [b]`; `stepT` repeatedly builds `acc.map Prod.fst` (lines 71,77,82,85,88).
`mulShape` stores the exact product `u * tbMag y` (lines 47-51); same-key addition stores
`u + v` (line 78); opposite-key addition returns the unrounded `trigRad` (line 80).
Consequently the cosh pass inherits outward rounding only through calls to `ballStep`; it does
not inherit the reverse-cons storage or a rounding/forcing policy for shape scalars. The
countercheck was to trace every stepT branch rather than infer its implementation from its
imports. All these definitions are unchanged by BALLFIX. No lunar cosh performance was measured;
this audit does not claim D39's performance goal is complete for that route.

The mirror claim was independently recomputed from stored JSON, using the actual
`toy_arith.py` at commit `26d9b34c` (hash below). Seven toys compare with `XC.out`;
the lunar operations/meta come from `XL.out`, but its balls must come from **`XL2.out`**.
The call uses `slp_balls(n, parse_ops(ops), Fraction(w), list(map(Fraction,c)),
list(map(Fraction,r)), N)` with N from toy meta and N=30 for lunar. Rational triples are
converted to Python Fractions before equality. Results:

```text
T2d 156 IDENTICAL
E1 3 IDENTICAL
E2 46 IDENTICAL
E3 39 IDENTICAL
D1 25 IDENTICAL
D0 25 IDENTICAL
S1 42 IDENTICAL
L final XL2 887 IDENTICAL
L stale XL DIFFER
```

D0's equality is the expected `none` rejection. This is an independent Python comparison against
stored Lean dumps, not a fresh Lean `#eval`, benchmark, universal equivalence theorem or lunar
certificate acceptance. `XL2.lean` imports the final Ball evaluator and evaluates `.balls` at
line 894; it contains no resource override. Its stored output provenance remains external to this
worktree. BALLFIX changes no evaluator body, so there is no new value-level divergence to attach.

External evidence directory: `/mnt/HC_Volume_106379410/kam-data/so-data3/step1-xc/`.

| Evidence | SHA-256 |
|---|---|
| `XL2.lean` | `0b9ac5945e78c3b01f6f47afc9f3ddf86d916f017a888827d5eca4612e5c690a` |
| `XL2.out` | `3c1c3fdc8a3b5b4de75add7175d048ea21713805a83a18b3603d4f1778d3588f` |
| `XC.out` | `49cba956cb4a6f724a7c070f77d02702064a05afb2e122e13a3da6b08e9732ae` |
| `XL.out` (stale balls) | `fe745169a175f1fda9075365e0a061574f343b3862705858d2c349597a980f5a` |
| `26d9b34c:scripts/spin_orbit/toy_arith.py` | `eda4338ec1252ace5b018178d927921ecb17f684f1e9d97bedaad35a28e997b3` |

**Reproduction note:** the stored `mine.py:5` still selects `('XL.out', 30)` and therefore does
not by itself reproduce the corrected lunar match. Its loop must read lunar balls from `XL2.out`
while retaining XL's operations/meta, as above. This small stale-script issue survives the
countercheck: the final dump matches, the old dump differs, and the script literally selects the
old dump. No edit was made to the external script. The handoff's explicit correction is accurate;
its reference to `mine.py` needs this qualification.

## Verification evidence

Every audit-owned Lean/Lake invocation was serialized with `LEAN_NUM_THREADS=1` and nice level 5;
no clean/cache/update, heartbeat, recursion-depth or synthesis-budget override was used.
Builds used the required compile gate. The 44 receipts below are independent audit runs, not copied
from the handoff. They are warm targeted builds, not claims of a clean rebuild or performance test.

```sh
export LEAN_NUM_THREADS=1
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-soballfix MODULE
# repeated sequentially, one MODULE per invocation; gate invokes nice -n 5 lake build
```

```text
KAM.Certificate.Expr.BallRound: rc=0; Build completed successfully (2845 jobs).
KAM.Certificate.Expr.Ball: rc=0; Build completed successfully (2951 jobs).
KAM.CertificateSharp.Ham.BallsTrig: rc=0; Build completed successfully (3255 jobs).
KAM.CertificateSharp.Ham.SplitBounds: rc=0; Build completed successfully (3256 jobs).
KAM.CertificateSharp.Ham.TrigCertifier: rc=0; Build completed successfully (3324 jobs).
KAM.CertificateSharp.V2.BaseTrig: rc=0; Build completed successfully (3368 jobs).
KAM.CertificateSharp.V2.HamTrig: rc=0; Build completed successfully (3401 jobs).
KAM.CertificateSharp.V2.Engine: rc=0; Build completed successfully (3364 jobs).
KAM.CertificateSharp.V2.RouteARefinedEngine: rc=0; Build completed successfully (3506 jobs).
KAM.Certificate.Soundness: rc=0; Build completed successfully (3319 jobs).
KAM.CertificateSharp.Sound: rc=0; Build completed successfully (3363 jobs).
KAM.Certificate.Tests.Ball: rc=0; Build completed successfully (2952 jobs).
KAM.Certificate.Tests.ComplexExp: rc=0; Build completed successfully (2845 jobs).
KAM.Certificate.Tests.Compose: rc=0; Build completed successfully (2962 jobs).
KAM.Certificate.Tests.Defs: rc=0; Build completed successfully (3252 jobs).
KAM.Certificate.Tests.Gram: rc=0; Build completed successfully (2963 jobs).
KAM.Certificate.Tests.Model: rc=0; Build completed successfully (2916 jobs).
KAM.Certificate.Tests.Negative: rc=0; Build completed successfully (3252 jobs).
KAM.Certificate.Tests.Packed: rc=0; Build completed successfully (2915 jobs).
KAM.Certificate.Tests.Positivity: rc=0; Build completed successfully (2917 jobs).
KAM.Certificate.Tests.Rat: rc=0; Build completed successfully (3254 jobs).
KAM.Certificate.Tests.RatData: rc=0; Build completed successfully (3253 jobs).
KAM.Certificate.Tests.Torsion: rc=0; Build completed successfully (2985 jobs).
KAM.Certificate.Tests.Toy2: rc=0; Build completed successfully (3326 jobs).
KAM.Certificate.Tests.Toy2Data: rc=0; Build completed successfully (3253 jobs).
KAM.Certificate.Tests.Toy2d: rc=0; Build completed successfully (3328 jobs).
KAM.Certificate.Tests.Toy2dData: rc=0; Build completed successfully (3253 jobs).
KAM.Certificate.Tests.Toy3: rc=0; Build completed successfully (3323 jobs).
KAM.Certificate.Tests.Toy3Data: rc=0; Build completed successfully (3253 jobs).
KAM.Certificate.Tests.ToyLit: rc=0; Build completed successfully (3252 jobs).
KAM.Certificate.Tests.Witness: rc=0; Build completed successfully (2920 jobs).
KAM.CertificateSharp.Tests.BallsTrig: rc=0; Build completed successfully (3335 jobs).
KAM.CertificateSharp.Tests.Corner: rc=0; Build completed successfully (3379 jobs).
KAM.CertificateSharp.Tests.Frame: rc=0; Build completed successfully (3381 jobs).
KAM.CertificateSharp.Tests.FreqTests: rc=0; Build completed successfully (3175 jobs).
KAM.CertificateSharp.Tests.Margin: rc=0; Build completed successfully (3348 jobs).
KAM.CertificateSharp.Tests.Shared: rc=0; Build completed successfully (3335 jobs).
KAM.CertificateSharp.Tests.Step0Coh: rc=0; Build completed successfully (3277 jobs).
KAM.CertificateSharp.V2.Tests.FrameFacts: rc=0; Build completed successfully (3515 jobs).
KAM.CertificateSharp.V2.Tests.Frozen: rc=0; Build completed successfully (3426 jobs).
KAM.CertificateSharp.V2.Tests.Refined: rc=0; Build completed successfully (3510 jobs).
KAM.CertificateSharp.V2.Tests.RefinedR1: rc=0; Build completed successfully (3505 jobs).
KAM.CertificateSharp.V2.Tests.TrigCombined: rc=0; Build completed successfully (3516 jobs).
KAM.CertificateSharp.V2.Tests.TrigFacts: rc=0; Build completed successfully (3409 jobs).
```

Dependency warnings are replayed in the build logs (PiHigh, Expr.Basic, Sound.Static,
Sound.Ham, Corner.SupBound and other unchanged dependencies). No diagnostic is attributed to
BallRound, Ball or BallsTrig themselves. No package source error was suppressed.

### Original types and exact consumption probes

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/soballfix-old-types.lean
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/soballfix-ball.lean
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/soballfix-trig.lean
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/soballfix-route.lean
```

All four final invocations exit 0. The first has 52 examples reconstructed from `inp` source
headers: 50 explicit source-header applications plus the two equation-style definition types
`ballStep` and `ballsAux`. It includes all pre-existing Ball and BallsTrig theorem types, and
retains each explicit binder application in order. The helper probe checks the two new helpers at
the independently written exact types and proves `ballForce o = o`. Initial scratch generation
used an implicit `Ph` abbreviation where the original file has a local notation, producing an
unresolved dimension in one scratch header; matching the original notation fixed the probe.
This was a probe error; no package edit or theorem weakening occurred.

There is no provider/frozen equality or seal-body probe: this package has no such declaration.
The existing compiled sharp proofs are the actual term-level consumers of the new helpers.

### Axioms

The probes run `#print axioms` for **every theorem in all three changed modules** and the five
listed checker consumers (60 declarations total). Exact output follows; every set is a subset of
`[propext, Classical.choice, Quot.sound]` and none contains `sorryAx` or a project axiom.

```text
'KAM.Certificate.dyScale_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dyDown_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.le_dyUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballRound_mem_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballRound_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.plusQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.timesQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballSqIter_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballExp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpSmall_reduced' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpReduced_cexpHalvings_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ball_two_pi_zpow_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.mem_constBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.inv_ball_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.revGet_reverse' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.ballsRev_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toC_zero_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toC_ratCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballZero_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.BallRel.ballRel_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.BallRel.ballRel_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballForce_eq_some' depends on axioms: [propext]
'KAM.Certificate.ballForce_some' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.ballStep_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStepG_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsSpec_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStep_inv_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsSpec_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.invGood_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetSmoothOn_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpMulO_prefix_self' depends on axioms: [propext]
'KAM.Certificate.slpInvPre_emit_prefix' depends on axioms: [propext]
'KAM.Certificate.slpInvNode_emit_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_inv_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkHamBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.checkTorusCertificateSharp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.mulShape_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.TRel.nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.TRel.length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.tb_fst_getD' depends on axioms: [propext, Quot.sound]
'KAM.CertificateSharp.getD_append_lt' depends on axioms: [propext]
'KAM.CertificateSharp.getD_append_ge' depends on axioms: [propext]
'KAM.CertificateSharp.TRel.snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.trig_add_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.stepT_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.ballsAuxT_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.val_mem_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.norm_val_le_slotMagQ_trig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.ballsAuxT_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.invGood_of_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.nonvanishingOn_of_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.checkTorusCertificateV2_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.checkHamClaim_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 /usr/bin/time -f 'wall=%e peak_kb=%M exit=%x' \
  nice -n 5 lake env leanchecker --verbose \
  KAM.Certificate.Expr.BallRound KAM.Certificate.Expr.Ball \
  KAM.CertificateSharp.Ham.BallsTrig KAM.CertificateSharp.V2.Engine \
  KAM.CertificateSharp.V2.RouteARefinedEngine
```

```text
replaying KAM.CertificateSharp.V2.RouteARefinedEngine
replaying KAM.CertificateSharp.V2.Engine
replaying KAM.CertificateSharp.Ham.BallsTrig
replaying KAM.Certificate.Expr.Ball
replaying KAM.Certificate.Expr.BallRound
wall=59.56 peak_kb=3108404 exit=0
```

### Lint, imports and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Certificate.lean)
check_lean_modules: PASS (1628 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

Lint exits 1 solely for the expressly permitted stale root (the missing BallRound import in
`KAM/Root/Certificate.lean`). It is already absent at `22f20b9c`; BALLFIX did not touch the root.
The auditor did not regenerate it. Module checks, frozen-anchor guard and ABI hashes pass.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md
git diff --check inp...HEAD
git diff --check
```

All three commands exit 0 with no output. Source scans find no forbidden proof escapes or
resource overrides in the three changed modules. Their total lengths are BallRound=190,
Ball=674, BallsTrig=408, below 1500 even counting all comments and blank lines. They all have
copyright, `module`, public imports, module docstrings and `@[expose] public section`.
The unchanged short-name collisions `TRel.nil`, `TRel.length`, `TRel.snoc` are outside the
compatibility repair; no new conflicting short name was observed in the two added helpers.

A recursive source-import walk from V2.RouteARefinedEngine, V2.Engine, V2.BaseTrig and V2.HamTrig
contains 267 KAM modules, no providers and 23 frozen modules, all definitions. No frozen theorem
or DRAFT_SORRY anchor is imported through this closure. Thus no imported frozen-theorem state
needs an exception. Lint independently validates the global quarantine and manifest invariants.

## Findings, source defects and closeout

No mathematical blocker or suspected pinned-source erratum was found. The observed notes are:

1. **Permitted hygiene:** stale generated root, to regenerate on landing. Confirmed independently
   by lint and the protected-path diff. This is the sole lint failure.
2. **Existing performance scope:** cosh-pass append/map storage and unrounded shape scalars.
   Confirmed by branch-level source tracing, with no new BALLFIX definition changes. A later
   optimization needs its own proof and measurements. Do not transfer disc-pass performance
   receipts to this evaluator.
3. **External reproduction script:** `mine.py` still reads stale lunar balls from XL.out.
   The handoff's corrected final-dump claim passes the independent comparison; the script path
   needs the explicit XL2-ball substitution recorded above.
4. **Inherited presentation:** two BALLDY definition headers name formerly anonymous binders.
   All original types elaborate; SO-BALLFIX itself changes no existing header. The earlier
   BallRound comment corrections and design amendment are present. Some older design rows still
   name `certCExpReduced`, but the controlling D39 amendment at lines 79-85 explicitly supersedes
   them with `ballExp`; no contradiction in the operative contract was found.

The adversarial pass tried to invalidate character exactness under rounding, introduce a possible
forcing rejection, lose inverse exclusion through rounding, transfer the wrong accumulator, treat
cosh storage as optimized, and use the stale mirror dump. Exact consumption and identity probes
refute the first four; source tracing and the two dump comparisons retain the last two as scoped
notes. This review did not independently regenerate XL2.out, benchmark the lunar cosh pass,
certify the lunar data, or audit all I/N/P frozen theorems. No larger closure follows.

Closeout: all requested AUDIT FOCUS items addressed; all changed and inherited new declarations
classified; all 44 targeted builds pass; 52 original-type examples and the helper probes pass;
60 axiom sets allowed; kernel replay exits 0; lint has only its permitted exception; protected
paths unchanged. No source deviation introduced by this audit. Final result: **PASS WITH NOTES**.
