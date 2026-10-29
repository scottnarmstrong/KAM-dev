# SO-EXPW independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-soexpw`.
Audited HEAD: `b56865ab1ddc25b10bc22ca5f985d0b05c508f11`.
Compared branch: `inp` at `943bf98e0e5ae15c5d2a3b8b2c06218c808a2fb4`, using `git diff inp...HEAD`.

## Verdict

**PASS WITH NOTES for the SO-EXPW signed contracts.** All eight signed declarations are present with their exact fully qualified names and statement surfaces. The four signed theorems independently elaborate against copied signature statements, using the exact explicit binders in order. All 48 new public theorems have only `[propext, Classical.choice, Quot.sound]`; kernel replay succeeds. Arbitrary certificate data cannot bypass the pin, residual, or reciprocal bounds.

There are no frozen theorem anchors or provider exports in this slice, hence no anchor to seal here. This verdict covers the four requested modules only, not tracks I/N/P or a lunar certificate. The generic package brief is specialized by the handoff's SO focus. The eight signed interfaces and their success-conditional guarantees are complete; literal algorithm conformance to the design has the documented exceptions D1-D3 below. No claim of unconditional checker success, production precision readiness, or full consumer integration is made.

| Signed node | Declaration under `KAM.Certificate` | Verdict | Note |
|---|---|---|---|
| SO-EXPW witness data | `ExpWitness` | PASS | Three fields match byte-for-byte. |
| SO-EXPW pin construction | `expPinBall` | PASS | Exact signed type and intended coefficient ball. |
| SO-EXPW pin soundness | `expPinBall_sound` | PASS | Exact type and explicit-binder replay. |
| SO-EXPW exponential radius | `expWitnessRadius` | PASS WITH NOTES | Exact type; D1 changes real-bound implementation. |
| F10 pin contract | `expWitnessRadius_pin` | PASS | Exact type; no smallness premise. |
| SO-EXPW exponential soundness | `expWitness_sound` | PASS | Exact type for every witness and enclosed function. |
| SO-EXPW reciprocal radius | `invWitnessRadius` | PASS WITH NOTES | Exact type; D3 limits success availability. |
| O2 reciprocal soundness | `invWitness_sound` | PASS | Exact type, nonvanishing and inverse enclosure both retained. |

## Authority and diff review

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the requested `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/SO/audits/SO-EXPW-handoff.md`, especially AUDIT FOCUS. Compared the slice with `/root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md` Revision 7, the §1.7/F10 design and §7 package row, and `/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §C (structure at 576, through inverse theorem at 619). The worktree has no SO statement.md or SO blueprint directory; the handoff explicitly names these design/signature authorities instead. Unrelated I/N/P theorem anchors are outside this SO-only audit.

The complete three-dot diff consists of four new Lean files (1301 lines) and the 200-line handoff. Inspected all new module bodies and the handoff, rather than just the final commit. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has empty output. Initial working tree was clean. The only transitive frozen dependency is `KAM/Frozen/Defs/ComplexStrip.lean`, read directly and manifest state verified **SEALED** (`KAM.complexStrip`). A source import-closure scan visits 35 KAM modules and finds no provider and no frozen theorem, hence no DRAFT_SORRY import.

## Proof and error-budget review

For the exponential, the polynomial is genuinely periodic and differentiable. The helper uses `F = E exp(-g0)`, computes its derivative, bounds the Pi-sup operator norm by the sum of basis values, translates an arbitrary strip point by integers, and applies the convex-strip mean value inequality. This pays `exp(B)^2 * (epsilon0 + (1/2+rho) sum rj)`. The model-tail term is bounded by `exp(B)*(exp(eta)-1)`. Neither gf holomorphy nor a witness-quality estimate is silently assumed; the tail estimate is pointwise from the enclosure. Positive strip width and nonnegative radius follow from existing premises, including at n=0.

Pin input coefficient rounding is paid by `coeffSumBall`; `certCExpReduced_sound` pays reduction, Taylor and repeated ball-squaring errors; `expPinErr` pays E's coefficient-sum rounding and final subtraction. `expWitnessRadius_pin` extracts the exact successful reduced call. An independent general probe proves that any reduced-pin `none` forces radius `none`.

The fused residual pays the E derivative's error terms, merging error, checked product error, derivative-of-g rounding times the E weighted bound, and upward 2pi scaling. Missing or invalid product advice uses a sound direct product. The conditional helper premises are independently discharged in `expWitnessRadiusOf_sound`, then its pin premise is discharged in the signed wrapper. They are not hidden hypotheses of `expWitness_sound`.

For the reciprocal, `u` encloses `Q*(2pi)^(-d)*bf`, including b's original tail and all multiplication/truncation errors. The constant-key subtraction and weighted remainder pay delta on the whole carrier. Successful delta<1 forces u and bf nonzero. The proved reciprocal upper bound and identity `bf^-1-(2pi)^(-d)Q=(2pi)^(-d) Q(1-u)/u` pay the final enclosure with degree `-b.deg`, for every integer degree. No lower bound is supplied by the certificate as a trusted premise.

## Design deviations and suspected defects

**D1 — Real exponential implementation differs from the accepted design (note, no soundness failure).** Design lines 138-140 and F10 row 149 say the real route is "unchanged" and the factors "stay on `ratExpUp`"; §1.7 line 246 repeats this, as do signature comments at 567-569. Actual `ExpBounds.lean:211` and `Exp.lean:94` use backend `expm1Up`, with `exp(2B)` formed from a rounded square. This rejects when N=0 or the rounded halved input exceeds one, instead of using a coarse rational fallback. Its bound is proved from the lawful backend and Mathlib's Taylor estimate, so no exported theorem is weakened. The generic backend has no law-free alpha-to-rational conversion, supporting the implementation motivation. Reconcile the design text and generator parameter selection before asserting literal design conformity. Even a nominal halving count at a threshold must account for upward rounding.

**D2 — Residual pipeline and advice keys (note).** The implementation fuses the residual without cutoff and directly multiplies when advice is absent or invalid, rather than the design's model-operation/crude fallback route. The full residual bound is independently proved. Keys `[1,j]` and `[2]` contain no witness identifier. Distinct witnesses sharing an advice book can select unsuitable advice; existing checks and fallback preserve soundness, but precision/performance can deteriorate. Consumer integration must arrange per-witness advice or reconcile the key scheme. No consumer code was audited and no signed argument was added.

**D3 — Reciprocal rejection limitation; handoff explanation is too narrow (independently refuted).** Handoff lines 174-177 says additional failure occurs when delta is "so close to `1`" that the rounded iterates stay above 1/2, approximately delta >= 1-2^-64. Upward rounding can instead stagnate far below one. On the lawful `CertFixed 2` backend, delta=3/4 has mantissa 3, passes delta<1, but `upMul delta delta` rounds 9/16 upward to 3/4. Thus `recipOneSubUp delta = none` after fuel exhaustion. All three facts were checked by fresh `decide +kernel` probes. This corrects the handoff's explanation and limits completeness over the full carrier; it does not refute `recipOneSubUp_ge` or either signed success-conditional theorem. Production delta being tiny is an application fact not proved here. `Inv.lean:62` and the signature's inverse-radius docstring should be read as one rejection condition, not an iff characterization.

Minor representation qualification: `isZeroKey` tests all stored entries. A nonzero entry beyond n is ignored by evaluation but prevents classification as a zero key. `oneSubSupUp` remains conservative, though its numerical radius need not be invariant under such representation changes. The handoff's "does not depend on how the keys are represented" should be understood as soundness for every representation, not equal bounds.

No suspected defect in a pinned mathematical source, frozen definition, or signed theorem statement was found. D1-D3 are implementation/design documentation discrepancies; no repository repair was made by the auditor.

## Declaration-by-declaration review and definition classification

Every name below is prefixed by `KAM.Certificate.`. Each row gives its exact source locator. All new definitions/structures are listed and classified; there are no new abbrevs, instances, classes, or inductives. Helper statements without a separate signed blueprint node were checked as support for §1.7, not represented as additional frozen exports. Their local premises are explicit and appropriately discharged by callers. Test data are concrete fixtures, not mathematical source assumptions.

| Node/file | Declaration and line | Kind | Verdict | Classification or fidelity note |
|---|---|---|---|---|
| §1.7 helper, `ExpBounds.lean` | `CertBall.sumPairs`:35 | def | PASS | Structural adjacent-pair ball addition; odd tail retained. |
| §1.7 helper, `ExpBounds.lean` | `CertBall.sumRounds`:40 | def | PASS | Structural fixed-count iteration, preserving the accumulated enclosure. |
| §1.7 helper, `ExpBounds.lean` | `CertBall.foldSum`:45 | def | PASS | Structural exact-zero/singleton/right-fold final reduction. |
| §1.7 helper, `ExpBounds.lean` | `CertBall.listSum`:51 | def | PASS | 64 balancing rounds followed by fold; no dropped terms. |
| §1.7 helper, `ExpBounds.lean` | `CertPoly.coeffSumBall`:55 | def | PASS | All coefficients summed as exact-radius-zero balls; evaluates at zero for every n. |
| §1.7 helper, `ExpBounds.lean` | `CC.negC`:59 | def | PASS | Exact componentwise backend negation under the arithmetic laws. |
| §1.7 helper, `ExpBounds.lean` | `CertPoly.negP`:62 | def | PASS | Termwise exact negation; keys and terms retained. |
| §1.7 helper, `ExpBounds.lean` | `ballCentreSum`:66 | def | PASS | Complex sum of interpreted ball centres on the whole list carrier. |
| §1.7 helper, `ExpBounds.lean` | `ballRadSum`:69 | def | PASS | Real sum of interpreted radii; arbitrary signed inputs allowed in algebraic helper. |
| §1.7 helper, `ExpBounds.lean` | `CC.toC_negC`:73 | theorem | PASS | Exact interpretation of backend negation. |
| §1.7 helper, `ExpBounds.lean` | `CertBall.plus_spec`:76 | theorem | PASS | Addition rounding paid in radius; does not require nonnegative input radii. |
| §1.7 helper, `ExpBounds.lean` | `CertBall.sumPairs_spec`:97 | theorem | PASS | Enclosure loss bounded by radius increase for one pairing round. |
| §1.7 helper, `ExpBounds.lean` | `CertBall.sumRounds_spec`:115 | theorem | PASS | Iterated pairing accounting by triangle inequality. |
| §1.7 helper, `ExpBounds.lean` | `CertBall.foldSum_spec`:128 | theorem | PASS | Final fold accounting, including empty and singleton cases. |
| §1.7 helper, `ExpBounds.lean` | `CertBall.mem_listSum`:148 | theorem | PASS | Conditional enclosure helper from source list membership, not an assumed exported conclusion. |
| §1.7 helper, `ExpBounds.lean` | `character_zero_point`:159 | theorem | PASS | Every Fourier character is one at zero. |
| §1.7 helper, `ExpBounds.lean` | `CertPoly.mem_coeffSumBall`:162 | theorem | PASS | All polynomial coefficient sum error paid; no key normalization premise. |
| §1.7 helper, `ExpBounds.lean` | `CertPoly.eval_negP`:172 | theorem | PASS | Polynomial negation evaluated exactly for every n and theta. |
| §1.7 helper, `ExpBounds.lean` | `CertModel.mul_deg`:181 | theorem | PASS | Both multiplication branches preserve the signed sum of degrees. |
| §1.7 helper, `ExpBounds.lean` | `expRemFactor`:195 | def | PASS | Rational Taylor factor; at M=0 totalized division gives zero, but every proof use is at M>=1. |
| §1.7 helper, `ExpBounds.lean` | `expSeriesUp`:199 | def | PASS | Fuelled upward Taylor sum and remainder; intended bound requires its stated nonnegative domination premises. |
| §1.7 helper, `ExpBounds.lean` | `expm1SqIter`:206 | def | PASS | Structural upward z*(2+z) squaring recurrence. |
| §1.7 helper, `ExpBounds.lean` | `expm1Up`:211 | def | PASS WITH NOTES | Sound backend bound on the stated nonnegative domain; rejects N=0 or failed rounded range check (D1). |
| §1.7 helper, `ExpBounds.lean` | `expSeriesUp_ge`:219 | theorem | PASS | Upward series bound under explicit nonnegative dominated real input and power accumulator. |
| §1.7 helper, `ExpBounds.lean` | `expm1SqIter_ge`:266 | theorem | PASS | Upward recurrence dominates exact repeated squaring for nonnegative lower input. |
| §1.7 helper, `ExpBounds.lean` | `expm1Up_sound`:283 | theorem | PASS | Real exponential minus one bounded whenever the guard succeeds; no trusted conversion. |
| §1.7 signed, `Exp.lean` | `ExpWitness`:47 | structure | PASS | Exactly the three signed data fields; contains no proof, accuracy assumption, or trusted property. |
| §1.7 signed, `Exp.lean` | `expPinBall`:58 | def | PASS | Signed type exact; returns balanced coefficient-sum centre and radius. |
| §1.7 helper, `Exp.lean` | `expPinErr`:63 | def | PASS | Pays E(0) sum rounding, negated output radius, subtraction rounding and centre norm. |
| §1.7 helper, `Exp.lean` | `expResidualProduct`:69 | def | PASS | Checked product at [1,j]; direct full product on missing/invalid advice (D2). |
| §1.7 helper, `Exp.lean` | `expResidualUp`:81 | def | PASS | Fused term/error weighted sum plus product radius and derivative-rounding cross term, scaled by upper 2pi. |
| §1.7 helper, `Exp.lean` | `expWitnessRadiusOf`:91 | def | PASS WITH NOTES | Analytic radius with upward operations; real bounds use expm1Up (D1). |
| §1.7 signed, `Exp.lean` | `expWitnessRadius`:108 | def | PASS WITH NOTES | Signed type exact; reduced pin checked first; any pin failure returns none. |
| §1.7 signed, `Exp.lean` | `expPinBall_sound`:114 | theorem | PASS | Exact signed statement; coefficient ball encloses g.poly.eval n 0. |
| §1.7 signed, `Exp.lean` | `expWitnessRadius_pin`:124 | theorem | PASS | Exact signed statement; extracts successful reduced call and its unconditional enclosure. |
| §1.7 helper, `Exp.lean` | `norm_sub_le_expPinErr`:140 | theorem | PASS | Conditional pin-ball helper; main export obtains its premise from certCExpReduced_sound. |
| §1.7 helper, `Exp.lean` | `CertPoly.fderiv_eval_single`:159 | theorem | PASS | Exact directional Fourier derivative with period-one factor 2pi. |
| §1.7 helper, `Exp.lean` | `norm_errTermsEval_add_le`:169 | theorem | PASS | One weighted pass pays both value norm and coefficient error. |
| §1.7 helper, `Exp.lean` | `norm_le_expResidualUp`:192 | theorem | PASS | Pays derivative of E, derivative of g, merge, product, cross and 2pi errors. |
| §1.7 helper, `Exp.lean` | `norm_clm_le_sum_single`:271 | theorem | PASS | Operator norm bound in the intended Pi sup norm, valid also at n=0. |
| §1.7 helper, `Exp.lean` | `norm_exp_sub_one_le_exp_norm`:286 | theorem | PASS | Mathlib complex exponential remainder at Taylor length one. |
| §1.7 helper, `Exp.lean` | `exists_int_translate`:290 | theorem | PASS | Integer translation reduces real parts; sup norm <=1/2+rho on the full strip. |
| §1.7 helper, `Exp.lean` | `norm_exp_sub_witness_le`:307 | theorem | PASS | Explicit conditional analytic helper; periodic integrating factor and convex-strip mean value bound. |
| §1.7 helper, `Exp.lean` | `expWitnessRadiusOf_sound`:378 | theorem | PASS | Pin premise is distinct helper input, discharged by the signed wrapper; all radius terms paid. |
| §1.7 signed, `Exp.lean` | `expWitness_sound`:474 | theorem | PASS | Exact signed statement; arbitrary E, gf and lawful backend; no accuracy premise beyond checked success. |
| §1.7 helper, `Inv.lean` | `isZeroKey`:37 | def | PASS | All stored key entries zero, including empty keys; sufficient, not necessary, for dimension-specific zero mode. |
| §1.7 helper, `Inv.lean` | `oneSubSupUp`:42 | def | PASS | Constant-key ball subtraction plus all other weighted terms plus model radius; conservative for malformed keys. |
| §1.7 helper, `Inv.lean` | `recipBoundAux`:49 | def | PASS | Fuelled upper reciprocal bound, only on successful return with the stated domination hypotheses. |
| §1.7 helper, `Inv.lean` | `recipOneSubUp`:56 | def | PASS WITH NOTES | 64-step fuelled helper; may fail through rounded stagnation even at delta=3/4 (D3). |
| §1.7 signed, `Inv.lean` | `invWitnessRadius`:63 | def | PASS WITH NOTES | Signed type exact; product, delta<1 and reciprocal-helper success required; extra failure possible (D3). |
| §1.7 helper, `Inv.lean` | `certKeyFun_eq_zero_of_isZeroKey`:77 | theorem | PASS | Stored all-zero key implies zero on every Fin n; implication only. |
| §1.7 helper, `Inv.lean` | `CertPoly.eval_filter_add`:91 | theorem | PASS | Exact partition of all terms by an arbitrary Boolean filter. |
| §1.7 helper, `Inv.lean` | `CertPoly.eval_zeroKeys`:105 | theorem | PASS | All-zero stored keys evaluate constantly, independent of n. |
| §1.7 helper, `Inv.lean` | `norm_one_sub_le_oneSubSupUp`:119 | theorem | PASS | Triangle/weighted bound for every enclosed degree-zero function. |
| §1.7 helper, `Inv.lean` | `recipBoundAux_ge`:161 | theorem | PASS | Induction proves upper reciprocal accumulator on successful return. |
| §1.7 helper, `Inv.lean` | `recipOneSubUp_ge`:202 | theorem | PASS | Specialization proves 1/(1-delta) bound; no success/completeness assertion. |
| §1.7 signed, `Inv.lean` | `invWitness_sound`:207 | theorem | PASS | Exact signed statement; all b degrees, arbitrary Q and bf; proves nonvanishing and correctly scaled inverse. |
| §J test, `Witness.lean` | `witnessTestW`:39 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTest_weight`:41 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTestQ`:44 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTestCfg`:46 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTest_expm1Up`:51 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_expm1Up_fail`:56 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_recip`:58 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_recip_fail`:61 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTestG`:66 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTestE`:69 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTest_exp`:75 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_exp_bad`:80 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTestG3`:86 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTest_pin_fail`:88 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_pin_reduced`:93 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_real_fail`:99 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTestB`:107 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTestInv`:110 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTest_inv`:116 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_inv_exact`:121 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_inv_fail`:126 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTestBessel`:133 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTestFix`:138 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTestCfgFix`:141 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTestGFix`:145 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTestRange`:150 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTestEFix`:153 | def | PASS | Concrete test fixture/finite data generator; every coefficient and parameter is checked as data. |
| §J test, `Witness.lean` | `witnessTest_exp_fixed`:158 | theorem | PASS | Kernel-decided Boolean/equality control; fresh source elaboration and kernel replay pass. |
| §J test, `Witness.lean` | `witnessTest_exp_encloses`:167 | theorem | PASS | Explicit instance of the signed soundness contract; no stronger consumer claim. |
| §J test, `Witness.lean` | `witnessTest_inv_encloses`:176 | theorem | PASS | Explicit instance of the signed soundness contract; no stronger consumer claim. |

## Independent validation receipts

All Lean/Lake commands and the lint command use `LEAN_NUM_THREADS=1 nice -n 5`; commands ran sequentially, with no overlap. Builds used the requested compile gate. No resource override, clean, update, cache fetch, package edit, or state-changing git command was used.

### Targeted compile gate — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soexpw KAM.Certificate.Model.ExpBounds KAM.Certificate.Model.Exp KAM.Certificate.Model.Inv KAM.Certificate.Tests.Witness
```

```text
[inp-gate] slot 1 acquired 19:18:42 for KAM.Certificate.Model.ExpBounds KAM.Certificate.Model.Exp KAM.Certificate.Model.Inv KAM.Certificate.Tests.Witness
⚠ [2839/2891] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one

Hint: Omit it from the simp argument list.
  [apply] simp [div_eq_mul_inv]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (2919 jobs).
```

This is a fresh gate invocation replaying existing artifacts; it is not a claim that every module was recompiled from scratch. The imported dependency warning is outside the slice.

### Exact signatures, explicit binder bodies, and axioms — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOEXPWAudit.lean
```

The probe copies all seven def/theorem headers directly from the authoritative signature file, checks whitespace-normalized header equality against production, and checks the ExpWitness structure byte-for-byte. It declares fresh names under `KAM.Certificate`, aliases all three definitions with their exact explicit arguments, and elaborates the four theorem bodies:

```lean
by exact KAM.Certificate.expPinBall_sound n g
by exact KAM.Certificate.expWitnessRadius_pin hE
by exact KAM.Certificate.expWitness_sound hW cfg hg hdeg hE
by exact KAM.Certificate.invWitness_sound hW cfg hb hQ
```

For each of the seven declarations it also elaborates `example : type_of% @KAM.Certificate.<name> := @audit_sig_<name>`. The signature file itself is never imported (its draft sorry bodies are irrelevant). The probe initially omitted `open CertArith`; correcting that auditor-only namespace omission produced an exit-0 run with no warning/error. All 48 requested `#print axioms` outputs from the successful run follow:

```text
'KAM.Certificate.CC.toC_negC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.plus_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.sumPairs_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.sumRounds_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.foldSum_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mem_listSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.character_zero_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.mem_coeffSumBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_negP' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.mul_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expSeriesUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expm1SqIter_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expm1Up_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expPinBall_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expWitnessRadius_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_sub_le_expPinErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.fderiv_eval_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_errTermsEval_add_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_le_expResidualUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_clm_le_sum_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_exp_sub_one_le_exp_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.exists_int_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_exp_sub_witness_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expWitnessRadiusOf_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.expWitness_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certKeyFun_eq_zero_of_isZeroKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_filter_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_zeroKeys' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_one_sub_le_oneSubSupUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.recipBoundAux_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.recipOneSubUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.invWitness_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_expm1Up' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_expm1Up_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_recip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_recip_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_exp_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_pin_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_pin_reduced' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_real_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_inv_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_inv_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_exp_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_exp_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.witnessTest_inv_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Model.ExpBounds KAM.Certificate.Model.Exp KAM.Certificate.Model.Inv KAM.Certificate.Tests.Witness
```

```text
replaying KAM.Certificate.Tests.Witness
replaying KAM.Certificate.Model.Inv
replaying KAM.Certificate.Model.Exp
replaying KAM.Certificate.Model.ExpBounds
```

### Fresh test-source elaboration and independent controls — both exit 0, empty output

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOEXPWTests.lean
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOEXPWControls.lean
```

The first probe is an exact scratch copy of `Tests/Witness.lean`, re-elaborating its bodies, including all `decide +kernel` proofs and both contract instances. Positive controls cover rational scalar bounds, the exp and inverse toys, large-pin reduction, exact reciprocal degree 3, and the 289-term fixed-point witness. False controls cover inadequate pin/real halvings, an inaccurate exp witness, delta=1 and Q=0. The bad exp witness is correctly allowed a large radius rather than arbitrarily rejected.

The second probe contains:

```lean
import KAM.Certificate.Model.Inv
import KAM.Certificate.Model.Exp
import KAM.Certificate.Arith.Fixed
open KAM.Certificate CertArith
example : blt (⟨3⟩ : CertFixed 2) (ofInt 1) = true := by decide +kernel
example : recipOneSubUp (⟨3⟩ : CertFixed 2) = none := by decide +kernel
example : (upMul (⟨3⟩ : CertFixed 2) ⟨3⟩).m = 3 := by decide +kernel
example {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (g : CertModel α) (E : ExpWitness α)
    (h : certCExpReduced (expPinBall g).1 (expPinBall g).2 E.pinHalvings E.pinOrder = none) :
    expWitnessRadius n W cfg g E = none := by simp [expWitnessRadius, h]
```

### Hygiene

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-soexpw KAM.Certificate.Model.ExpBounds KAM.Certificate.Model.Exp KAM.Certificate.Model.Inv KAM.Certificate.Tests.Witness
```

Exit 0, exact output: `short-name check OK (no reused public short name)`. Checker includes dotted final components against KAM/Mathlib, with the documented exemption for signed names. No root namespace declaration/shadow was introduced; all declarations live in `KAM.Certificate` and its intended nested namespaces.

A direct Python source scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `ofReduceBool`, `EuclideanSpace` or resource override in the four modules. Module headers, public imports, docstrings and public sections are present; production definitions are in `@[expose] public noncomputable section`. Tests are ordinary public definitions. Length/maximum Unicode line width: ExpBounds 330/97, Exp 487/99, Inv 300/100, Witness 184/100. The sole local option is `Inv.lean:61`, `set_option linter.unusedVariables false in`; it suppresses a linter for the signed dimension parameter n, whose unused status is explained immediately above. It changes neither proof resources nor kernel trust.

Lint receipt and final report-only integrity follow below.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with exactly this output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1350 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole lint failure is the generated-root exception explicitly allowed by the audit brief. Module checks, frozen-anchor guard and all 144 ABI hashes pass. `KAM.lean` was not regenerated or edited.

Final integrity commands:

```sh
git diff --exit-code
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff inp...HEAD --check
git diff --check
git status --short
```

The four diff commands exit 0 with empty output. Final status contains only the new report:

```text
?? docs/tracks/SO/audits/SO-EXPW-audit-1.md
```

All auditor-created scratch probes, copies and logs were removed after their receipts were embedded here. No tracked source was changed, and no git state was modified. The report is deliberately in this worktree at the user's exact absolute path, overriding the generic brief's main-worktree destination. No timing forecast from the prover was independently benchmarked; no large production certificate or SO-EMB consumer was tested.
