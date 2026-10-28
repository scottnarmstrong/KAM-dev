# Independent T4 package audit 1

Overall verdict: **PASS WITH NOTES** (N1 comparison/root hygiene, N2 dependency provenance).
Both required T4 theorem exports and both exact definitions PASS. No frozen theorem is sealed.
Date: 2026-10-28.

## Scope and pinned authority

This report audits only `KAM/Planetary/PlanarTorsion/PairCoefficients.lean` and
`PairCoefficients/{Vanish,Series,Laplace}.lean` in `/root/code/KAM-inp-p11c-t4`.
HEAD: `98de073fd2693ce1ee88c71128d2e14589c4ba6d`.
Comparison ref observed: `inp=d9183adae208ecf2e726620694b69c8168e33006`.
`git diff inp...HEAD` warns of multiple merge bases and selects
`f82deaf1e9ac7d32d79f857a9b69287a68705b98`. All four scoped files are additions in that diff.
OrbitJet is a T2 dependency, inspected only for the meaning of `p11c_JetEq` and import hygiene;
its proof package is not certified here. No provider or frozen theorem is delivered by T4.
Thus frozen-provider equality and a frozen seal-body probe are not applicable.

Read: AGENTS.md, PLAN, DECISIONS, the package audit brief, T4-handoff including AUDIT FOCUS,
P11C design sections 2–4 and 7 (including its proof instructions), the prior design audit,
track-P statement, and blueprint-P/parts/p11b-planar-torsion.tex L64–98.
The user's exact worktree report destination overrides the generic brief's main-worktree wording.
The lean-statement-audit skill supplies the refute-first binder/body checks; these are
infrastructure declarations, not manifest-bound theorem anchors.

Pinned input SHA-256:

| Input | SHA-256 |
|---|---|
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| `docs/tracks/P/design/P11C-LEAN-DESIGN.md` | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |
| `blueprint-P/parts/p11b-planar-torsion.tex` | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |

## Required surface and completeness

Whitespace-stripped source comparisons give `True` for both complete definition commands
and both complete theorem headers against the pinned signatures. A fresh Lean probe additionally
copies both signature definitions under new names and checks their equality by `rfl`, and
copies both exact theorem statements with bodies `by exact pair_series` and
`by exact pair_quadratic_consistency a ha`.

| Required declaration | Verdict | Scope |
|---|---|---|
| `p11c_pairCoeffs` | PASS | Exact definition, signature L350–365; all A,B,p1,…,p6 formulas. |
| `p11c_pairSeriesJet` | PASS | Exact definition, signature L697–705. |
| `pair_series` | PASS | Exact signature L707–710; analytic signed interval and actual derivatives. |
| `pair_quadratic_consistency` | PASS | Exact signature L712–714; only source premise 0<a<1. |

T4's design row L202 is complete. The shared pair-jet proposition is only partly assigned to T4:
its rational formulas, alpha-series (pj-red's final sentences, blueprint L96), and the two
quadratic identities (pj-cons L97) are delivered. Actual averaging/Kepler jet identification,
formal inverse-radius expansion, averaging rule, cancellation of other monomials and attachment
to the physical interaction remain T5 (`pair_jet`); physical quartic conversion is T6.
No T4 theorem claims those remaining steps. The design's T2/T5 proof instructions are respected:
the alpha receipt is actual iterated Frechet derivative equality, not an assumed CAS expansion.

Main-statement expanded binder test (SOURCE=1, STANDING=0, TYPING=1, RULED=0, EXCESS=0):

| Theorem | Binder | Bin | Authority |
|---|---|---|---|
| `pair_series` | none (no implicit or instance binders) | — | Exact closed conjunction, signature L707–710. |
| `pair_quadratic_consistency` | `(a : ℝ)` | TYPING |
| `pair_quadratic_consistency` | `(ha : a ∈ Ioo (0 : ℝ) 1)` | SOURCE |

`p11c_JetEq k f g` (OrbitJet/Analytic L49–51) expands to
`∀ j ≤ k, iteratedFDeriv ℝ j f 0 = iteratedFDeriv ℝ j g 0`.
Consequently the first jet includes orders 0 through 6 and the B jet includes 0 through 7.
It contains no assumption field. All helper premises are explicit in their separately named
conditional lemmas; the two required theorems supply them in their proofs.

## Declaration-by-declaration review

All names below have prefix `KAM.Planetary.`. P=PairCoefficients.lean,
L=PairCoefficients/Laplace.lean, S=PairCoefficients/Series.lean,
V=PairCoefficients/Vanish.lean. Each helper implements the local argument of
blueprint L96–97 or the elementary analytic/divisibility infrastructure used there.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| pj-red / pj-cons; P:33 | `p11c_pairCoeffs` (def) | PASS | Exact eight rational formulas, same order and normalization as signature L350–365 and blueprint L71–78. |
| pj-red / pj-cons; P:52 | `p11c_pairSeriesJet` (def) | PASS | Exact polynomial jet, including B through degree 7; signature L697–705, blueprint L84–89. |
| pj-red / pj-cons; P:65 | `p11cN0` (def) | PASS | Literal polynomial numerator table for b0; reconstruction proved by p11c_pairCoeffs_apply. |
| pj-red / pj-cons; P:73 | `p11cN1` (def) | PASS | Literal polynomial numerator table for b1; reconstruction proved by p11c_pairCoeffs_apply. |
| pj-red / pj-cons; P:83 | `p11cDn` (def) | PASS | Literal denominator table 4D²,2D²,64D⁴,64D⁴,32D⁴,16D⁴,16D⁴,16D⁴. |
| pj-red / pj-cons; P:89 | `p11cOrd` (def) | PASS | Literal sufficient vanishing orders [8,8,8,8,8,8,7,7]; no assertion of exact multiplicity. |
| pj-red / pj-cons; P:92 | `p11cQuot` (def) | PASS | Explicit polynomial factor, verified by p11c_pair_identity at every real a, including 0. |
| pj-red / pj-cons; P:109 | `p11c_pairCoeffs_apply` (theorem) | PASS | All-real componentwise reconstruction; fin_cases, simp, ring. |
| pj-red / pj-cons; P:114 | `p11c_laplace_half_zero` (theorem) | PASS | k=0 specialization of the full signed-interval bridge. |
| pj-red / pj-cons; P:117 | `p11c_laplace_half_one` (theorem) | PASS | k=1 specialization of the full signed-interval bridge. |
| pj-red / pj-cons; P:120 | `p11cDn_ne` (theorem) | PASS | |a|<1 implies 1-a²>0; every denominator nonzero. |
| pj-red / pj-cons; P:125 | `p11cOrd_le` (theorem) | PASS | Finite table check of sufficient order ≤8. |
| pj-red / pj-cons; P:127 | `p11cOrd_ge` (theorem) | PASS | Finite table check of sufficient order ≥7. |
| pj-red / pj-cons; P:129 | `p11c_pair_identity` (theorem) | PASS | Exact all-real polynomial identity for each of eight components; ring. |
| pj-red / pj-cons; P:137 | `p11cN0_analyticAt` (theorem) | PASS | Polynomial analytic everywhere, checked by finite cases and fun_prop. |
| pj-red / pj-cons; P:140 | `p11cN1_analyticAt` (theorem) | PASS | Polynomial analytic everywhere, checked by finite cases and fun_prop. |
| pj-red / pj-cons; P:143 | `p11cDn_analyticAt` (theorem) | PASS | Polynomial analytic everywhere, checked by finite cases and fun_prop. |
| pj-red / pj-cons; P:146 | `p11cQuot_analyticAt` (theorem) | PASS | Polynomial analytic everywhere, checked by finite cases and fun_prop. |
| pj-red / pj-cons; P:149 | `p11c_pairSeriesJet_analyticAt` (theorem) | PASS | Polynomial analytic everywhere, checked by finite cases and fun_prop. |
| pj-red / pj-cons; P:153 | `p11c_abs_lt_one_nhds` (theorem) | PASS | Openness of |a|<1 supplies the actual local equality domain. |
| pj-red / pj-cons; P:156 | `p11c_comp_analyticAt` (theorem) | PASS | Integral-to-series equality locally, then analytic quotient with denominator guard. |
| pj-red / pj-cons; P:167 | `p11c_comp_vanishes` (theorem) | PASS | Explicit analytic factor (Quot+a^(8-Ord)(N0 tail0+N1 tail1))/Dn, locally exact. |
| pj-red / pj-cons; P:187 | `p11c_iteratedFDeriv_eq_of_vanishes_real` (theorem) | PASS | Scalar conversion from iterated derivatives to multilinear Frechet derivatives. |
| pj-red / pj-cons; P:196 | `pair_series` (theorem) | PASS | Exact conjunction: analytic on (-1,1), vector JetEq 6, B JetEq 7; no premises. |
| pj-red / pj-cons; P:215 | `pair_quadratic_consistency` (theorem) | PASS | Exact two identities for 0<a<1; applies laplace_up at s=1/2, then field_simp/ring. |
| pj-red / pj-cons; L:26 | `p11cHalf` (def) | PASS | Literal a^k times halfCoef series at a²; equality to actual integral proved for |a|<1. |
| pj-red / pj-cons; L:28 | `p11cHalf_good` (theorem) | PASS | Part-8 halfCoef bound implies P11cGood; no assumed tail convergence. |
| pj-red / pj-cons; L:31 | `p11c_laplace_neg` (theorem) | PASS | π translation of 2π-periodic integral; cos(k(t+π))=(-1)^k cos(kt). |
| pj-red / pj-cons; L:58 | `p11c_laplace_half_nonneg` (theorem) | PASS | Normalized Part-8 integral bridge, rpow_neg, HasSum_laplaceTerm and laplaceTerm_half; includes a=0. |
| pj-red / pj-cons; L:74 | `p11c_laplace_half` (theorem) | PASS | Extends nonnegative bridge to negative a by parity and (-a)²=a². |
| pj-red / pj-cons; L:86 | `p11cHalf_analyticAt` (theorem) | PASS | Series analytic at a² and analytic composition for |a|<1. |
| pj-red / pj-cons; L:93 | `p11cHead` (def) | PASS | Literal four-term polynomial head in a², multiplied by a^k. |
| pj-red / pj-cons; L:97 | `p11cTail` (def) | PASS | Literal shifted series with q+4, multiplied by a^k; analytic on (-1,1). |
| pj-red / pj-cons; L:100 | `p11cHalf_eq_head_add` (theorem) | PASS | Exact split at q=4 gives a^8 times analytic shifted tail. |
| pj-red / pj-cons; L:107 | `p11cTail_analyticAt` (theorem) | PASS | Shifted P11cGood plus composition, on the entire signed interval. |
| pj-red / pj-cons; L:113 | `pcoef_half_values` (theorem) | PASS | Finite exact Pochhammer/factorial computation, norm_num. |
| pj-red / pj-cons; L:120 | `p11cHead_zero` (theorem) | PASS | Explicit b0 head through a^6, checked by ring. |
| pj-red / pj-cons; L:127 | `p11cHead_one` (theorem) | PASS | Explicit b1 head through a^7, checked by ring. |
| pj-red / pj-cons; S:23 | `p11cSeries` (def) | PASS | Literal real tsum; convergence proved at every point subsequently used. |
| pj-red / pj-cons; S:26 | `P11cGood` (def) | PASS | Literal absolute-summability predicate for all 0≤r<1; established for halfCoef. |
| pj-red / pj-cons; S:29 | `P11cGood.of_bound` (theorem) | PASS | Absolute coefficient bound ≤1 gives summability by geometric domination. |
| pj-red / pj-cons; S:36 | `P11cGood.shift` (theorem) | PASS | Shift summability; handles r=0 separately, with no division by zero. |
| pj-red / pj-cons; S:50 | `P11cGood.summable` (theorem) | PASS | Absolute-value summability on |x|<1. |
| pj-red / pj-cons; S:55 | `P11cGood.hasFPowerSeriesOnBall` (theorem) | PASS | Radius ≥1 and actual HasSum for ofScalars series; no formal-only inference. |
| pj-red / pj-cons; S:69 | `P11cGood.analyticAt` (theorem) | PASS | Analyticity at each point of the open unit ball. |
| pj-red / pj-cons; S:74 | `P11cGood.split` (theorem) | PASS | Exact finite head plus x^N times shifted tail, using established summability. |
| pj-red / pj-cons; V:24 | `p11cVanishes` (def) | PASS | Literal local analytic divisibility predicate, not an assumed series result. |
| pj-red / pj-cons; V:27 | `p11cVanishes.mono` (theorem) | PASS | Local conditional helper: multiply analytic factor by a^(m-n). |
| pj-red / pj-cons; V:33 | `p11cVanishes.add` (theorem) | PASS | Local conditional helper: add analytic factors. |
| pj-red / pj-cons; V:40 | `p11cVanishes.mul_left` (theorem) | PASS | Local conditional helper: multiply analytic factors. |
| pj-red / pj-cons; V:45 | `p11cVanishes_pow_mul` (theorem) | PASS | Direct witness for local analytic divisibility. |
| pj-red / pj-cons; V:49 | `p11c_iteratedDeriv_pow_mul` (theorem) | PASS | Induction via product derivative, eventual equality and j<m. |
| pj-red / pj-cons; V:70 | `p11c_iteratedDeriv_eq_of_vanishes` (theorem) | PASS | Differentiate f-g locally; analytic regularity supplies subtraction rule. |
| pj-red / pj-cons; V:81 | `p11c_iteratedFDeriv_eq_of_vanishes` (theorem) | PASS | Coordinate projections and ext_ring recover the entire Pi-valued Frechet derivative. |

## Definitions and proof reconstruction

All 13 new definitions are literal formulas or explicit local analytic predicates.
For each definition in the declaration table:
`BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL;
CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS`.
There are no new abbrevs, structures, instances, choice-selected objects or fallback branches.

The real total rational definition has the exact signature's total-division convention;
regularity is asserted only on (-1,1), where every denominator is proved nonzero.
The series definitions use Lean's total `tsum`; every use requiring convergence is accompanied
by `P11cGood.summable` or the Part-8 HasSum theorem. No conclusion relies on a divergent-sum value.
`p11cVanishes` and `P11cGood` are local helper predicates whose required instances are proved,
not input assumptions of `pair_series`.
`p11cQuot` denotes a polynomial factor in an exact divisibility identity, including a=0;
it is not a total pointwise division by a power of a at zero.

The proof was reconstructed as follows:

1. Part-8 `halfCoef k q = pcoef (1/2) (q+k) * pcoef (1/2) q` has absolute value ≤1.
   Geometric domination proves P11cGood; shifted coefficients retain it, including r=0.
   The actual FormalMultilinearSeries radius is at least 1 and its sum is the exported series.
2. L58–72 identifies the normalized integral at 0≤a<1 with the Part-8 series, retaining
   `(2*pi)^(-1)` and the un-doubled cosine coefficient. L31–56 proves parity using periodic
   translation by pi. L74–84 therefore establishes the same identification on **all** |a|<1,
   including negative a and a=0. Analyticity uses composition at a², not a positive-only germ.
3. L100–111 splits at q=4, obtaining `b_k=head_k+a^8 tail_k`; the tail is analytic at every
   |a|<1. For k=1 its additional factor a is retained. No division by a is used in the split.
4. P129–134 proves `N0*head0+N1*head1-Dn*jet=a^Ord*Quot` for every real a, component by
   component with ring. The polynomial tables are actual terms; no CAS certificate is assumed.
5. P167–185 constructs the analytic factor explicitly. The exponent `8-Ord` is legitimate
   because `Ord≤8`. The nonzero Dn lemma guards all quotient steps. Orders are at least 8
   for components 0–5, and at least 7 for 6–7. These imply the vector jet through 6 and,
   separately, the component-1 jet through 7. V49–99 proves the derivative consequences,
   including the Pi-valued multilinear equality, rather than equating only function values.
6. P215–235 specializes the proved T3 laplace_up recurrence at s=1/2, uses its k=1 formula,
   and closes the two consistency identities by field_simp/ring. Guards 0<a<1 give both
   a≠0 and 1-a²≠0; none is introduced as an extra theorem premise.

## Findings, hygiene and limits

N1 (comparison-scope note): the required
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
only KAM.lean changes, adding seven inherited public imports. The diff on
`KAM/Frozen manifest README.md` is empty. The multiple-merge-base warning selects
f82deaf1; `git log -- KAM.lean` attributes the generated edits to integration regeneration
commits, whereas the T4 commits modify only the four scoped files. Thus the literal
whole-branch hygiene condition fails; it is not silently reported as an empty diff.
No T4 source/frozen edit causes this note. Do not regenerate the root in this report-only audit.

N2 (dependency note): the handoff's untracked T2-copy issue has been resolved in this HEAD
by merge 98de073f. OrbitJet/Analytic.lean is tracked and defines the exact genuine JetEq.
The design's reduced import DAG omits this helper edge; the actual import is explicit.
T2's proof audit remains separate. T4 is infrastructure and seals no frozen anchor.

No suspected new blueprint or pinned-paper defect was found in this scope. The handoff's
CAS wording “diff vanishes through a^7; comp 1 through a^8” should not be read as an
additional proved jet order: components 6–7 have nonzero degree-7 terms, as the handoff's
approach paragraph already states. The certified orders are precisely those above.
No pinned PDF was independently re-audited; the mathematical authority here is the supplied
blueprint and exact adopted signature, whose formulas and normalization were checked directly.

## Verification receipts

All final Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
A preliminary gate wait and preliminary lint run were cancelled before they launched Lean;
the complete lint was rerun under the required environment and priority before the build.
No process owned by another audit was interrupted.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t4 KAM.Planetary.PlanarTorsion.PairCoefficients
   ```

   Exit 0. Gate output: `[inp-gate] slot 1 acquired 17:06:28 for KAM.Planetary.PlanarTorsion.PairCoefficients`.
   Final output: `Build completed successfully (9121 jobs).`
   Only replayed upstream unused-variable warnings: Kepler/Energy L106,
   Poincare/Chart L212,L247, Kepler/Mass L147,L157,L500,L524. No T4 warning/error.

2. Exact-type, exact-body, root-name and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T4Audit.lean > .lake/abi-scratch/T4Audit.out 2>&1
   ```

   Exit 0; output consists of exactly the following 41 axiom lines. The probe imports the
   production PairCoefficients module, copies the two literal signature definitions and
   checks each equality by rfl, then copies the two signature theorem statements with exact
   applications. A run_cmd inspects the environment for root constants with any of the 45
   direct T4 namespace names; no root collision exists. An independent source declaration
   scan of all other KAM files finds no matching direct short name. Nested helper methods
   (`P11cGood.*`, `p11cVanishes.*`) remain under their distinct parent names; their qualified
   declarations do not collide. No sorryAx or other project axiom is present.

```text
'KAM.Planetary.p11c_pairCoeffs_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_half_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_half_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cDn_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cOrd_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cOrd_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_pair_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cN0_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cN1_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cDn_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQuot_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_pairSeriesJet_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_abs_lt_one_nhds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_comp_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_comp_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_iteratedFDeriv_eq_of_vanishes_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pair_series' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pair_quadratic_consistency' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cHalf_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_half_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cHalf_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cHalf_eq_head_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cTail_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pcoef_half_values' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cHead_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cHead_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11cGood.of_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11cGood.shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11cGood.summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11cGood.hasFPowerSeriesOnBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11cGood.analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11cGood.split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVanishes.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVanishes.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVanishes.mul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVanishes_pow_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_iteratedDeriv_pow_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_iteratedDeriv_eq_of_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_iteratedFDeriv_eq_of_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation containing all four scoped modules:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.PairCoefficients KAM.Planetary.PlanarTorsion.PairCoefficients.Vanish KAM.Planetary.PlanarTorsion.PairCoefficients.Series KAM.Planetary.PlanarTorsion.PairCoefficients.Laplace > .lake/abi-scratch/T4Kernel.out 2>&1
   ```

   Exit 0. Exact output:

   ```text
   replaying KAM.Planetary.PlanarTorsion.PairCoefficients.Laplace
   replaying KAM.Planetary.PlanarTorsion.PairCoefficients.Series
   replaying KAM.Planetary.PlanarTorsion.PairCoefficients.Vanish
   replaying KAM.Planetary.PlanarTorsion.PairCoefficients
   ```

4. Source hygiene:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, exactly:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (802 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   This is the explicitly allowed generated-root exception. Direct forbidden-token/override/
   EuclideanSpace scan of the four scoped files has no matches. Their physical line counts
   are 237,134,82,101 (554 total); each is below 1500, and lint reports no line over 100.
   Each has copyright, module, public imports, module documentation and an exposed public
   noncomputable section. No new instance or root declaration is introduced.

5. Import closure: 75 project modules reachable; no Provider module and no frozen theorem.
   All 47 reachable frozen modules are manifest-owned SEALED definitions. The relevant
   frozen carriers and coordinate/average definitions are used unchanged. T4 itself imports
   only Mathlib, T3 LaplaceReduction, T2 OrbitJet.Analytic and its own helper modules;
   its Laplace helper imports the delivered Part-8 SecularForm.LaplaceIdentities.
   The actual integral normalization and Part-8 series were inspected directly.

6. Comparison/provenance checks:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff inp...HEAD -- KAM/Frozen manifest README.md
   git log --format='%h %s' f82deaf1..HEAD -- KAM.lean
   git diff --check
   ```

   First output is seven added root imports (7 insertions,0 deletions), as disclosed in N1;
   second output is empty. Both diff invocations warn of multiple merge bases.
   Root provenance: `ff90b30b`, `cbc738ce`, `7e495e50`, all integration regeneration commits.
   Whitespace check passes. The final report-only whitespace check also passes; initial scoped source hashes are
   unchanged. Scratch probes and captured outputs are removed after their contents are recorded here.


## Helper binder inventory

These binders belong to independently named local helper lemmas, not additional premises
of either required theorem. SOURCE below means the explicit premise of that elementary
helper statement (as reconstructed from its displayed claim), with blueprint L96–97 as the
local proof obligation. TYPING covers indices and objects. No hidden instances or bundled
proof fields occur. Expanding P11cGood and p11cVanishes gives exactly the formulas in the
definition classification above; their instances are constructed before final use.

| Helper | Binder | Bin |
|---|---|---|
| `p11c_pairCoeffs_apply` | `(a : ℝ)` | TYPING |
| `p11c_pairCoeffs_apply` | `(i : Fin 8)` | TYPING |
| `p11c_laplace_half_zero` | `{x : ℝ}` | TYPING |
| `p11c_laplace_half_zero` | `(hx : \|x\| < 1)` | SOURCE |
| `p11c_laplace_half_one` | `{x : ℝ}` | TYPING |
| `p11c_laplace_half_one` | `(hx : \|x\| < 1)` | SOURCE |
| `p11cDn_ne` | `{a : ℝ}` | TYPING |
| `p11cDn_ne` | `(ha : \|a\| < 1)` | SOURCE |
| `p11cDn_ne` | `(i : Fin 8)` | TYPING |
| `p11cOrd_le` | `(i : Fin 8)` | TYPING |
| `p11cOrd_ge` | `(i : Fin 8)` | TYPING |
| `p11c_pair_identity` | `(i : Fin 8)` | TYPING |
| `p11c_pair_identity` | `(a : ℝ)` | TYPING |
| `p11cN0_analyticAt` | `(i : Fin 8)` | TYPING |
| `p11cN0_analyticAt` | `(x : ℝ)` | TYPING |
| `p11cN1_analyticAt` | `(i : Fin 8)` | TYPING |
| `p11cN1_analyticAt` | `(x : ℝ)` | TYPING |
| `p11cDn_analyticAt` | `(i : Fin 8)` | TYPING |
| `p11cDn_analyticAt` | `(x : ℝ)` | TYPING |
| `p11cQuot_analyticAt` | `(i : Fin 8)` | TYPING |
| `p11cQuot_analyticAt` | `(x : ℝ)` | TYPING |
| `p11c_pairSeriesJet_analyticAt` | `(i : Fin 8)` | TYPING |
| `p11c_pairSeriesJet_analyticAt` | `(x : ℝ)` | TYPING |
| `p11c_abs_lt_one_nhds` | `{a : ℝ}` | TYPING |
| `p11c_abs_lt_one_nhds` | `(ha : \|a\| < 1)` | SOURCE |
| `p11c_comp_analyticAt` | `{a : ℝ}` | TYPING |
| `p11c_comp_analyticAt` | `(ha : \|a\| < 1)` | SOURCE |
| `p11c_comp_analyticAt` | `(i : Fin 8)` | TYPING |
| `p11c_comp_vanishes` | `(i : Fin 8)` | TYPING |
| `p11c_iteratedFDeriv_eq_of_vanishes_real` | `{m : ℕ}` | TYPING |
| `p11c_iteratedFDeriv_eq_of_vanishes_real` | `{f : ℝ → ℝ}` | TYPING |
| `p11c_iteratedFDeriv_eq_of_vanishes_real` | `{g : ℝ → ℝ}` | TYPING |
| `p11c_iteratedFDeriv_eq_of_vanishes_real` | `(hf : AnalyticAt ℝ f 0)` | SOURCE |
| `p11c_iteratedFDeriv_eq_of_vanishes_real` | `(hg : AnalyticAt ℝ g 0)` | SOURCE |
| `p11c_iteratedFDeriv_eq_of_vanishes_real` | `(hv : p11cVanishes m (fun a => f a - g a))` | SOURCE |
| `p11cHalf_good` | `(k : ℕ)` | TYPING |
| `p11c_laplace_neg` | `(s : ℝ)` | TYPING |
| `p11c_laplace_neg` | `(k : ℕ)` | TYPING |
| `p11c_laplace_neg` | `(a : ℝ)` | TYPING |
| `p11c_laplace_half_nonneg` | `(k : ℕ)` | TYPING |
| `p11c_laplace_half_nonneg` | `{a : ℝ}` | TYPING |
| `p11c_laplace_half_nonneg` | `(ha : 0 ≤ a)` | SOURCE |
| `p11c_laplace_half_nonneg` | `(ha1 : a < 1)` | SOURCE |
| `p11c_laplace_half` | `(k : ℕ)` | TYPING |
| `p11c_laplace_half` | `{a : ℝ}` | TYPING |
| `p11c_laplace_half` | `(ha : \|a\| < 1)` | SOURCE |
| `p11cHalf_analyticAt` | `(k : ℕ)` | TYPING |
| `p11cHalf_analyticAt` | `{a : ℝ}` | TYPING |
| `p11cHalf_analyticAt` | `(ha : \|a\| < 1)` | SOURCE |
| `p11cHalf_eq_head_add` | `(k : ℕ)` | TYPING |
| `p11cHalf_eq_head_add` | `{a : ℝ}` | TYPING |
| `p11cHalf_eq_head_add` | `(ha : \|a\| < 1)` | SOURCE |
| `p11cTail_analyticAt` | `(k : ℕ)` | TYPING |
| `p11cTail_analyticAt` | `{a : ℝ}` | TYPING |
| `p11cTail_analyticAt` | `(ha : \|a\| < 1)` | SOURCE |
| `p11cHead_zero` | `(a : ℝ)` | TYPING |
| `p11cHead_one` | `(a : ℝ)` | TYPING |
| `P11cGood.of_bound` | `{w : ℕ → ℝ}` | TYPING |
| `P11cGood.of_bound` | `(hw : ∀ q, \|w q\| ≤ 1)` | SOURCE |
| `P11cGood.shift` | `{w : ℕ → ℝ}` | TYPING |
| `P11cGood.shift` | `(hw : P11cGood w)` | SOURCE |
| `P11cGood.shift` | `(N : ℕ)` | TYPING |
| `P11cGood.summable` | `{w : ℕ → ℝ}` | TYPING |
| `P11cGood.summable` | `(hw : P11cGood w)` | SOURCE |
| `P11cGood.summable` | `{x : ℝ}` | TYPING |
| `P11cGood.summable` | `(hx : \|x\| < 1)` | SOURCE |
| `P11cGood.hasFPowerSeriesOnBall` | `{w : ℕ → ℝ}` | TYPING |
| `P11cGood.hasFPowerSeriesOnBall` | `(hw : P11cGood w)` | SOURCE |
| `P11cGood.analyticAt` | `{w : ℕ → ℝ}` | TYPING |
| `P11cGood.analyticAt` | `(hw : P11cGood w)` | SOURCE |
| `P11cGood.analyticAt` | `{x : ℝ}` | TYPING |
| `P11cGood.analyticAt` | `(hx : \|x\| < 1)` | SOURCE |
| `P11cGood.split` | `{w : ℕ → ℝ}` | TYPING |
| `P11cGood.split` | `(hw : P11cGood w)` | SOURCE |
| `P11cGood.split` | `{x : ℝ}` | TYPING |
| `P11cGood.split` | `(hx : \|x\| < 1)` | SOURCE |
| `P11cGood.split` | `(N : ℕ)` | TYPING |
| `p11cVanishes.mono` | `{m : ℕ}` | TYPING |
| `p11cVanishes.mono` | `{n : ℕ}` | TYPING |
| `p11cVanishes.mono` | `(hmn : n ≤ m)` | SOURCE |
| `p11cVanishes.mono` | `{f : ℝ → ℝ}` | TYPING |
| `p11cVanishes.mono` | `(hf : p11cVanishes m f)` | SOURCE |
| `p11cVanishes.add` | `{m : ℕ}` | TYPING |
| `p11cVanishes.add` | `{f : ℝ → ℝ}` | TYPING |
| `p11cVanishes.add` | `{g : ℝ → ℝ}` | TYPING |
| `p11cVanishes.add` | `(hf : p11cVanishes m f)` | SOURCE |
| `p11cVanishes.add` | `(hg : p11cVanishes m g)` | SOURCE |
| `p11cVanishes.mul_left` | `{m : ℕ}` | TYPING |
| `p11cVanishes.mul_left` | `{f : ℝ → ℝ}` | TYPING |
| `p11cVanishes.mul_left` | `(g : ℝ → ℝ)` | TYPING |
| `p11cVanishes.mul_left` | `(hg : AnalyticAt ℝ g 0)` | SOURCE |
| `p11cVanishes.mul_left` | `(hf : p11cVanishes m f)` | SOURCE |
| `p11cVanishes_pow_mul` | `(m : ℕ)` | TYPING |
| `p11cVanishes_pow_mul` | `{h : ℝ → ℝ}` | TYPING |
| `p11cVanishes_pow_mul` | `(hh : AnalyticAt ℝ h 0)` | SOURCE |
| `p11c_iteratedDeriv_eq_of_vanishes` | `{m : ℕ}` | TYPING |
| `p11c_iteratedDeriv_eq_of_vanishes` | `{f : ℝ → ℝ}` | TYPING |
| `p11c_iteratedDeriv_eq_of_vanishes` | `{g : ℝ → ℝ}` | TYPING |
| `p11c_iteratedDeriv_eq_of_vanishes` | `(hf : AnalyticAt ℝ f 0)` | SOURCE |
| `p11c_iteratedDeriv_eq_of_vanishes` | `(hg : AnalyticAt ℝ g 0)` | SOURCE |
| `p11c_iteratedDeriv_eq_of_vanishes` | `(hv : p11cVanishes m (fun a => f a - g a))` | SOURCE |
| `p11c_iteratedFDeriv_eq_of_vanishes` | `{n : ℕ}` | TYPING |
| `p11c_iteratedFDeriv_eq_of_vanishes` | `{m : ℕ}` | TYPING |
| `p11c_iteratedFDeriv_eq_of_vanishes` | `{F : ℝ → Fin n → ℝ}` | TYPING |
| `p11c_iteratedFDeriv_eq_of_vanishes` | `{G : ℝ → Fin n → ℝ}` | TYPING |
| `p11c_iteratedFDeriv_eq_of_vanishes` | `(hF : ∀ i, AnalyticAt ℝ (fun a => F a i) 0)` | SOURCE |
| `p11c_iteratedFDeriv_eq_of_vanishes` | `(hG : ∀ i, AnalyticAt ℝ (fun a => G a i) 0)` | SOURCE |
| `p11c_iteratedFDeriv_eq_of_vanishes` | `(hv : ∀ i, p11cVanishes m (fun a => F a i - G a i))` | SOURCE |
| `p11c_iteratedDeriv_pow_mul` | `j : ℕ` (outer ∀) | TYPING |
| `p11c_iteratedDeriv_pow_mul` | `m : ℕ` (outer ∀) | TYPING |
| `p11c_iteratedDeriv_pow_mul` | `{h : ℝ → ℝ}` | TYPING |
| `p11c_iteratedDeriv_pow_mul` | `AnalyticAt ℝ h 0` (arrow premise) | SOURCE |
| `p11c_iteratedDeriv_pow_mul` | `j < m` (arrow premise) | SOURCE |

Top-level parenthesized helper binder-name counts: SOURCE=36, TYPING=72, STANDING=0, RULED=0, EXCESS=0.
Universally quantified derivative indices and scalar radii inside conclusions are output tests,
not extra logical premises. The arrow-form input of `p11c_iteratedDeriv_pow_mul`
is `AnalyticAt ℝ h 0` (SOURCE), with `j,m,h` TYPING and `j<m` SOURCE; its entire claim
is proved by induction in V49–68. All other logical inputs are named in the table.


Only this report is a lasting auditor edit. Scratch files are confined to .lake/abi-scratch
and are removed after checking. The pre-existing untracked T4-handoff is preserved.
No source, frozen file, manifest, README or generated root is edited; no git mutation is run.

Scoped source SHA-256 at final verification:

| File | SHA-256 |
|---|---|
| `KAM/Planetary/PlanarTorsion/PairCoefficients.lean` | `41bc9a4b72f73cafbbead8cd74d0f7947074c5c8024189585fc2ba6745c4a778` |
| `KAM/Planetary/PlanarTorsion/PairCoefficients/Laplace.lean` | `0f9b403970cafe81c7a65e64994bcd648be5b9e3a94d67b70854fd4ea1509d61` |
| `KAM/Planetary/PlanarTorsion/PairCoefficients/Series.lean` | `a1f092f24146bf821e8bd8ab868bcd5fad699e092f1cf847e3759d7044592aa8` |
| `KAM/Planetary/PlanarTorsion/PairCoefficients/Vanish.lean` | `43ca84e59b82404a77738aa8dc33f7f1f7f9a75b1cec41b4f12510f702465b29` |
