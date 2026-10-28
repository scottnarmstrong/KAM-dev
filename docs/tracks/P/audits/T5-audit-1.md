# Independent T5 package audit 1

Overall verdict: **PASS WITH NOTES** (N1 inherited comparison/root hygiene; N2 informational route/footprint).
The signed `KAM.Planetary.pair_jet` and both signed definitions PASS. T5 delivers the actual
averaged interaction, not an assumed coefficient identity. This is an infrastructure package;
there is no T5 frozen theorem/provider pair to seal and no physical headline is closed here.

## Scope and immutable inputs

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-t5`.
Audited HEAD: `8aebe5989912674c2db8e771a803776f0fef16c3`.
Observed comparison ref: `inp=b5e58ec5e766134ead4e306f3ed3c4dc0da81acd`.
`git diff inp...HEAD` warns of multiple merge bases and selects
`38861df6404871197b333652da38321935567c0a`. The full comparison was captured and its scope
inventoried (13,541 diff lines); mathematical implementation review is confined to the 17 PairJet
files listed below, as required by AUDIT FOCUS. Other packages in this comparison are not certified.

Authority read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T5-handoff including AUDIT FOCUS,
P11C-LEAN-DESIGN.md (T5 row, complete node table, upstream interfaces, proof instructions and
signature appendix), DESIGN-P11C-design-audit-1.md, track-P statement, and blueprint-P Part 11b
L64–98. The statement-audit skill was used for binder, body, consumption and axiom checks.
The user's exact worktree destination overrides the generic brief's main-worktree destination.
Only this report is a lasting edit; transient probes and audit receipts are in `.lake/abi-scratch/`.

| Input | SHA-256 |
|---|---|
| P11C-LEAN-DESIGN.md | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| `blueprint-P/parts/p11b-planar-torsion.tex` | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |

## Findings and refutation

**N1 — comparison/root hygiene, inherited; nonblocking for this slice.** The literal command
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: it contains
31 added import lines in `KAM.lean`. Frozen files, manifest and README have no diff.
Refutation: `git diff 601bf145^..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty;
`601bf145` is the first T5 commit. The root additions predate T5 and name other packages
(including T2), not PairJet. This is not a T5 protected-file edit. The generated root remains
stale for the new modules; the brief explicitly permits that lint exception. Do not report a
clean protected-path three-dot check or regenerate the root during this audit.

**N2 — proof route and footprint, informational.** T5 uses coefficientwise exact algebra and
local evenness rather than separately exporting all S2/S3 invariance statements. The exact
quartic polynomial equality implies cancellation of all unlisted degree-four monomials, including
imaginary terms, so no symmetry premise is missing. The blueprint's “every ... occurring ...
k≤8” does not demand a table of unused indices 7 and 8: actual generated terms are reduced by
the explicit table used in Combine2/4. The design's 750-line estimate is exceeded in total
(5,591 lines), but the required split is implemented: largest file is 995 lines.

No mathematical blocker survived checks of physical norm, radian normalization, coordinate order,
source premises, diagonal-to-multilinear passage, or odd-order closure. No new pinned-source erratum
is alleged. Existing design-audit notes about graph provenance and the dispatch DAG do not alter
the signed T5 surface; generic `p11c_homogeneousPart` already lives in Setting upstream.

## Signed declarations, binder audit and completeness

Whitespace-stripped complete definitions and theorem header are identical to signature L363–372.
Fresh Lean copies of both signature definitions satisfy `rfl` equality with production definitions.
A fresh copy of the exact signed theorem elaborates with `by exact KAM.Planetary.pair_jet a ha`.
The probe also checks `example : type_of% @KAM.Planetary.pair_jet := @KAM.Planetary.pair_jet`;
the independent copied statement is the substantive type check. Frozen-provider equality and a
frozen seal-body probe are N/A, because T5 has no frozen anchor or provider export.

Expanded binder test for `pair_jet`:

| Binder | Bin | Source |
|---|---|---|
| `(a : ℝ)` | TYPING | Blueprint L65 and signature L371. |
| `(ha : a ∈ Ioo (0 : ℝ) 1)` | SOURCE | Literal `0<α<1`, blueprint L65. |

Counts: SOURCE=1, STANDING=0, TYPING=1, RULED=0, EXCESS=0. There are no implicit,
instance, bundled or conclusion-shaped premises in this theorem. `p11c_JetEq` expands to
`∀ j ≤ 5, iteratedFDeriv ℝ j f 0 = iteratedFDeriv ℝ j g 0`, including the full multilinear
maps at orders 0 through 5, not only their diagonals. Its ambient norm is the standard Pi/product
norm; the physical inverse distance is the complex norm, hence the physical plane 2-norm.

| Graph node / design row | Lean implementation | Verdict | Reason |
|---|---|---|---|
| T5, `bpP:p11b:pair-jet` integral share | `pair_jet`, `p11c_pairAverage`, `p11c_pairJet` | PASS | Exact signed actual integral, analyticity at zero and full 5-jet. |
| `stepP:p11b:pj-formal` | Bridge, Diff, Diag, Ray | PASS | Actual secular bridge, compact noncollision neighbourhood, differentiated integral, analytic diagonal identification and polarization are proved and consumed. |
| `stepP:p11b:pj-bin` | Rot, Ray, all seven `p11cPJ_q*_eq` | PASS | Orbit line jet and inverse norm jet, exact binomial coefficients through degree four; no CAS premise. |
| `stepP:p11b:pj-avg` | Average, Terms, all seven `p11cPJ_q*_avg` | PASS | Fourier charge selection, signed Fourier index and normalized Laplace integral. |
| `stepP:p11b:pj-red` T5 share | Reduction, Combine2/4; `p11cPJ_avg2/4` | PASS | Guarded recurrences and exact rational extraction of all four quadratic and nine complex quartic coefficients. |
| `stepP:p11b:pj-cons` | T4 `pair_quadratic_consistency`; T5 `p11cPJ_avg2` | PASS for T5 share | Actual averaged quadratic part matches the same A,B; the Laplace identities themselves are T4, not re-certified here. |
| Shared proposition's alpha-series | T4 `pair_series`, `p11c_pairCoeffs` | Upstream scope | Complete shared node requires T4 evidence as well; T5 does not claim to reprove its series receipt. |

All six node-table rows touching T5 are accounted for. No unsigned export masquerades as a full
source node with extra assumptions. Generic conditional helpers have distinct names; their
analyticity/jet/smoothness/charge premises are produced at call sites. In particular:

- Bridge: positive action and eccentricity-disc hypotheses are supplied near zero. The exact
  fixed-centre potential is `-pairAverage` for unit physical data and axes `(a,1)`; the square-root
  scale produces the intended eccentricity vector and the physical positions `Λ² orbit`.
- Diff: `p11cPJW` is an open disc/noncollision set containing every `(l,0)`. Compactness supplies
  one angle-uniform neighbourhood. The four-variable slice is proved and calls Part-8
  `SecularForm.e_diff`; no differentiation/interchange premise enters `pair_jet`.
- Ray: `P² N=1` and the positive constant branch identify the inverse norm jet; eventual nonzero
  factors justify cancellation. All seven binomial coefficients agree with the blueprint.
- Average/Terms: continuity proves integrability before finite summation. Neutral modes give
  `(2π)² b`, charged modes zero; the outer `(2π)^(-2)` cancels exactly.
- Combine2/4: arbitrary complex ζ and ζbar arguments are allowed independently, a stronger
  algebraic statement than the physical conjugate specialization. The facade supplies actual
  conjugates and identifies products with squares and dot products.
- Diag/facade: analyticity justifies symmetric iterated derivatives and polarization. Only even
  orders 0,2,4 need the orbit 4-jet. Local evenness proves orders 1,3,5 vanish. Thus a missing
  orbit 5-jet is not a gap and equality through order five is obtained.
  A separately quantified remainder estimate is not exported by this signed T5 theorem.

## Definition classification

There are 151 explicit definitions and one structure, all literal computational objects; no
choice-defined object, analytic-existence package, or proof-obligation field is introduced.
The declaration inventory below classifies each individually by its family and locator.

| Family | Classification and full-carrier check |
|---|---|
| `p11c_pairAverage`, `p11c_pairJet` | Literal signed integral/polynomial formulas, definitionally checked against the signature. No new branch or altered carrier. Total inverse/integral conventions are exactly those of the signed formula; analytic claims concern `0<a<1` near zero. |
| `PJTerm` | Pure coefficient/exponent data: one complex coefficient, seven natural exponents; no Prop fields. |
| Fourier atoms, monomials, charge/index, lists, coefficient tables | Literal finite algebra on every declared input; exact expansion and integral theorems certify their use. No numerical assumptions or external certificates. |
| `p11cPJN`, `p11cPJv`, `p11cPJj*`, `p11cPJq*`, `p11cPJcJet`, conjugation/rotation | Literal truncated-jet algebra; the identity and ray theorems connect it to the integrand. |
| `p11cPJF`, `p11cPJF4`, `p11cPJG`, `p11cPJW` | Actual inverse-distance integrand, its orbit difference, and the explicitly stated open noncollision/disc locus. No surrogate integrand. |
| `p11cPJD`, `p11cPJax`, `p11cPJscale`, `p11cPJx` | Literal auxiliary unit-data, axes and coordinate maps. Square roots keep their standard total semantics; inverse-chart assertions explicitly require positive action and the disc and prove those guards. |
| `p11cPJequiv` | Explicit linear coordinate permutation with both inverse laws, no selected witness. |
| `p11cPJcoeff` | Finite polynomial coefficient accessor; zero above degree four is the intended coefficient of a degree-four polynomial, not a fallback for an unpaid theorem. |
| `p11cPJP2`, `p11cPJP4` | Literal homogeneous pieces; exact scaling and line-jet identities. |

For all 152 objects: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL;
CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.
Auxiliary literal encodings are certified by their displayed reconstruction/expansion identities.

## Verification receipt

All audit Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No heartbeat, recursion-depth or synthesis-heartbeat override was used. No rebuild from scratch,
package mutation, cache operation or library clean was performed.

1. Targeted compile-gate build:

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t5 KAM.Planetary.PlanarTorsion.PairJet
```

Exit **0**. Exact gate/final output:

```text
[inp-gate] slot 3 acquired 21:01:38 for KAM.Planetary.PlanarTorsion.PairJet
Build completed successfully (9158 jobs).
```

Replayed scoped warnings: 37 unused-variable, 10 unused-simp-argument and one deprecation
(`Bridge.lean:101:28`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`). Thus the handoff's “unused-simp
only” description is slightly incomplete; these are nonblocking linter warnings, not escapes.

2. Fresh signature/body/axiom probe:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T5Probe.lean
```

Exit **0**; no error or warning. Both copied definitions pass `rfl`; the exact copied signed
statement passes its explicit-binder assembly. All 203 `#print axioms` commands produce exactly
`[propext, Classical.choice, Quot.sound]`; complete output is below. In particular:

```text
'KAM.Planetary.pair_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation (facade and every lemma module):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.PairJet KAM.Planetary.PlanarTorsion.PairJet.Average KAM.Planetary.PlanarTorsion.PairJet.Bridge KAM.Planetary.PlanarTorsion.PairJet.Combine2 KAM.Planetary.PlanarTorsion.PairJet.Combine4 KAM.Planetary.PlanarTorsion.PairJet.Defs KAM.Planetary.PlanarTorsion.PairJet.Diag KAM.Planetary.PlanarTorsion.PairJet.Diff KAM.Planetary.PlanarTorsion.PairJet.Piece22 KAM.Planetary.PlanarTorsion.PairJet.Piece4a KAM.Planetary.PlanarTorsion.PairJet.Piece4b KAM.Planetary.PlanarTorsion.PairJet.Piece4c KAM.Planetary.PlanarTorsion.PairJet.PolyJet KAM.Planetary.PlanarTorsion.PairJet.Ray KAM.Planetary.PlanarTorsion.PairJet.Reduction KAM.Planetary.PlanarTorsion.PairJet.Rot KAM.Planetary.PlanarTorsion.PairJet.Terms
```

Exit **0**; exact complete output:

```text
replaying KAM.Planetary.PlanarTorsion.PairJet.Terms
replaying KAM.Planetary.PlanarTorsion.PairJet.Defs
replaying KAM.Planetary.PlanarTorsion.PairJet.Diff
replaying KAM.Planetary.PlanarTorsion.PairJet.Bridge
replaying KAM.Planetary.PlanarTorsion.PairJet.Piece4b
replaying KAM.Planetary.PlanarTorsion.PairJet.Diag
replaying KAM.Planetary.PlanarTorsion.PairJet.Piece22
replaying KAM.Planetary.PlanarTorsion.PairJet.Piece4a
replaying KAM.Planetary.PlanarTorsion.PairJet.Average
replaying KAM.Planetary.PlanarTorsion.PairJet.Reduction
replaying KAM.Planetary.PlanarTorsion.PairJet.Combine4
replaying KAM.Planetary.PlanarTorsion.PairJet.Combine2
replaying KAM.Planetary.PlanarTorsion.PairJet.Rot
replaying KAM.Planetary.PlanarTorsion.PairJet.PolyJet
replaying KAM.Planetary.PlanarTorsion.PairJet.Ray
replaying KAM.Planetary.PlanarTorsion.PairJet.Piece4c
replaying KAM.Planetary.PlanarTorsion.PairJet
```

Module-set comparison: 17 requested, 17 replayed, no missing/extra modules.

4. Source lint and frozen ABI check:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted generated-root staleness. Exact complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (842 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All source-pattern, line-size, module, frozen-anchor and ABI checks otherwise pass. No root
regeneration was performed.

5. Static scope/hygiene checks:

- `git diff --check inp...HEAD -- KAM/Planetary/PlanarTorsion/PairJet.lean KAM/Planetary/PlanarTorsion/PairJet`
  exits **0**, with only the multiple-merge-base warning recorded above.
- `rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace|_root_' KAM/Planetary/PlanarTorsion/PairJet.lean KAM/Planetary/PlanarTorsion/PairJet`
  produces **no matches** (exit 1).
- Python Unicode-character line scan: **no line over 100 characters**; 17 files, 5,591 lines,
  maximum 995. Each has copyright, `module`, public imports, module docstring and exposed public
  noncomputable section. No harmful root shadow or auxiliary top-level namespace was introduced.
- Project-wide public-declaration short-name scan outside the scoped files: **zero collisions**
  with any of the 355 explicit T5 public declarations, including PJTerm and its qualified methods.
- Recursive local-project import scan: **112 modules**, **zero providers**, **zero frozen theorem
  modules**; all **47 frozen definition modules are SEALED**, matched by exact manifest `path`
  (not substring membership in dependency metadata). Their literal definition bodies were inspected.
- The literal protected-path three-dot check is nonempty only for inherited `KAM.lean`, as N1
  records. The T5-commit-range protected-path check is empty.
- Final tracked working diff is empty. Initial untracked T5-handoff is preserved; this report is
  the only new repository artifact. Probe source and temporary audit scratch are removed after
  recording their results.


## Complete declaration inventory

All names have prefix `KAM.Planetary.`. Locations below are relative to
`KAM/Planetary/PlanarTorsion/`; `PairJet/F.lean` abbreviates the corresponding module.
Every explicit new public declaration is listed (355: 203 theorems, 151 defs, one structure).
Generated PJTerm constructor/projections carry only its data fields and are covered by that row.
All 203 theorem axiom sets are exactly `[propext, Classical.choice, Quot.sound]`.
The node column denotes the local source argument, not a claim that each helper is an independent
graph-node export. Conditional lemmas retain their explicit premises and are consumed internally.

| Node / file:line | Declaration | Verdict | Reason / definition classification |
|---|---|---|---|
| pj-formal; PairJet.lean:57 | `p11cPJ_avg0` (theorem) | PASS | Exact normalized diagonal derivative or leading average identity. |
| pj-formal; PairJet.lean:74 | `p11cPJ_diag_avg` (theorem) | PASS | Exact normalized diagonal derivative or leading average identity. |
| pj-formal; PairJet.lean:95 | `p11cPJ_diag_jet` (theorem) | PASS | Exact normalized diagonal derivative or leading average identity. |
| pair-jet; PairJet.lean:103 | `pair_jet` (theorem) | PASS | Exact signed theorem; actual analytic average and full 5-jet. |
| pj-avg; PairJet/Average.lean:26 | `p11cPJS` (def) | PASS | Literal kernel power or Fourier exponential. |
| pj-avg; PairJet/Average.lean:28 | `p11cPJS_pow` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:35 | `p11cPJS_continuous` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:38 | `p11cPJS_periodic` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:41 | `p11cPJS_even` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:44 | `p11cPJS_two_pi_sub` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:48 | `p11cPJ_integral_cell_two` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:87 | `p11cPJE` (def) | PASS | Literal kernel power or Fourier exponential. |
| pj-avg; PairJet/Average.lean:89 | `p11cPJE_add_int` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:92 | `p11cPJE_add_real` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:95 | `p11cPJE_neg_real` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:98 | `p11cPJE_zero` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:100 | `p11cPJE_two_pi` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:105 | `p11cPJE_period` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:108 | `p11cPJE_continuous` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:112 | `p11cPJ_inner` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:137 | `p11cPJ_integral_E` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:150 | `p11cPJ_cell` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:173 | `p11cPJ_cell_charged` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:179 | `p11cPJ_cell_neutral` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-avg; PairJet/Average.lean:189 | `p11cPJ_laplace` (theorem) | PASS | Exact periodic Fourier integration; radian normalization retained. |
| pj-formal; PairJet/Bridge.lean:31 | `p11cPJD` (def) | PASS | Literal auxiliary physical data/coordinate formula. |
| pj-formal; PairJet/Bridge.lean:34 | `p11cPJax` (def) | PASS | Literal auxiliary physical data/coordinate formula. |
| pj-formal; PairJet/Bridge.lean:36 | `p11cPJax_mem` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:47 | `p11cPJscale` (def) | PASS | Literal auxiliary physical data/coordinate formula. |
| pj-formal; PairJet/Bridge.lean:50 | `p11cPJx` (def) | PASS | Literal auxiliary physical data/coordinate formula. |
| pj-formal; PairJet/Bridge.lean:55 | `p11cPJ_action` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:59 | `p11cPJ_poincareV` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:107 | `p11cPJ_position` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:126 | `p11cPJ_planeLength_sub` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:135 | `p11cPJ_pairPotential_two` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:142 | `p11cPJ_action_pos` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:149 | `p11cPJ_perturbation` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:188 | `p11cPJ_secular_eq` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:196 | `p11cPJ_mem_slowDom` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:216 | `p11cPJscale_analyticAt` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:227 | `p11cPJx_analyticAt` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:238 | `p11cPJ_eventually_small` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:245 | `p11cPJ_pairAverage_analyticAt` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:265 | `p11cPJx_neg` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-formal; PairJet/Bridge.lean:272 | `p11cPJ_pairAverage_even` (theorem) | PASS | Exact physical chart/secular/analytic/evenness bridge with explicit domain guards. |
| pj-red; PairJet/Combine2.lean:30 | `p11cPJ_mu2_0` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine2.lean:44 | `p11cPJ_mu2_1` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine2.lean:58 | `p11cPJ_mu2_2` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine2.lean:72 | `p11cPJ_mu2_3` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine2.lean:86 | `p11cPJ_avg2` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:32 | `p11cPJ_mu4_0` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:49 | `p11cPJ_mu4_1` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:67 | `p11cPJ_mu4_2` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:86 | `p11cPJ_mu4_3` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:104 | `p11cPJ_mu4_4` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:122 | `p11cPJ_mu4_5` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:140 | `p11cPJ_mu4_6` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:159 | `p11cPJ_mu4_7` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:177 | `p11cPJ_mu4_8` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pj-red; PairJet/Combine4.lean:194 | `p11cPJ_avg4` (theorem) | PASS | Exact reduced coefficient identity; only 0<a<1 plus algebraic data. |
| pair-jet; PairJet/Defs.lean:26 | `p11c_pairAverage` (def) | PASS | Literal signed formula; exact body probe by rfl. |
| pair-jet; PairJet/Defs.lean:30 | `p11c_pairJet` (def) | PASS | Literal signed formula; exact body probe by rfl. |
| pj-formal; PairJet/Diag.lean:32 | `p11cPJcoeff` (def) | PASS | Literal coefficient accessor or explicit linear equivalence. |
| pj-formal; PairJet/Diag.lean:41 | `p11cPJequiv` (def) | PASS | Literal coefficient accessor or explicit linear equivalence. |
| pj-formal; PairJet/Diag.lean:53 | `p11cPJequiv_apply` (theorem) | PASS | Analytic jet coefficient uniqueness or exact symmetric polarization/coordinate transport. |
| pj-formal; PairJet/Diag.lean:84 | `p11cPJ_poly_unique` (theorem) | PASS | Analytic jet coefficient uniqueness or exact symmetric polarization/coordinate transport. |
| pj-formal; PairJet/Diag.lean:119 | `p11cPJ_diag_coeff` (theorem) | PASS | Analytic jet coefficient uniqueness or exact symmetric polarization/coordinate transport. |
| pj-formal; PairJet/Diag.lean:172 | `p11cPJ_jetEq_of_diag` (theorem) | PASS | Analytic jet coefficient uniqueness or exact symmetric polarization/coordinate transport. |
| pj-formal; PairJet/Diag.lean:204 | `p11cPJ_diag_comp_equiv` (theorem) | PASS | Analytic jet coefficient uniqueness or exact symmetric polarization/coordinate transport. |
| pj-formal; PairJet/Diff.lean:48 | `p11cPJ_orbit_analyticAt` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:100 | `p11c_orbit_zero` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:116 | `p11cPJG` (def) | PASS | Literal integrand/difference/open domain. |
| pj-formal; PairJet/Diff.lean:120 | `p11cPJW` (def) | PASS | Literal integrand/difference/open domain. |
| pj-formal; PairJet/Diff.lean:124 | `p11cPJF4` (def) | PASS | Literal integrand/difference/open domain. |
| pj-formal; PairJet/Diff.lean:126 | `p11cPJF4_eq` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:144 | `p11cPJG_analyticAt` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:161 | `p11cPJF4_analyticAt` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:192 | `isOpen_p11cPJW` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:208 | `mem_p11cPJW_zero` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:229 | `p11cPJ_iteratedFDeriv_slice` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:252 | `p11cPJ_e_diff` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:302 | `p11cPJ_diag_integral` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-formal; PairJet/Diff.lean:350 | `p11cPJF_analyticAt` (theorem) | PASS | Joint analyticity, open noncollision locus, or proved partial-derivative/integral bridge. |
| pj-bin / pj-avg; PairJet/Piece22.lean:27 | `p11cPJLN_q22a_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece22.lean:39 | `p11cPJLN_q22a` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece22.lean:42 | `p11cPJLC_q22a_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece22.lean:60 | `p11cPJLC_q22a` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-red; PairJet/Piece22.lean:63 | `p11cPJC_q22a_0` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece22.lean:67 | `p11cPJC_q22a_1` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece22.lean:71 | `p11cPJC_q22a_2` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece22.lean:75 | `p11cPJC_q22a_3` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-avg; PairJet/Piece22.lean:79 | `p11cPJLN_q22a_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece22.lean:84 | `p11cPJLC_q22a_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece22.lean:89 | `p11cPJ_q22a_neutral` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-avg; PairJet/Piece22.lean:94 | `p11cPJ_q22a_charged` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin; PairJet/Piece22.lean:99 | `p11cPJ_q22a_eq` (theorem) | PASS | Exact all-variable expansion by ring, stronger than physical specialization. |
| pj-avg; PairJet/Piece22.lean:109 | `p11cPJ_q22a_avg` (theorem) | PASS | Exact finite Fourier averaging with full (2π)² factor. |
| pj-avg; PairJet/Piece22.lean:138 | `p11cPJ_q22a_integrable` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin / pj-avg; PairJet/Piece22.lean:156 | `p11cPJLN_q22b_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece22.lean:182 | `p11cPJLN_q22b` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece22.lean:185 | `p11cPJLC_q22b_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece22.lean:223 | `p11cPJLC_q22b` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-red; PairJet/Piece22.lean:226 | `p11cPJC_q22b_0` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece22.lean:231 | `p11cPJC_q22b_1` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece22.lean:237 | `p11cPJC_q22b_2` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece22.lean:243 | `p11cPJC_q22b_3` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-avg; PairJet/Piece22.lean:248 | `p11cPJLN_q22b_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece22.lean:253 | `p11cPJLC_q22b_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece22.lean:258 | `p11cPJ_q22b_neutral` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-avg; PairJet/Piece22.lean:263 | `p11cPJ_q22b_charged` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin; PairJet/Piece22.lean:268 | `p11cPJ_q22b_eq` (theorem) | PASS | Exact all-variable expansion by ring, stronger than physical specialization. |
| pj-avg; PairJet/Piece22.lean:278 | `p11cPJ_q22b_avg` (theorem) | PASS | Exact finite Fourier averaging with full (2π)² factor. |
| pj-avg; PairJet/Piece22.lean:307 | `p11cPJ_q22b_integrable` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:27 | `p11cPJLN_q44a_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:43 | `p11cPJLN_q44a` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:46 | `p11cPJLC_q44a_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:84 | `p11cPJLC_q44a_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:106 | `p11cPJLC_q44a` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-red; PairJet/Piece4a.lean:110 | `p11cPJC_q44a_0` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:113 | `p11cPJC_q44a_1` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:116 | `p11cPJC_q44a_2` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:120 | `p11cPJC_q44a_3` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:123 | `p11cPJC_q44a_4` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:126 | `p11cPJC_q44a_5` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:129 | `p11cPJC_q44a_6` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:133 | `p11cPJC_q44a_7` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:136 | `p11cPJC_q44a_8` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-avg; PairJet/Piece4a.lean:139 | `p11cPJLN_q44a_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:144 | `p11cPJLC_q44a_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:149 | `p11cPJLC_q44a_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:154 | `p11cPJ_q44a_neutral` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-avg; PairJet/Piece4a.lean:159 | `p11cPJ_q44a_charged` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin; PairJet/Piece4a.lean:165 | `p11cPJ_q44a_eq` (theorem) | PASS | Exact all-variable expansion by ring, stronger than physical specialization. |
| pj-avg; PairJet/Piece4a.lean:176 | `p11cPJ_q44a_avg` (theorem) | PASS | Exact finite Fourier averaging with full (2π)² factor. |
| pj-avg; PairJet/Piece4a.lean:211 | `p11cPJ_q44a_integrable` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:229 | `p11cPJLN_q413_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:267 | `p11cPJLN_q413_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:284 | `p11cPJLN_q413` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:288 | `p11cPJLC_q413_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:326 | `p11cPJLC_q413_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:364 | `p11cPJLC_q413_2` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:402 | `p11cPJLC_q413_3` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:440 | `p11cPJLC_q413_4` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:444 | `p11cPJLC_q413` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-red; PairJet/Piece4a.lean:451 | `p11cPJC_q413_0` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:456 | `p11cPJC_q413_1` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:462 | `p11cPJC_q413_2` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:469 | `p11cPJC_q413_3` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:475 | `p11cPJC_q413_4` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:480 | `p11cPJC_q413_5` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:486 | `p11cPJC_q413_6` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:493 | `p11cPJC_q413_7` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:499 | `p11cPJC_q413_8` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-avg; PairJet/Piece4a.lean:504 | `p11cPJLN_q413_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:509 | `p11cPJLN_q413_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:514 | `p11cPJLC_q413_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:519 | `p11cPJLC_q413_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:524 | `p11cPJLC_q413_2_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:529 | `p11cPJLC_q413_3_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:534 | `p11cPJLC_q413_4_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:539 | `p11cPJ_q413_neutral` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-avg; PairJet/Piece4a.lean:545 | `p11cPJ_q413_charged` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin; PairJet/Piece4a.lean:552 | `p11cPJ_q413_eq` (theorem) | PASS | Exact all-variable expansion by ring, stronger than physical specialization. |
| pj-avg; PairJet/Piece4a.lean:563 | `p11cPJ_q413_avg` (theorem) | PASS | Exact finite Fourier averaging with full (2π)² factor. |
| pj-avg; PairJet/Piece4a.lean:598 | `p11cPJ_q413_integrable` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:616 | `p11cPJLN_q422_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:654 | `p11cPJLN_q422_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:670 | `p11cPJLN_q422` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:674 | `p11cPJLC_q422_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:712 | `p11cPJLC_q422_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:750 | `p11cPJLC_q422_2` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:788 | `p11cPJLC_q422_3` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4a.lean:826 | `p11cPJLC_q422` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-red; PairJet/Piece4a.lean:832 | `p11cPJC_q422_0` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:837 | `p11cPJC_q422_1` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:843 | `p11cPJC_q422_2` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:850 | `p11cPJC_q422_3` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:856 | `p11cPJC_q422_4` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:861 | `p11cPJC_q422_5` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:867 | `p11cPJC_q422_6` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:874 | `p11cPJC_q422_7` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4a.lean:880 | `p11cPJC_q422_8` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-avg; PairJet/Piece4a.lean:885 | `p11cPJLN_q422_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:890 | `p11cPJLN_q422_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:895 | `p11cPJLC_q422_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:900 | `p11cPJLC_q422_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:905 | `p11cPJLC_q422_2_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:910 | `p11cPJLC_q422_3_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4a.lean:915 | `p11cPJ_q422_neutral` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-avg; PairJet/Piece4a.lean:921 | `p11cPJ_q422_charged` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin; PairJet/Piece4a.lean:928 | `p11cPJ_q422_eq` (theorem) | PASS | Exact all-variable expansion by ring, stronger than physical specialization. |
| pj-avg; PairJet/Piece4a.lean:939 | `p11cPJ_q422_avg` (theorem) | PASS | Exact finite Fourier averaging with full (2π)² factor. |
| pj-avg; PairJet/Piece4a.lean:974 | `p11cPJ_q422_integrable` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:26 | `p11cPJLN_q4112_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:66 | `p11cPJLN_q4112_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:106 | `p11cPJLN_q4112_2` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:126 | `p11cPJLN_q4112` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:131 | `p11cPJLC_q4112_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:169 | `p11cPJLC_q4112_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:211 | `p11cPJLC_q4112_2` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:252 | `p11cPJLC_q4112_3` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:291 | `p11cPJLC_q4112_4` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:331 | `p11cPJLC_q4112_5` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:371 | `p11cPJLC_q4112_6` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:409 | `p11cPJLC_q4112_7` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4b.lean:419 | `p11cPJLC_q4112` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-red; PairJet/Piece4b.lean:429 | `p11cPJC_q4112_0` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4b.lean:435 | `p11cPJC_q4112_1` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4b.lean:442 | `p11cPJC_q4112_2` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4b.lean:450 | `p11cPJC_q4112_3` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4b.lean:457 | `p11cPJC_q4112_4` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4b.lean:463 | `p11cPJC_q4112_5` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4b.lean:470 | `p11cPJC_q4112_6` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4b.lean:478 | `p11cPJC_q4112_7` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4b.lean:485 | `p11cPJC_q4112_8` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-avg; PairJet/Piece4b.lean:491 | `p11cPJLN_q4112_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:496 | `p11cPJLN_q4112_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:501 | `p11cPJLN_q4112_2_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:506 | `p11cPJLC_q4112_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:511 | `p11cPJLC_q4112_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:516 | `p11cPJLC_q4112_2_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:521 | `p11cPJLC_q4112_3_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:526 | `p11cPJLC_q4112_4_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:531 | `p11cPJLC_q4112_5_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:536 | `p11cPJLC_q4112_6_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:541 | `p11cPJLC_q4112_7_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4b.lean:546 | `p11cPJ_q4112_neutral` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-avg; PairJet/Piece4b.lean:553 | `p11cPJ_q4112_charged` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin; PairJet/Piece4b.lean:561 | `p11cPJ_q4112_eq` (theorem) | PASS | Exact all-variable expansion by ring, stronger than physical specialization. |
| pj-avg; PairJet/Piece4b.lean:573 | `p11cPJ_q4112_avg` (theorem) | PASS | Exact finite Fourier averaging with full (2π)² factor. |
| pj-avg; PairJet/Piece4b.lean:609 | `p11cPJ_q4112_integrable` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:26 | `p11cPJLN_q4114_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:65 | `p11cPJLN_q4114_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:107 | `p11cPJLN_q4114_2` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:149 | `p11cPJLN_q4114_3` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:178 | `p11cPJLN_q4114` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:184 | `p11cPJLC_q4114_0` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:222 | `p11cPJLC_q4114_1` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:260 | `p11cPJLC_q4114_2` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:304 | `p11cPJLC_q4114_3` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:345 | `p11cPJLC_q4114_4` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:386 | `p11cPJLC_q4114_5` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:424 | `p11cPJLC_q4114_6` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:462 | `p11cPJLC_q4114_7` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:506 | `p11cPJLC_q4114_8` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:544 | `p11cPJLC_q4114_9` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:582 | `p11cPJLC_q4114_10` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-bin / pj-avg; PairJet/Piece4c.lean:606 | `p11cPJLC_q4114` (def) | PASS | Literal finite Fourier list or concatenation; expansion checked by ring. |
| pj-red; PairJet/Piece4c.lean:619 | `p11cPJC_q4114_0` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4c.lean:626 | `p11cPJC_q4114_1` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4c.lean:634 | `p11cPJC_q4114_2` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4c.lean:643 | `p11cPJC_q4114_3` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4c.lean:651 | `p11cPJC_q4114_4` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4c.lean:658 | `p11cPJC_q4114_5` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4c.lean:666 | `p11cPJC_q4114_6` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4c.lean:675 | `p11cPJC_q4114_7` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-red; PairJet/Piece4c.lean:683 | `p11cPJC_q4114_8` (def) | PASS | Literal Laplace coefficient combination; extracted by exact averaging. |
| pj-avg; PairJet/Piece4c.lean:690 | `p11cPJLN_q4114_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:695 | `p11cPJLN_q4114_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:700 | `p11cPJLN_q4114_2_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:705 | `p11cPJLN_q4114_3_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:710 | `p11cPJLC_q4114_0_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:715 | `p11cPJLC_q4114_1_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:720 | `p11cPJLC_q4114_2_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:725 | `p11cPJLC_q4114_3_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:730 | `p11cPJLC_q4114_4_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:735 | `p11cPJLC_q4114_5_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:740 | `p11cPJLC_q4114_6_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:745 | `p11cPJLC_q4114_7_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:750 | `p11cPJLC_q4114_8_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:755 | `p11cPJLC_q4114_9_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:760 | `p11cPJLC_q4114_10_ok` (theorem) | PASS | Finite charge check for list/chunks; no extra logical premise. |
| pj-avg; PairJet/Piece4c.lean:765 | `p11cPJ_q4114_neutral` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-avg; PairJet/Piece4c.lean:772 | `p11cPJ_q4114_charged` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-bin; PairJet/Piece4c.lean:782 | `p11cPJ_q4114_eq` (theorem) | PASS | Exact all-variable expansion by ring, stronger than physical specialization. |
| pj-avg; PairJet/Piece4c.lean:795 | `p11cPJ_q4114_avg` (theorem) | PASS | Exact finite Fourier averaging with full (2π)² factor. |
| pj-avg; PairJet/Piece4c.lean:831 | `p11cPJ_q4114_integrable` (theorem) | PASS | Integrability from continuous finite Fourier/kernel expression. |
| pj-formal; PairJet/PolyJet.lean:28 | `p11c_slowLength_sq` (theorem) | PASS | Exact polynomial scaling, evenness, analyticity or line-jet identity. |
| pj-formal; PairJet/PolyJet.lean:36 | `p11cPJP2` (def) | PASS | Literal homogeneous polynomial piece. |
| pj-formal; PairJet/PolyJet.lean:40 | `p11cPJP4` (def) | PASS | Literal homogeneous polynomial piece. |
| pj-formal; PairJet/PolyJet.lean:43 | `p11c_pairJet_smul` (theorem) | PASS | Exact polynomial scaling, evenness, analyticity or line-jet identity. |
| pj-formal; PairJet/PolyJet.lean:55 | `p11c_pairJet_neg` (theorem) | PASS | Exact polynomial scaling, evenness, analyticity or line-jet identity. |
| pj-formal; PairJet/PolyJet.lean:62 | `p11c_pairJet_analyticAt` (theorem) | PASS | Exact polynomial scaling, evenness, analyticity or line-jet identity. |
| pj-formal; PairJet/PolyJet.lean:88 | `p11c_pairJet_isJet` (theorem) | PASS | Exact polynomial scaling, evenness, analyticity or line-jet identity. |
| pj-bin / pj-formal; PairJet/Ray.lean:29 | `p11cPJF` (def) | PASS | Literal conjugate/rotated/inverse-square-root jet or actual integrand. |
| pj-bin / pj-formal; PairJet/Ray.lean:35 | `p11cPJconj` (def) | PASS | Literal conjugate/rotated/inverse-square-root jet or actual integrand. |
| pj-bin / pj-formal; PairJet/Ray.lean:39 | `p11cPJconj_ev` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:42 | `p11cPJ_isJet_conj` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:52 | `p11cPJ_tendsto_of_isJet` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:64 | `p11cPJ_isJet_inv_norm` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:123 | `p11cPJcJet` (def) | PASS | Literal conjugate/rotated/inverse-square-root jet or actual integrand. |
| pj-bin / pj-formal; PairJet/Ray.lean:129 | `p11cPJcJet_sq` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:137 | `p11cPJ_N_rot` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:149 | `p11cPJE_one` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:152 | `p11cPJE_neg_one` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:155 | `p11cPJS_sq` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:166 | `p11cPJrotN` (def) | PASS | Literal conjugate/rotated/inverse-square-root jet or actual integrand. |
| pj-bin / pj-formal; PairJet/Ray.lean:172 | `p11cPJrot` (def) | PASS | Literal conjugate/rotated/inverse-square-root jet or actual integrand. |
| pj-bin / pj-formal; PairJet/Ray.lean:175 | `p11cPJconj_refJet` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:180 | `p11cPJconj_add` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:184 | `p11cPJconj_smul` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:188 | `p11cPJconj_neg` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:191 | `p11cPJ_cos_two` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-bin / pj-formal; PairJet/Ray.lean:201 | `p11cPJ_ray` (theorem) | PASS | Jet algebra/limit identity; inverse-norm guards proved at physical call site. |
| pj-red; PairJet/Reduction.lean:26 | `p11cPJ_laplace_neg` (theorem) | PASS | Cosine evenness identifies signed Laplace indices. |
| pj-red; PairJet/Reduction.lean:33 | `p11cPJtab_1_0` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:45 | `p11cPJtab_1_1` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:58 | `p11cPJtab_1_2` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:71 | `p11cPJtab_1_3` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:84 | `p11cPJtab_2_0` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:97 | `p11cPJtab_2_1` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:110 | `p11cPJtab_2_2` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:123 | `p11cPJtab_2_3` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:137 | `p11cPJtab_2_4` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:152 | `p11cPJtab_3_0` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:166 | `p11cPJtab_3_1` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:179 | `p11cPJtab_3_2` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:193 | `p11cPJtab_3_3` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:208 | `p11cPJtab_3_4` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:223 | `p11cPJtab_3_5` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:238 | `p11cPJtab_4_0` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:252 | `p11cPJtab_4_1` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:266 | `p11cPJtab_4_2` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:281 | `p11cPJtab_4_3` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:296 | `p11cPJtab_4_4` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:311 | `p11cPJtab_4_5` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-red; PairJet/Reduction.lean:328 | `p11cPJtab_4_6` (theorem) | PASS | Guarded exact half-integer recurrence; rational identity. |
| pj-bin; PairJet/Rot.lean:30 | `p11cPJj1` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:33 | `p11cPJj2` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:36 | `p11cPJj3` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:39 | `p11cPJj4` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:45 | `p11cPJv` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:49 | `p11cPJN` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:58 | `p11cPJq22a` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:62 | `p11cPJq22b` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:66 | `p11cPJq44a` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:70 | `p11cPJq413` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:74 | `p11cPJq422` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:78 | `p11cPJq4112` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-bin; PairJet/Rot.lean:82 | `p11cPJq4114` (def) | PASS | Literal rotated jet/binomial piece on the full algebraic carrier. |
| pj-avg; PairJet/Terms.lean:27 | `PJTerm` (structure) | PASS | Literal coefficient/exponent data, no proof fields. |
| pj-avg; PairJet/Terms.lean:38 | `p11cPJKa` (def) | PASS | Literal monomial/list/charge/index formula. |
| pj-avg; PairJet/Terms.lean:43 | `p11cPJsum` (def) | PASS | Literal monomial/list/charge/index formula. |
| pj-avg; PairJet/Terms.lean:47 | `PJTerm.charge` (def) | PASS | Literal monomial/list/charge/index formula. |
| pj-avg; PairJet/Terms.lean:50 | `PJTerm.fourierIdx` (def) | PASS | Literal monomial/list/charge/index formula. |
| pj-avg; PairJet/Terms.lean:52 | `p11cPJE_pow` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |
| pj-avg; PairJet/Terms.lean:56 | `p11cPJKa_eq` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |
| pj-avg; PairJet/Terms.lean:80 | `p11cPJat` (def) | PASS | Literal monomial/list/charge/index formula. |
| pj-avg; PairJet/Terms.lean:84 | `continuous_p11cPJKa` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |
| pj-avg; PairJet/Terms.lean:101 | `p11cPJ_term_integral` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |
| pj-avg; PairJet/Terms.lean:113 | `p11cPJ_term_integral_charged` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |
| pj-avg; PairJet/Terms.lean:125 | `p11cPJat_integrableOn` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |
| pj-avg; PairJet/Terms.lean:145 | `p11cPJ_sum_integral` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |
| pj-avg; PairJet/Terms.lean:168 | `p11cPJ_sum_integral_charged` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |
| pj-avg; PairJet/Terms.lean:176 | `p11cPJ_sum_integral_neutral` (theorem) | PASS | Exact finite Fourier selection/integration; explicit produced continuity/charge guards. |

## Exact axiom output

Command: `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T5Probe.lean`
(exit 0). The probe contains the copied definition/body checks and signed theorem above,
followed by `#print axioms KAM.Planetary.<name>` for every theorem row in inventory order.
Its SHA-256 was `ba4b4602fb6feb55efae88b263644f03fbaf998d9aa6555a68891715c0dff843`.

```text
'KAM.Planetary.p11cPJ_avg0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_diag_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_diag_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pair_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJS_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJS_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJS_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJS_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJS_two_pi_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_integral_cell_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_add_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_neg_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_inner' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_integral_E' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_cell_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_cell_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_laplace' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJax_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_poincareV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_position' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_planeLength_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_pairPotential_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_action_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_perturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_secular_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mem_slowDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJscale_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJx_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_eventually_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_pairAverage_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJx_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_pairAverage_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu2_0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu2_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu2_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu2_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_avg2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_7' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_mu4_8' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_avg4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJequiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_poly_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_diag_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_jetEq_of_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_diag_comp_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_orbit_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_orbit_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJF4_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJG_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJF4_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_p11cPJW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_p11cPJW_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_iteratedFDeriv_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_e_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_diag_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJF_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q22a_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q22a_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22a_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22a_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22a_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22a_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22a_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q22b_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q22b_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22b_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22b_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22b_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22b_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q22b_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q44a_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q44a_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q44a_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q44a_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q44a_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q44a_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q44a_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q44a_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q413_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q413_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q413_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q413_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q413_2_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q413_3_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q413_4_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q413_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q413_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q413_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q413_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q413_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q422_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q422_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q422_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q422_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q422_2_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q422_3_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q422_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q422_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q422_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q422_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q422_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q4112_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q4112_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q4112_2_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4112_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4112_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4112_2_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4112_3_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4112_4_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4112_5_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4112_6_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4112_7_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4112_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4112_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4112_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4112_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4112_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q4114_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q4114_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q4114_2_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLN_q4114_3_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_0_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_1_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_2_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_3_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_4_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_5_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_6_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_7_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_8_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_9_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJLC_q4114_10_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4114_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4114_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4114_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4114_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_q4114_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_slowLength_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_pairJet_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_pairJet_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_pairJet_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_pairJet_isJet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJconj_ev' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_isJet_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_tendsto_of_isJet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_isJet_inv_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJcJet_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_N_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJS_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJconj_refJet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJconj_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJconj_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJconj_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_cos_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_ray' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_laplace_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_1_0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_1_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_1_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_2_0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_2_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_2_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_2_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_2_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_3_0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_3_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_3_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_3_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_3_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_3_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_4_0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_4_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_4_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_4_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_4_4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_4_5' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJtab_4_6' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJE_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJKa_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_p11cPJKa' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_term_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_term_integral_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJat_integrableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_sum_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_sum_integral_charged' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPJ_sum_integral_neutral' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scoped file hashes

| File | Lines | SHA-256 |
|---|---|---|
| `KAM/Planetary/PlanarTorsion/PairJet.lean` | 190 | `f0431cb3520a1c2895623239ef7e4546ad54f0d308e7c62e9e7fcbcc4ffb0ad5` |
| `KAM/Planetary/PlanarTorsion/PairJet/Average.lean` | 240 | `fcc57613d5134221ac87a114b92c4131ce2e3b99ed89f0455aa4c36827f67248` |
| `KAM/Planetary/PlanarTorsion/PairJet/Bridge.lean` | 286 | `844e9664c6e05eb9597d1d23542f537305ca1999ba4598af1d525bbf43290109` |
| `KAM/Planetary/PlanarTorsion/PairJet/Combine2.lean` | 134 | `43627bc4fe4ae52d0024a27423e39a6c721004d9b4b41e6f2ccfcfee572e9a20` |
| `KAM/Planetary/PlanarTorsion/PairJet/Combine4.lean` | 294 | `3deec59b0d30ddaffad16a1b7ecc9ddf757c5926f9efbc03a9443dd7281192ce` |
| `KAM/Planetary/PlanarTorsion/PairJet/Defs.lean` | 37 | `29dd4b65a41bc42245bc6ed9d0296df07bed50cb7616781af9c3f6d6424bbcc9` |
| `KAM/Planetary/PlanarTorsion/PairJet/Diag.lean` | 215 | `88cf725b5791b066564f775c5ee8ff13f58750f22c5b3d14f117c7e8c7161a09` |
| `KAM/Planetary/PlanarTorsion/PairJet/Diff.lean` | 365 | `c583c99248e880e2250358eeb1091e32152128a49077836438fea38541da3dde` |
| `KAM/Planetary/PlanarTorsion/PairJet/Piece22.lean` | 328 | `4859d1e635380fc9ef51d03741debe2ec63dce64e67a1ca1e66f0f1ef7892184` |
| `KAM/Planetary/PlanarTorsion/PairJet/Piece4a.lean` | 995 | `06ad3c445e5494c6a9383b8f2afd6e3e93ad1184b7a2a17c480c5dcb8f8db55c` |
| `KAM/Planetary/PlanarTorsion/PairJet/Piece4b.lean` | 630 | `3a0ccb7a7ff64388e294506b45b6125cc5c3142cb52a44057f0bd7c9c3a23a28` |
| `KAM/Planetary/PlanarTorsion/PairJet/Piece4c.lean` | 852 | `a95ebb2043659d33f741712bb58ba20da2eb34d8a24700ed0dc74c395fa2aa84` |
| `KAM/Planetary/PlanarTorsion/PairJet/PolyJet.lean` | 104 | `7eba204b7a71599325ea104db642ebf9fd93adf91762f938a0a4b32fe64d7f57` |
| `KAM/Planetary/PlanarTorsion/PairJet/Ray.lean` | 298 | `17118e3b1d65a449808fc16c56d15640e554d75db6361384d7c6d5cdd7accbc0` |
| `KAM/Planetary/PlanarTorsion/PairJet/Reduction.lean` | 347 | `b4ae47a7ca0653725757e70488208569d2360faf92e17a21035769a649b97127` |
| `KAM/Planetary/PlanarTorsion/PairJet/Rot.lean` | 88 | `bf3dca7a2c5667dfe7ffeba51a4a9192f841f4787bf12e74e4427f0173af8fed` |
| `KAM/Planetary/PlanarTorsion/PairJet/Terms.lean` | 188 | `3b526ab67bd7d267eb76650539fd2fcaec7426f25203d628ade89e2354d1e912` |

## Closeout and limitations

The audit covers the signed T5 surface and its local proof dependencies/consumption. T2, T3,
T4, Part-8, and diagonal polarization modules are upstream dependencies, not independently
re-audited packages here. No draft frozen theorem is imported or promoted. No frozen proof
body was changed. Blueprint alpha-series and quadratic Laplace consistency remain T4's
assigned share; physical eccentricity conversion and secular quartic extraction belong to T6.
No suspected pinned-source defect, introduced statement deviation, unresolved proof assumption,
or unauthorized resource override was found in T5. The generated-root update remains an orchestrator integration follow-up. No source repair, git state change or external messaging
was performed. Temporary probe files are removed after recording their results.
