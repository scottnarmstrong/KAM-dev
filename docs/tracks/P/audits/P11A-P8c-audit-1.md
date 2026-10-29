# Independent audit: P11A-P8c (audit 1)

**Verdict: PASS WITH NOTES for the authorized P8c parametric package.** No frozen anchor is proved or seal-ready in this slice. In particular, this verdict does not certify the signed `amount`, the parent graph node as a completed physical-data theorem, or P-FIXED.

Audited HEAD: `41efd537b14e63ff5577934a42b75e7715b4aaee`.
Comparison ref `inp`: `c2be145a358746329fa8147c2f951d8bfc7ecbfb`.
Only `KAM/Planetary/Preparation/AmountCore.lean` is substantively audited, as required by AUDIT FOCUS. Report location follows the user's explicit worktree path, overriding the generic brief's MAIN-worktree destination. No repository source was edited.

## Authority and comparison

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external package-audit brief, P11A-P8c-handoff.md including its overnight split ruling, P11A-LEAN-DESIGN.md (node table and amount steps), graph records at docs/graph/P/DEPGRAPH.md:20739–20858, blueprint-P/parts/p11-cp09-preparation.tex:214–222, track P statement, and the external P11ASignatures.lean entries for p11JetBound, P11PreparedFullSpec and amount. Checked the physical endpoint frozen FixedSunPlanetaryKAM statement and the definitions/interfaces actually used by AmountCore.

`git diff inp...HEAD` warns:

```text
warning: inp...HEAD: multiple merge bases, using a2464f937a8b578ae414ec08331359284ec94a78
```

The two merge bases are `a2464f937a8b578ae414ec08331359284ec94a78` and `11a05936187b0e9191a65fbbab67b3ba7ea89048`. The requested three-dot comparison has 14 files, 3067 insertions and one deletion: AmountCore plus inherited PreparedData/P7d preparation and prior audit documentation. `git diff --name-only b83f55d8..HEAD` contains only AmountCore. This explains the inherited scope; this audit does not certify those other modules.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (apart from the merge-base warning). `git diff --check inp...HEAD` exits 0.

## Declaration and node review

All names below are in `KAM.Planetary`; locators refer to AmountCore.lean. PASS for auxiliary declarations means correct for their stated interface, not a new signed source theorem.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| definition | `p11DiagVec` (L36) | PASS | Literal diagonal map on every vector, including n=0; no fallback. |
| am-norm helper | `p11dot_diagVec` (L39) | PASS | Diagonal self-adjointness for the literal coordinate dot product. |
| am-norm helper | `p11euclid_sq_sum` (L45) | PASS | Euclidean square is the coordinate sum of squares. |
| am-norm helper | `p11euclid_diagVec_sq` (L49) | PASS | Exact squared diagonal norm formula. |
| am-norm helper | `p11euclid_diagVec_bounds` (L56) | PASS | Required lower bound eps² for unit c; positivity and eps≤1 explicit. |
| am-norm helper | `p11dot_smul_left` (L69) | PASS | Exact homogeneity. |
| am-norm helper | `p11maxJet_smul_ge` (L74) | PASS | Nonnegative homogeneity inequality; smoothness at the evaluation point explicit. |
| stepP:p11:am-norm | `amount_norm` (L89) | PASS | Literal eps² amount inequality, general input dimension d; no compactness needed. |
| assembly helper | `index_def_anti` (L129) | PASS | Correct antitonic direction; nonempty smaller set and positive target dimension explicit. |
| assembly helper | `index_def_congr` (L134) | PASS | Germ equality on an open neighbourhood, hence equality of all jets and amounts. |
| stepP:p11:am-dir | `amount_dir` (L165) | PASS | Literal betaJ/2 lower bound, from stability with rho=2 and the displayed smallness. |
| definition | `p11Inl` (L185) | PASS | Literal continuous linear inclusion r↦append r 0 on the whole carrier. |
| slice helper | `p11Inl_apply` (L198) | PASS | Definitional inclusion formula. |
| slice helper | `p11_append_eq` (L200) | PASS | Exact affine decomposition of append. |
| slice helper | `p11euclid_inl` (L207) | PASS | Preserves Euclidean unit directions. |
| slice helper | `p11_iteratedFDeriv_slice` (L215) | PASS | All tuples of directions, including order zero; open-domain chain rule. |
| slice helper | `p11dg_slice_le` (L245) | PASS | Slice diagonal gauge bounded by the ambient gauge using the isometric inclusion. |
| slice helper | `p11_slice_chart` (L255) | PASS | Constructs an open inverse-chart domain containing the complete affine image of R. |
| stepP:p11:am-scale | `amount_scale` (L284) | PASS | Pointwise unit-c conclusion eps^mu*b; stronger than its infimum consequence. Chart scaling supplies the eps^j identities; slice inclusion embeds the directions. |
| bpP:p11:amount, parametric combination only | `amount_transfer` (L330) | PASS | Exact (1/2)*eps^(mu+2)*betaJ lower bound; signed amount and its fixed-data thresholds deferred to P8e by ruling. |

There are no signed declarations in this file and no provider exports. Frozen/provider type-equality and candidate seal-body probes are therefore inapplicable. The signed `amount` in P11ASignatures.lean:1135–1141 is intentionally absent: it chooses fixed-data constants, uses the same selected `p11PreparedData`, returns `P11PreparedFullSpec`, and bounds the amount of `p11PreparedFreqR`. The differently named `amount_transfer` is an authorized conditional helper and does not claim that signature.

The eps² scalar-family identity is established inside amount_norm (L103–109), with a normalized Euclidean unit coefficient and s>0. The lower diagonal norm bound suffices for the claimed eps² conclusion. The explanatory blueprint also writes |Dc|≤1; this unused auxiliary upper bound is not separately exported or invoked here. No downstream estimate relies on it. In the scaling step the chain rule and eps^j gauge identities are supplied by the checked ChartScaling dependency, and p11_iteratedFDeriv_slice supplies the ambient direction identity. The pointwise amount_scale bound and the infimum argument inside amount_transfer establish the required eps^mu loss uniformly in the frozen rho. The final ring identity multiplies this by eps², without changing the order or the 1/2 factor.

## Definitions and P8e applicability

The only new definitions are p11DiagVec and p11Inl. Both are literal coordinate constructions on their entire carriers, with exposed bodies under the exposed public section; neither uses choice, a conditional default, a selected extension, or derivative junk. p11Inl is a genuine continuous linear map for the Pi topology and an isometry for the explicit Euclidean length. All public declarations remain in KAM.Planetary; no root declaration is introduced. A repository-wide declaration-name scan found no reused short name among these 20 declarations. The previous p11euclid_sq clash was removed by the committed rename to p11euclid_sq_sum.

The parametric hypotheses match the prepared interfaces as follows:

- Take mu=(p11PatchData D).mu, W=Q.checkW, J0=(p11SecularData D).J0, varpi=(p11PatchData D).varpi, betaJ=(p11PatchData D).beta, and R=Rho=the n-dimensional closed half cube. K is p11PreparedBox n, literally the (n+n)-dimensional half cube (SlowData.lean:34–35). Its head and tail satisfy hK, and all these boxes are compact/nonempty.
- `he` is exactly the vector difference of the unscaled J slice and varpi, in `p11JetBound true mu`, with all orders j≤mu including zero. P11PreparedFullSpec (PreparedData.lean:85–105; signature:1103–1124) provides this on the open J ball for every rho with Pi norm <5/4. Restricting its point quantifier to A=(J0+eps•·)''R discharges he once A lies in that ball. No replacement by C0 closeness, operator jets, or scaled-r derivatives occurs.
- For small positive eps, the half cube has norm at most 1/2<5/4. Choose an open neighbourhood U containing the box with tail norm <5/4 and unscaled head within the J ball. Smoothness of Q.checkW there must be obtained from its equality with p11SlowNormalizedFreq and analytic derivatives of h0+g2. This is actual remaining P8e proof work; P11PreparedFullSpec contains the identification, not a literal ContDiffOn field. P8c neither proves that bridge nor silently assumes it as a completed signed result. The explicit split ruling permits this premise.
- The base map is analytic on the patch open set by P11PatchSpec (Working.lean:96–111). The holo-chart bounds in Holomorphic.lean:73–97 give the derivative bounds and J0 interior to the patch compact. P8e must derive a finite dimension/order conversion L1 for the Euclidean diagonal jets, restrict to A, and obtain hbeta using index_def_anti with A⊆patch.K. The helper permits any such L1, with no dependence of a newly selected constant hidden in its conclusion.
- P8e must choose eps≤1 and small enough for A⊆patch.K, A inside the J domain, and 2^mu*theta*(2*L1+theta)≤betaJ/2, with theta=c3*eps*log(1/eps)^Q. These are the literal blueprint smallness/geometry requirements. The helper fixes them as explicit inputs; it does not supply uniform thresholds.
- The diagonal identification in P11PreparedSpec (PreparedData.lean:61–64) holds on ‖y‖≤5/4. To identify amounts, use index_def_congr on the OPEN ball of radius 5/4, which contains the half cube; pointwise agreement on the closed cube alone would not identify derivatives. This pays the exact output-map bridge without a global identity hypothesis.

No conclusion-shaped premise is added under the P8c split: hbeta concerns the original varpi, he is the prepared closeness estimate, and hW is the permitted smoothness bridge. amount_scale's lower bound b is the explicit intermediate result supplied by amount_dir; amount_transfer discharges that step rather than assuming its own target amount. Positivity of betaJ is not required by the conditional inequalities, so they are slightly more general; positivity of the signed beta_epsilon remains P8e work.

## Independent validation

All Lean/Lake commands below were serialized and used LEAN_NUM_THREADS=1 and nice -n 5. No heartbeat, recursion or synthesis-budget override was used.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8c KAM.Planetary.Preparation.AmountCore
```

Exit 0. Relevant output:

```text
[inp-gate] slot 2 acquired 01:14:48 for KAM.Planetary.Preparation.AmountCore
Build completed successfully (9052 jobs).
```

Replayed dependencies Stability and ChartScaling emitted unused-variable and deprecation warnings; AmountCore emitted none. Those warnings do not change the checked signatures.

2. Untracked scratch axiom probe imported only AmountCore and issued `#print axioms KAM.Planetary.<name>` for every theorem in the declaration table:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP8cAudit.lean
```

Exit 0; complete output:

```text
'KAM.Planetary.p11dot_diagVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11euclid_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11euclid_diagVec_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11euclid_diagVec_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dot_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11maxJet_smul_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amount_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.index_def_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amount_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Inl_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_append_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11euclid_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_iteratedFDeriv_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dg_slice_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_slice_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amount_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amount_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.AmountCore
```

Exit 0. Output:

```text
replaying KAM.Planetary.Preparation.AmountCore
```

There is one audited lemma module and no provider module, so this single-module invocation covers every new proof body.

4. Project import closure, obtained recursively from local imports:

```text
KAM/Fourier/Derivative.lean
KAM/Nekhoroshev/Interfaces/Norms.lean
KAM/Planetary/Preparation/AmountCore.lean
KAM/Planetary/WeakMeasure/Basic.lean
KAM/Planetary/WeakMeasure/ChartScaling.lean
KAM/Planetary/WeakMeasure/Stability.lean
Provider/frozen theorem imports: []
```

There are no imported DRAFT_SORRY anchors or providers to justify through manifest state. A code-mask scan found zero forbidden-token matches (sorry, admit, axiom, unsafe, opaque, EuclideanSpace, set_option). The file has 373 total lines and maximum Unicode line width 100. Copyright, module command, public imports, module docstring, exposed public noncomputable section, and closing module end are present.

5. Lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly permitted generated-root mismatch. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1192 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No generated root was regenerated. No forbidden-token, size, line-width, errata-rendering, module, anchor, or ABI failure was reported.

## Uncertainties, defects and deviations

No suspected defect in a pinned source was discovered within this slice. No source was fetched from the web or substituted. No frozen definition, law, norm, carrier, index order, or signature was changed. The actual source material assessed here is the local pinned blueprint/design/signature contract; this is not a new independent recheck of CP09's PDF.

The parent amount node and signed theorem remain outside this P8c completion. Their positive coefficient, constant quantifier order, selected-Q FullSpec, actual prepared-frequency attachment, and fixed-data eps threshold must be checked when P8e is assembled. The stale graph LEAN_STATUS entries are not updated in this report-only audit. The handoff's older 369-line count is superseded by the live 373-line file; its statement that only ChartScaling is imported omits the explicit public Mathlib import, which has no quarantine consequence.

Only the requested audit report is added; the pre-existing untracked handoff is retained. The scratch axiom probe is removed after validation. No state-changing git command was used.
