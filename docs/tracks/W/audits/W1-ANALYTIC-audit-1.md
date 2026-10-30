# W1-ANALYTIC independent audit 1

**Overall: FAIL against the complete blueprint-node and package-hygiene contract.** The implemented analytic core is **PASS WITH NOTES**: its new theorems have clean axioms, all 14 modules build and kernel-replay, and the focused analytic statements match the current `inp` blueprint. Two retained failures prevent a full package PASS: the commutation part of `complexification-lemma` (i) is missing, and the branch changes protected generated files. Neither finding is a counterexample to the implemented analytic estimates. No provider, seal, or newly proved frozen theorem is involved; seal readiness is N/A.

## Scope, frozen inputs, and authority

Audited 2026-10-30 in `/root/code/KAM-inp-wpd`, report-only authority from the user. The report location in the generic brief is superseded by the user's exact absolute path. The handoff's AUDIT FOCUS supersedes provider/seal probes and selects the SLIM lint wrapper. No production source, frozen file, manifest, generated root, or git history was edited by this auditor. Temporary probes and evidence are under `.lake/abi-scratch/` and are deleted after their evidence is embedded here.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/W/audits/W1-ANALYTIC-handoff.md`. There is no `docs/tracks/W/statement.md`; consulted `docs/tracks/W/W-STATEMENTS.md`, the actual SEALED definitions and manifest instead. The statements document's stale DRAFT banner does not override the manifest.

- Package HEAD: `c87c7a34db8e1e56aacb97a01d60c8a659271955`.
- `inp` at audit start: `d600c634e77f75013abaa6c27c985139e888f8c5`.
- Merge base: `003c5a3a04b09690bc03ab763b69e159641da2b4`.
- Reviewed the full `git diff inp...HEAD`: 17 files, 1,956 added lines; the 14 analytic modules are all additions. The diff also adds the handoff and generated `KAM/Root/Wave.lean`, and changes `KAM.lean`.
- Source: `inp:blueprint-W/parts/w1-sequences.tex`, blob `ace707ffb486c5bc736f23567ab0cf9060d84389`, SHA256 `b27ab7134c188941198e547c4577e3263e0e5f618a41ebd6983ac48b8b07e796` at the pinned start revision. The subsection `bpW:w1:analytic` through the next subsection is byte-identical in the worktree and pinned `inp`, SHA256 `9713bb61cd1148a634d85d9d8ac5a20a0ed436b97cb5e60c900f07ad2da60f25`. Source lines below refer to that `inp` snapshot (708–924), not the older branch's shifted line numbering.
- Consumer definitions: `wave.WaveSpace.v1`, `wave.IsAnalyticTorusEmbedding.v1`, and `kam.complexStrip.v1` are SEALED. Their files match the manifest's full-file SHA256 values; frozen and manifest diffs are empty.

Method: focused source-correspondence audit, tier 2. First reconstructed source hypotheses and conclusions, then inspected all added declarations/bodies and the complete diff, attempted to refute suspected mismatches by inspecting source guards and possible renamed support, and finally ran serialized mechanical checks. No new agent was launched. Findings below describe the explicit adversarial recheck; this is one independent auditor, not a second-person review of its own findings.

## Findings and refutation attempts

### F1 — incomplete blueprint node: FAIL

Source `bpW:w1:complexification-lemma` (i), pinned `inp` lines 721–723: **“All three commute with \(\tau_{a,p}\), \(\kappa_{a,p}\) and every real multiplier \(D_\mu\).”** No theorem proves those commutations in the package. `ComplexificationLp.lean:53–120` supplies the coordinate formulas, norms, left inverse, conjugate linearity, and square-norm identity, but no transport/multiplier compatibility. The handoff's “Not done / caveats” explicitly confirms this omission.

Refutation attempt: searched the new modules and existing `KAM/Wave` and `KAM/Frozen/Wave` for the operator names, commutation statements and generic substitutes; inspected `lpPointwise`, `conjLp_smul`, and all concrete coordinate formulas. `conjLp_smul` proves scalar compatibility, not compatibility with the weighted-coordinate maps or an arbitrary sequence multiplier; the formula lemmas do not themselves constitute the missing theorem. The handoff explains that the operators are in other unmerged packages. This explains the omission but does not close it. **SURVIVED** as a completion gap, not as a false theorem. Close by proving the actual commutation statements after those operators land, or obtain an explicit scope split; do not mark the entire node done meanwhile.

### F2 — protected generated-path delta: FAIL

The exact gate `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is nonempty: `KAM.lean:32` adds `public import KAM.Root.Wave`. The new `KAM/Root/Wave.lean:1–30` is also protected by AGENTS hard rule 10. The handoff expressly says both were regenerated.

Refutation attempt: inspected the entire delta and the headers: these really are generated import changes, not changes to mathematical content; no frozen file, manifest file or README change is present. The brief only exempts an expected **lint diagnostic** “KAM.lean is out of date”; it does not exempt a committed protected-path delta. The AUDIT FOCUS changes the lint command but does not grant that exemption. **SURVIVED** as a workflow/hygiene failure. Orchestrator should remove these deltas from the submitted package or record explicit authorization; this auditor leaves them untouched.

### Notes which did not become findings

- `FlowHyp.M_pos` is SOURCE, not EXCESS. The current source at `inp:866–867` says “where \(0<M<\delta\) (so \(\delta>0\))”. `FlowHyp` records exactly these inequalities. Omitting explicit `U ⊆ V` strengthens the theorem harmlessly: `margin` and `delta_pos` imply it.
- The flow has `HasDerivWithinAt` on `Icc (-1) 1`, continuous trajectory, and continuous right-hand side `X ∘ trajectory`. This is the correct closed-interval C¹ meaning, including one-sided derivatives at the endpoints. The series extension outside this interval is not asserted to be a differentiable flow there. Uniqueness tests all solutions in `V`, not just solutions assumed to stay in the smaller ball.
- The derivative bound on Picard iterates is proved directly by exponential integration rather than exporting the blueprint's sharper finite exponential sum. That sharper intermediate bound is not needed for any claimed final conclusion.
- `degreeSeries` averages all words of a given multiplicity rather than selecting a nondecreasing word. The off-diagonal multilinear map therefore differs from the blueprint's displayed proof construction, but its diagonal polynomial and norm estimate are proved, exactly as required by the existential power-series statement. This is a disclosed proof-construction deviation, not a missing source conclusion.
- Handoff says maximum file length 201; actual maximum is 202 physical lines (`HoloAnalytic.lean`). It remains far below 1,500.

## Node verdicts

All declaration names below have prefix `KAM.Wave.`.

| Blueprint node | Lean declaration(s) | Verdict | Reason |
|---|---|---|---|
| complexification | `complexifyLp`, `reLp`, `conjLp`, `WaveSpaceC`, `complexifyWave`, `reWave` | PASS | Exact coordinate maps and product representation; no fallback. |
| complexification-lemma (i) | concrete coordinate/norm/inverse/conjugation theorems | FAIL for full clause; implemented subset PASS | F1: commutation with weighted maps and multipliers absent. |
| complexification-lemma (ii) | `analyticAt_comp_realLinear` | PASS | General real-linear pre/postcomposition; completeness not needed (stronger). |
| complexification-lemma (iii) | `analyticAt_real_part` | PASS | Analyticity, local recovery, exact real derivative; general split pair. |
| holomorphic | Mathlib `DifferentiableOn ℂ` | PASS | Uses existing definition, no new surrogate predicate. |
| cauchy | `norm_fderiv_le_div_of_ball`, `norm_fderiv_le_div_of_ball_subset`, `lipschitz_of_margin` | PASS | Positive radii, nonnegative bound, correct operator norm, pointwise bounds. Domain/target completeness not required (stronger). |
| deriv-continuous | `norm_fderiv_sub_le_holoMargin`, `continuousOn_fderiv_of_holomorphic` | PASS | Exact `2 * B * (ρ^2)⁻¹`, half-radius inner ball; local boundedness derived from continuity. |
| uniform-limit (i) | `holomorphic_of_tendstoUniformlyOn`, `mem_of_tendstoUniformlyOn` | PASS WITH NOTES | No bound on limit; derivative convergence with doubled-ball margin. Reality generalized to closed sets; closedness for concrete ℓ² inclusion was proved in scratch. |
| uniform-limit (ii) | `norm_fderiv_le_div_of_tendstoUniformlyOn` | PASS | Only this part adds `M ≥ 0` and a pointwise bound for the limit; positive margin. |
| holo-analytic-fd | `analyticOnNhd_of_differentiableOn_banach`, `holomorphic_fd_power_series`, `holomorphic_real_part_analytic` | PASS | Arbitrary Banach target, n=0 qualitative; n≥1 enlarged radius, absolutely summable coefficients, correct binomial estimate and HasFPowerSeriesOnBall. |
| torus-analytic | `torus_analytic` | PASS | Correct period-one strip and real inclusion; exact analyticity conjunct consumed in a compiled frozen-predicate composition probe. Does not claim embedding injectivity. |
| flow (i) | time derivative, integral identity, initial value, displacement, ball membership, uniqueness exports | PASS | Source premises only, endpoint interpretation and V-valued uniqueness verified. |
| flow (ii) | `holomorphicOn_holoFlow`, `norm_fderiv_holoFlow_le` | PASS | Exact holomorphy and `exp (M / δ * abs t)` estimate. |
| flow (iii) | `holoFlow_mem_range` | PASS WITH NOTES | Abstract split closed real subspace; concrete inclusion has continuous left inverse and closed range. No new reality axiom is needed. |
| flow (iv) | `norm_holoFlow_sub_holoFlow_le` | PASS | Two fields with common source hypotheses, `N ≥ 0`, correct `abs t * exp (M / δ * abs t) * N`. |

## Binder and hypothesis audit

SOURCE = explicit source condition; TYPING = carrier, point or coefficient data; STANDING = independently fixed source convention. RULED and EXCESS counts for the source-facing exports are zero. Generic internal auxiliary lemmas are assessed at their advertised conditional types, not substituted for source results.

| Export / expanded logical binder | Bin | Source or reason |
|---|---|---|
| `FlowHyp.isOpen_V` | SOURCE | flow: V open |
| `FlowHyp.isOpen_U` | SOURCE | flow: U open |
| `FlowHyp.holo` | SOURCE | flow: X holomorphic on V |
| `FlowHyp.bound` | SOURCE | flow: pointwise norm bound M |
| `FlowHyp.margin` | SOURCE | flow: doubled ball in V |
| `FlowHyp.M_pos` | SOURCE | flow: 0 < M |
| `FlowHyp.M_lt` | SOURCE | flow: M < δ |
| flow `F` | TYPING | complex Banach target |
| flow `[NormedAddCommGroup F]` | TYPING | Banach carrier |
| flow `[NormedSpace ℂ F]` | TYPING | complex scalar structure; induced real structure used consistently |
| flow `[CompleteSpace F]` | TYPING | source Banach completeness |
| flow `X` | TYPING | vector field |
| flow `V` | TYPING | outer domain |
| flow `U` | TYPING | initial-point domain |
| flow `M` | TYPING | source bound parameter |
| flow `δ` | TYPING | margin parameter |
| flow `w` | TYPING | initial point |
| flow `t` | TYPING | real time |
| flow `hw` | SOURCE | w ∈ U |
| flow `ht` | SOURCE | abs t ≤ 1, represented as interval membership |
| uniqueness `γ` | TYPING | comparison curve |
| uniqueness `hγd` | SOURCE | curve solves the same ODE |
| uniqueness `hγV` | SOURCE | values in V |
| uniqueness `h0` | SOURCE | common initial value |
| reality `G` | TYPING | underlying real space |
| reality `[NormedAddCommGroup G]` | TYPING | real carrier |
| reality `[NormedSpace ℝ G]` | TYPING | real scalar structure |
| reality `[CompleteSpace G]` | TYPING | real Banach space being complexified |
| reality `ι` | TYPING | real inclusion |
| reality `re` | TYPING | real projection |
| reality `hre` | STANDING | split inclusion property; concrete theorem `reLp_complexifyLp` |
| reality `hclosed` | STANDING | real subspace closed; proved for concrete inclusion in probe |
| reality `hX` | SOURCE | X real on reals in V |
| reality `hwR` | SOURCE | real initial point |
| parameters `Y` | TYPING | second member of the field family |
| parameters `hY` | SOURCE | seven identical FlowHyp source conditions, listed above |
| parameters `N` | TYPING | field-difference bound |
| parameters `hN` | SOURCE | 0 ≤ N |
| parameters `hXY` | SOURCE | pointwise difference bound throughout V |
| torus `s` | TYPING | geometric width |
| torus `hs` | SOURCE | 0 < s |
| torus `Kt` | TYPING | complex extension |
| torus `hK` | SOURCE | holomorphic on strip |
| torus `hreal` | SOURCE | real on reals |
| torus `hper` | SOURCE | integer period in every coordinate |
| Cauchy `hr` / margin `hδ` | SOURCE | radius strictly positive |
| Cauchy `hM` | SOURCE | M ≥ 0 |
| Cauchy `hf` | SOURCE | differentiability on indicated domain |
| Cauchy `hbd` | SOURCE | bound on every point of domain |
| margin `hw` | SOURCE | ball inclusion |
| Lipschitz `hV` | SOURCE | open V |
| Lipschitz `hC` | SOURCE | convex C |
| Lipschitz `hCV` | SOURCE | δ-margin at each point of C |
| derivative continuity `hU` | SOURCE | U open |
| derivative continuity `hf` | SOURCE | holomorphic f |
| derivative estimate `hρ` | SOURCE | ρ positive |
| derivative estimate `hB` | SOURCE | B ≥ 0 |
| derivative estimate `hsub` | SOURCE | double-radius ball in U |
| derivative estimate `hbd` | SOURCE | pointwise local bound |
| derivative estimate `hw` | SOURCE | w in half-radius ball |
| derivative estimate `hw'` | SOURCE | w' in half-radius ball |
| uniform limit `hU` | SOURCE | U open |
| uniform limit `hf` | SOURCE | all sequence members holomorphic |
| uniform limit `hg` | SOURCE | uniform convergence on U |
| derivative convergence `hδ` | SOURCE | δ positive |
| derivative convergence `hw` | SOURCE | double-radius ball in U |
| quantitative limit `hM` | SOURCE | M ≥ 0 |
| quantitative limit `hbd` | SOURCE | bound on limit on U |
| quantitative limit `hδ` | SOURCE | δ positive |
| quantitative limit `hw` | SOURCE | single-radius ball in U |
| closed-set limit `hR` | STANDING | closedness of generalized real subspace |
| closed-set limit `hS` | TYPING | selected real-point set contained in U |
| closed-set limit `hfR` | SOURCE | all sequence values real on selected real points |
| finite-dimensional analytic `hU` | SOURCE | U open |
| finite-dimensional analytic `hf` | SOURCE | holomorphy |
| quantitative power series `hn` | SOURCE | n ≥ 1 |
| quantitative power series `hr` | SOURCE | r > 0 |
| quantitative power series `hcl` | SOURCE | closed polydisc inclusion |
| real analytic clause `hre` | STANDING | split complexification |
| real analytic clause `hreal` | SOURCE | real on real points in U |

Rows are per named premise on each distinct source surface; repeated flow fields are expanded once and reused at their appearances. For the seven FlowHyp fields: SOURCE=7, STANDING=0, TYPING=0, RULED=0, EXCESS=0. For all logical inputs in the source-facing results, EXCESS=0 and RULED=0. Remaining implicit norm/scalar instances and free variables in the Cauchy/uniform-limit/power-series lemmas are TYPING; there is no second-countability input on the Banach target. Constants have exactly source dependence: Cauchy `M/r`, derivative continuity `2B/ρ²`, flow `L=M/δ`, and witnesses `r₁,M₁,c,p` chosen after f and the closed polydisc as allowed by the source.

`PicardInv` contains the differentiability/bound/continuity being established by induction. Helpers taking `hk : PicardInv ... k` are explicitly conditional induction-step lemmas, distinct from the source theorem. `picardInv_zero` and `picard_holo` construct the bundle for every k; no final flow export assumes it. Likewise generic Gronwall and integral helpers receive their ordinary problem data as hypotheses; their source consumers supply these data in the proofs.

## Definition classification and whole-carrier inspection

| Definition / structure | Body, carrier and characterization assessment |
|---|---|
| `lpPointwise` | Literal continuous real-linear map on every ℓ² input. Membership is proved from the norm-nonincreasing hypothesis, not asserted by an instance. |
| `complexifyLp` | Literal coordinate inclusion on all real ℓ²; no branch or choice. |
| `reLp` | Literal coordinate real part on all complex ℓ²; no branch or choice. |
| `conjLp` | Literal coordinate conjugation on all complex ℓ²; involutive, conjugate-linear and isometric, proved. |
| `WaveSpaceC` | Literal product of two complex ℓ² spaces, max product norm; matches frozen weighted-coordinate convention. |
| `complexifyWave` | Literal product map of inclusions, on entire WaveSpace. |
| `reWave` | Literal product map of real parts, on entire WaveSpaceC; proved left inverse. |
| `wordCount` | Literal finite coordinate multiplicities; all n,m including zero. |
| `wordFiberCard` | Literal finite cardinality; zero for unrealizable multiplicities is intended, not a substitute coefficient. |
| `wordTerm` | Literal continuous multilinear coordinate product times vector, including degree zero. |
| `degreeSeries` | Literal finite weighted sum of word terms; the inverse cardinality is evaluated only at `wordCount σ`, whose fiber contains σ. `wordFiberCard_pos` proves positivity for each degree-compatible α. No zero-denominator fallback is used. |
| `FlowHyp` | Prop bundle of seven SOURCE conditions, not a conclusion package. Delta positivity and Lipschitz control are proved from it. |
| `wavePicard` | Literal primitive recursion with Bochner interval integrals, on all X,w,k,t. Integrals are total Mathlib functions; arbitrary off-source X need not define genuine integrable trajectories. Under FlowHyp, w∈U, abs t≤1, continuity/integrability and ball containment are proved before using the recursion analytically. |
| `picardD` | Literal Mathlib fderiv of the Picard iterate. fderiv's default off differentiability is not used: `PicardInv.diff`, ultimately proved by induction, supplies differentiability at every analytic use. |
| `picardG` | Literal composition `DX(φ_k) ∘ Dφ_k`; both derivative factors are justified at every point of use. |
| `PicardInv` | Explicit induction invariant; conditional helpers remain conditional, and the unconditional-in-k producer is proved. No source result assumes this invariant. |
| `holoFlow` | Literal Picard increment series `w + ∑' k, (φ_{k+1}-φ_k)`. On the source locus its norm-majorant summability, convergence to the iterates, integral identity, derivative, and uniqueness are all proved. The raw total formula exists outside that locus; a divergent tsum then has Mathlib's default value and is not certified as a dynamical flow. |

For the unconditional literal coordinate/finite-sum objects: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS/CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A. For the flow construction, the raw integral/series recipes are total constructions, but **flow semantics are certified only on the source domain** `(FlowHyp X V U M δ, w∈U, abs t≤1)`. This report does not certify a unique solution for arbitrary X,w,t. Under the brief's explicit test (“Junk values or fallbacks that a theorem relies on fail”), no source-facing theorem was found to rely on a nonintegrable integral, divergent tsum, or nondifferentiable fderiv default. A consumer must retain those guards. An unconditional, whole-carrier interpretation of the name `holoFlow` would fail this audit.

Additional local branches inspected: `exists_separable_lift` constructs a lift equal to f on U and zero outside U. This is an existential auxiliary extension, not a new global source object; all uses transfer back only on U and use openness to justify local derivative equalities. Uniform-limit proof's `choose!` selects derivative limits only on the stated ball; uniqueness of derivatives identifies them with `fderiv` there, and no off-ball value enters an exported conclusion.

## Focused mathematical and consumer checks

The Cauchy proof obtains bounds on smaller closed balls then passes to the open radius; it needs neither a supremum nor compactness of the target. Uniform convergence is qualitative first; its proof obtains a uniformly Cauchy derivative sequence and uses completeness only when forming the derivative limit. Reality passes through a closed set. The enlarged polydisc and bound in `holomorphic_fd_power_series` are outputs, not hidden premises: separable reduction handles arbitrary Banach targets, finite-dimensional compactness handles the domain, and the coefficient series is explicitly absolutely summable. The n=0 result is an actual application of the generic analytic theorem, confirmed in Lean with an arbitrary Banach target and no second-countability instance.

The flow margin audit follows `FlowHyp.ball_subset_V`: for z∈B(w,δ), B(z,δ)⊆B(w,2δ)⊆V. All Picard iterates, the flow, and any competing V-valued solution move by at most M abs t < δ. Thus the field's Lipschitz bound is used only on the common convex B(w,δ), including the two-field parameter comparison. The proof never assumes V convex or a globally finite norm of DX on V.

The frozen `IsAnalyticTorusEmbedding` body (`KAM/Frozen/Wave/Defs/IsAnalyticTorusEmbedding.lean:33`) requires periodicity followed by `AnalyticOnNhd ℝ K Set.univ`, with K on `Fin 2 → ℝ`. `torus_analytic` produces that exact analytic proposition and period-one periodicity, using `KAM.complexStrip 2 s` = coordinatewise imaginary widths < s and `KAM.realInclusion 2`. A compiled scratch example assembles these into the actual frozen predicate while supplying its two independent injectivity obligations separately. This verifies the analytic/periodic attachment only; neither injectivity nor W6/W8 theorem closure is claimed.

## Verification

Every Lean/Lake invocation used `LEAN_NUM_THREADS=1`, `nice -n 5`, and was completed before starting the next. No heartbeat, recursion-depth or synthesis-budget override, clean, cache fetch, package mutation, or library-wide build was used. The targeted build reused existing artifacts.

Let `MODULES` be the following exact arguments, in this order:

```text
KAM.Wave.Analytic.Cauchy
KAM.Wave.Analytic.Complexification
KAM.Wave.Analytic.ComplexificationLp
KAM.Wave.Analytic.DegreeSeries
KAM.Wave.Analytic.Separable
KAM.Wave.Analytic.HoloAnalytic
KAM.Wave.Analytic.UniformLimit
KAM.Wave.Analytic.TorusAnalytic
KAM.Wave.Analytic.Flow.Integral
KAM.Wave.Analytic.Flow.Gronwall
KAM.Wave.Analytic.Flow.Picard
KAM.Wave.Analytic.Flow.PicardHolo
KAM.Wave.Analytic.Flow.Limit
KAM.Wave.Analytic.Flow.Holomorphic
```

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpd $MODULES`: **exit 0**, gate acquired slot 1, output `Build completed successfully (2902 jobs).` Only warnings: `Flow/Limit.lean:39` unused section instance `[NormedSpace ℂ F]`, `:85` unused named w, `:92` unused named t. These are not proof failures.
2. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose $MODULES`: **exit 0**. Output:

```text
replaying KAM.Wave.Analytic.Flow.Holomorphic
replaying KAM.Wave.Analytic.Flow.Limit
replaying KAM.Wave.Analytic.Flow.PicardHolo
replaying KAM.Wave.Analytic.Flow.Picard
replaying KAM.Wave.Analytic.Flow.Gronwall
replaying KAM.Wave.Analytic.Flow.Integral
replaying KAM.Wave.Analytic.TorusAnalytic
replaying KAM.Wave.Analytic.UniformLimit
replaying KAM.Wave.Analytic.HoloAnalytic
replaying KAM.Wave.Analytic.Separable
replaying KAM.Wave.Analytic.DegreeSeries
replaying KAM.Wave.Analytic.ComplexificationLp
replaying KAM.Wave.Analytic.Complexification
replaying KAM.Wave.Analytic.Cauchy
```

3. Generated `.lake/abi-scratch/W1Audit.lean` from the declaration census, importing all 14 modules and the frozen embedding definition, emitting `#print axioms` for every explicit new theorem and every def/abbrev (105 commands: 90 theorems, 15 def/abbrevs). Ran `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W1Audit.lean`: **exit 0**, 105 outputs, each exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or project axiom. The same invocation elaborated the four source/consumer probes described below.

Probe obligations (all exit 0): n=0 finite-dimensional holomorphy → real theorem's arbitrary-Banach-target analytic conclusion; construct `FlowHyp` directly from its seven source premises; assemble exact frozen `IsAnalyticTorusEmbedding` from `torus_analytic`'s analytic/periodic conjuncts with separately supplied injectivity; prove `IsClosed (range complexifyLp)` as the closed equalizer of continuous `complexifyLp ∘ reLp` and identity, using the actual proved left inverse. The injectivity assumptions belong only to this test of the consumer's remaining obligations and were not added to production declarations.

4. SLIM lint: `LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpd` — **exit 0**. Exact output:

```text
check_lean_modules: PASS (1642 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

There was no stale-root lint diagnostic. This does not waive the separate protected-path delta rule in F2.
5. `git diff --check inp...HEAD`: **exit 0**, no output. Forbidden-token/resource/EuclideanSpace search in the new modules: **no matches** (rg exit 1). All 14 files have copyright, module, public imports, module docstring and public section, and definitions are exposed through `@[expose] public ... section`; maximum physical length 202. No new provider or draft theorem import. Direct project dependencies outside this package are `KAM.Strip.Cauchy`, `KAM.Strip.Analytic`, and SEALED `KAM.Frozen.Wave.Defs.WaveSpace`; axiom closure rules out an indirect unproved theorem dependency.
6. Protected paths: `git diff inp...HEAD -- KAM/Frozen manifest README.md`: **empty**. Adding `KAM.lean` gives the nonempty one-line import delta in F2; adding `KAM/Root` also finds its new generated Wave facade. No auditor repair was made.

## Complete declaration ledger

One row per explicit new declaration, including all auxiliary public exports. Locations are at package HEAD above. `PASS (conditional)` means the exact auxiliary theorem is valid with its advertised induction/problem hypotheses and is not a completed source node by itself. Definition rows use the classification and domain qualifications above. All theorem rows have the same independently printed standard axiom set.

| Node / role | Declaration (file:line) | Verdict | Reason / qualification |
|---|---|---|---|
| cauchy / deriv-continuous | `norm_fderiv_le_div_of_ball` (KAM/Wave/Analytic/Cauchy.lean:36) | PASS | Guarded radius and pointwise bound; exact source estimate. |
| cauchy / deriv-continuous | `norm_fderiv_le_div_of_ball_subset` (KAM/Wave/Analytic/Cauchy.lean:55) | PASS | Guarded radius and pointwise bound; exact source estimate. |
| cauchy / deriv-continuous | `lipschitz_of_margin` (KAM/Wave/Analytic/Cauchy.lean:61) | PASS | Guarded radius and pointwise bound; exact source estimate. |
| cauchy / deriv-continuous | `norm_fderiv_sub_le_holoMargin` (KAM/Wave/Analytic/Cauchy.lean:79) | PASS | Exact 2B/ρ² constant and half-radius domain. |
| cauchy / deriv-continuous | `continuousOn_fderiv_of_holomorphic` (KAM/Wave/Analytic/Cauchy.lean:139) | PASS | Local bound derived from continuity; no global bound premise. |
| complexification-lemma (ii)/(iii) | `analyticAt_comp_realLinear` (KAM/Wave/Analytic/Complexification.lean:39) | PASS | Real-linear pre/postcomposition; no completeness premise. |
| complexification-lemma (ii)/(iii) | `analyticAt_real_part` (KAM/Wave/Analytic/Complexification.lean:45) | PASS | Local real recovery and exact derivative identity. |
| complexification / lemma (i) | `lpPointwise` (KAM/Wave/Analytic/ComplexificationLp.lean:30) | PASS | Whole-carrier coordinate CLM; norm hypothesis proves ℓ² membership. |
| complexification / lemma (i) | `lpPointwise_apply` (KAM/Wave/Analytic/ComplexificationLp.lean:40) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `norm_ofRealCLM_le` (KAM/Wave/Analytic/ComplexificationLp.lean:45) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `norm_reCLM_le` (KAM/Wave/Analytic/ComplexificationLp.lean:47) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `norm_conjCLE_le` (KAM/Wave/Analytic/ComplexificationLp.lean:50) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `complexifyLp` (KAM/Wave/Analytic/ComplexificationLp.lean:53) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `reLp` (KAM/Wave/Analytic/ComplexificationLp.lean:57) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `conjLp` (KAM/Wave/Analytic/ComplexificationLp.lean:61) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `complexifyLp_apply` (KAM/Wave/Analytic/ComplexificationLp.lean:64) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `reLp_apply` (KAM/Wave/Analytic/ComplexificationLp.lean:67) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `conjLp_apply` (KAM/Wave/Analytic/ComplexificationLp.lean:70) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `norm_complexifyLp` (KAM/Wave/Analytic/ComplexificationLp.lean:74) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `norm_reLp_le` (KAM/Wave/Analytic/ComplexificationLp.lean:79) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `reLp_complexifyLp` (KAM/Wave/Analytic/ComplexificationLp.lean:83) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `norm_conjLp` (KAM/Wave/Analytic/ComplexificationLp.lean:87) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `conjLp_smul` (KAM/Wave/Analytic/ComplexificationLp.lean:92) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `conjLp_conjLp` (KAM/Wave/Analytic/ComplexificationLp.lean:96) | PASS | Coordinate/norm/conjugation fact proved as stated; does not close F1. |
| complexification / lemma (i) | `norm_sq_complexify_add_I_smul` (KAM/Wave/Analytic/ComplexificationLp.lean:100) | PASS | ℓ² square-norm identity; no product-norm substitution. |
| holo-analytic-fd / degree grouping | `wordCount` (KAM/Wave/Analytic/DegreeSeries.lean:40) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `wordFiberCard` (KAM/Wave/Analytic/DegreeSeries.lean:44) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `wordTerm` (KAM/Wave/Analytic/DegreeSeries.lean:48) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `wordTerm_apply` (KAM/Wave/Analytic/DegreeSeries.lean:53) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `norm_wordTerm_le` (KAM/Wave/Analytic/DegreeSeries.lean:57) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `degreeSeries` (KAM/Wave/Analytic/DegreeSeries.lean:79) | PASS | Averaged-word construction; diagonal and norm proved. |
| holo-analytic-fd / degree grouping | `sum_wordCount` (KAM/Wave/Analytic/DegreeSeries.lean:84) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `exists_word_of_sum` (KAM/Wave/Analytic/DegreeSeries.lean:91) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `prod_word` (KAM/Wave/Analytic/DegreeSeries.lean:114) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `wordFiberCard_pos` (KAM/Wave/Analytic/DegreeSeries.lean:124) | PASS | Positive fiber cardinality proved from degree compatibility. |
| holo-analytic-fd / degree grouping | `degreeSeries_apply_diag` (KAM/Wave/Analytic/DegreeSeries.lean:129) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `norm_degreeSeries_le` (KAM/Wave/Analytic/DegreeSeries.lean:152) | PASS | Finite combinatorial/multilinear identity or bound supporting exact series diagonal. |
| holo-analytic-fd / degree grouping | `card_antidiagonalTuple` (KAM/Wave/Analytic/DegreeSeries.lean:180) | PASS | Stars-and-bars cardinality, including zero dimensions/degrees. |
| flow / comparison helper | `exp_sub_one_div_le` (KAM/Wave/Analytic/Flow/Gronwall.lean:33) | PASS (conditional) | Explicit conditional calculus/comparison lemma; source consumers supply its inputs. |
| flow / comparison helper | `norm_sub_le_of_solutions_forward` (KAM/Wave/Analytic/Flow/Gronwall.lean:42) | PASS (conditional) | Explicit conditional calculus/comparison lemma; source consumers supply its inputs. |
| flow / comparison helper | `continuousOn_of_hasDerivWithinAt_Icc` (KAM/Wave/Analytic/Flow/Gronwall.lean:72) | PASS (conditional) | Explicit conditional calculus/comparison lemma; source consumers supply its inputs. |
| flow / comparison helper | `norm_sub_le_of_solutions` (KAM/Wave/Analytic/Flow/Gronwall.lean:77) | PASS (conditional) | Explicit conditional calculus/comparison lemma; source consumers supply its inputs. |
| flow / comparison helper | `norm_sub_le_of_deriv_bound` (KAM/Wave/Analytic/Flow/Gronwall.lean:125) | PASS (conditional) | Explicit conditional calculus/comparison lemma; source consumers supply its inputs. |
| flow / conclusions | `hasDerivWithinAt_holoFlow` (KAM/Wave/Analytic/Flow/Holomorphic.lean:39) | PASS | Closed-interval ODE, with continuity of trajectory and RHS supplied separately. |
| flow / conclusions | `eq_holoFlow_of_solution` (KAM/Wave/Analytic/Flow/Holomorphic.lean:63) | PASS | Uniqueness among all V-valued solutions, not just a smaller-ball premise. |
| flow / conclusions | `holomorphicOn_holoFlow` (KAM/Wave/Analytic/Flow/Holomorphic.lean:85) | PASS | Uniform holomorphic limit. |
| flow / conclusions | `norm_fderiv_holoFlow_le` (KAM/Wave/Analytic/Flow/Holomorphic.lean:91) | PASS | Exact exp(M/δ * abs t) operator-norm bound. |
| flow / conclusions | `holoFlow_mem_range` (KAM/Wave/Analytic/Flow/Holomorphic.lean:105) | PASS | General split closed real subspace; concrete closedness proved in probe. |
| flow / conclusions | `norm_holoFlow_sub_holoFlow_le` (KAM/Wave/Analytic/Flow/Holomorphic.lean:132) | PASS | Common source constants, common convex trajectory ball, exact parameter estimate. |
| flow / integral helper | `norm_integral_le_primitive` (KAM/Wave/Analytic/Flow/Integral.lean:33) | PASS (conditional) | Explicit conditional calculus/comparison lemma; source consumers supply its inputs. |
| flow / integral helper | `norm_integral_le_pow` (KAM/Wave/Analytic/Flow/Integral.lean:62) | PASS (conditional) | Explicit conditional calculus/comparison lemma; source consumers supply its inputs. |
| flow / integral helper | `norm_integral_le_exp` (KAM/Wave/Analytic/Flow/Integral.lean:76) | PASS (conditional) | Explicit conditional calculus/comparison lemma; source consumers supply its inputs. |
| flow / Picard limit | `holoFlow` (KAM/Wave/Analytic/Flow/Limit.lean:36) | PASS | Literal increment tsum; solution meaning only on guarded source domain. |
| flow / Picard limit | `tendstoUniformlyOn_of_succ_sub` (KAM/Wave/Analytic/Flow/Limit.lean:39) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `summable_picard_bound` (KAM/Wave/Analytic/Flow/Limit.lean:57) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `norm_picard_succ_sub_le_bound` (KAM/Wave/Analytic/Flow/Limit.lean:68) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `tendstoUniformlyOn_picard_U` (KAM/Wave/Analytic/Flow/Limit.lean:82) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `tendstoUniformlyOn_picard_time` (KAM/Wave/Analytic/Flow/Limit.lean:88) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `tendsto_picard` (KAM/Wave/Analytic/Flow/Limit.lean:94) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `norm_holoFlow_sub_le` (KAM/Wave/Analytic/Flow/Limit.lean:98) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `holoFlow_mem_ball` (KAM/Wave/Analytic/Flow/Limit.lean:103) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `holoFlow_zero` (KAM/Wave/Analytic/Flow/Limit.lean:110) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `continuousOn_holoFlow_time` (KAM/Wave/Analytic/Flow/Limit.lean:115) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `continuousOn_X_holoFlow` (KAM/Wave/Analytic/Flow/Limit.lean:120) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard limit | `holoFlow_eq_integral` (KAM/Wave/Analytic/Flow/Limit.lean:126) | PASS | Convergence/continuity/integral consequence of the proved summable Picard majorant. |
| flow / Picard construction | `FlowHyp` (KAM/Wave/Analytic/Flow/Picard.lean:38) | PASS | Seven source fields; M_pos is explicitly in current blueprint. |
| flow / Picard construction | `wavePicard` (KAM/Wave/Analytic/Flow/Picard.lean:48) | PASS | Literal integral recursion; analytical uses establish integrability. |
| flow / Picard construction | `wavePicard_zero` (KAM/Wave/Analytic/Flow/Picard.lean:52) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `wavePicard_succ` (KAM/Wave/Analytic/Flow/Picard.lean:54) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `FlowHyp.delta_pos` (KAM/Wave/Analytic/Flow/Picard.lean:62) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `FlowHyp.ball_subset_V` (KAM/Wave/Analytic/Flow/Picard.lean:64) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `FlowHyp.lipschitzOn_ball` (KAM/Wave/Analytic/Flow/Picard.lean:72) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `FlowHyp.norm_fderiv_le_ball` (KAM/Wave/Analytic/Flow/Picard.lean:77) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `FlowHyp.mem_V_of_ball` (KAM/Wave/Analytic/Flow/Picard.lean:81) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `FlowHyp.continuousOn_X` (KAM/Wave/Analytic/Flow/Picard.lean:84) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `continuousOn_wavePrimitive` (KAM/Wave/Analytic/Flow/Picard.lean:93) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `uIoc_subset_Icc` (KAM/Wave/Analytic/Flow/Picard.lean:103) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `uIcc_subset_Icc'` (KAM/Wave/Analytic/Flow/Picard.lean:106) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `norm_picard_sub_le` (KAM/Wave/Analytic/Flow/Picard.lean:117) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `picard_mem_ball` (KAM/Wave/Analytic/Flow/Picard.lean:138) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `continuousOn_X_picard` (KAM/Wave/Analytic/Flow/Picard.lean:145) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / Picard construction | `norm_picard_succ_sub_le` (KAM/Wave/Analytic/Flow/Picard.lean:151) | PASS | Source margin, recursion, continuity or factorial estimate; no extra final-flow premise. |
| flow / holomorphic iterates | `picardD` (KAM/Wave/Analytic/Flow/PicardHolo.lean:35) | PASS | fderiv alias; differentiability produced by induction. |
| flow / holomorphic iterates | `PicardInv` (KAM/Wave/Analytic/Flow/PicardHolo.lean:39) | PASS | Induction invariant; never an extra premise of final flow results. |
| flow / holomorphic iterates | `picardInv_zero` (KAM/Wave/Analytic/Flow/PicardHolo.lean:47) | PASS | Proves base invariant, no assumed derivative bound. |
| flow / holomorphic iterates | `picardG` (KAM/Wave/Analytic/Flow/PicardHolo.lean:65) | PASS | Derivative composition alias; factors justified at point of use. |
| flow / holomorphic iterates | `continuousOn_picardG` (KAM/Wave/Analytic/Flow/PicardHolo.lean:68) | PASS (conditional) | Statement and body checked at the named source/helper role. |
| flow / holomorphic iterates | `norm_picardG_le` (KAM/Wave/Analytic/Flow/PicardHolo.lean:75) | PASS (conditional) | Statement and body checked at the named source/helper role. |
| flow / holomorphic iterates | `hasFDerivAt_picard_succ` (KAM/Wave/Analytic/Flow/PicardHolo.lean:82) | PASS (conditional) | Statement and body checked at the named source/helper role. |
| flow / holomorphic iterates | `picardD_succ` (KAM/Wave/Analytic/Flow/PicardHolo.lean:121) | PASS (conditional) | Statement and body checked at the named source/helper role. |
| flow / holomorphic iterates | `picard_holo` (KAM/Wave/Analytic/Flow/PicardHolo.lean:128) | PASS | Proves invariant for every k; induction premises discharged. |
| holo-analytic-fd | `exists_powerSeries_coeff_banach` (KAM/Wave/Analytic/HoloAnalytic.lean:38) | PASS | Coefficients chosen before bound A; arbitrary Banach target. |
| holo-analytic-fd | `analyticOnNhd_of_differentiableOn_banach` (KAM/Wave/Analytic/HoloAnalytic.lean:59) | PASS | No target second-countability; all n including 0. |
| holo-analytic-fd | `tsum_degree_fiber` (KAM/Wave/Analytic/HoloAnalytic.lean:73) | PASS | Summability/grouping identity supporting the quantitative power series. |
| holo-analytic-fd | `summable_card_mul_pow` (KAM/Wave/Analytic/HoloAnalytic.lean:86) | PASS | Summability/grouping identity supporting the quantitative power series. |
| holo-analytic-fd | `holomorphic_fd_power_series` (KAM/Wave/Analytic/HoloAnalytic.lean:102) | PASS | Enlarged polydisc, absolute convergence, binomial estimate and power-series representation. |
| holo-analytic-fd | `holomorphic_real_part_analytic` (KAM/Wave/Analytic/HoloAnalytic.lean:191) | PASS | Real analytic on actual preimage of U. |
| holo-analytic-fd / Banach reduction | `exists_separable_lift` (KAM/Wave/Analytic/Separable.lean:41) | PASS | Closed separable subspace and holomorphic lift are outputs. |
| torus-analytic | `WaveSpaceC` (KAM/Wave/Analytic/TorusAnalytic.lean:32) | PASS | Literal product complexification or proved left-inverse identity. |
| torus-analytic | `complexifyWave` (KAM/Wave/Analytic/TorusAnalytic.lean:36) | PASS | Literal product complexification or proved left-inverse identity. |
| torus-analytic | `reWave` (KAM/Wave/Analytic/TorusAnalytic.lean:39) | PASS | Literal product complexification or proved left-inverse identity. |
| torus-analytic | `reWave_complexifyWave` (KAM/Wave/Analytic/TorusAnalytic.lean:41) | PASS | Literal product complexification or proved left-inverse identity. |
| torus-analytic | `torus_analytic` (KAM/Wave/Analytic/TorusAnalytic.lean:46) | PASS | Exact frozen analytic/periodic conjuncts; injectivity remains separate. |
| uniform-limit | `uniformCauchySeqOn_fderiv` (KAM/Wave/Analytic/UniformLimit.lean:36) | PASS | Derivative Cauchy estimate on stated doubled-ball margin. |
| uniform-limit | `holomorphic_of_tendstoUniformlyOn` (KAM/Wave/Analytic/UniformLimit.lean:72) | PASS | Qualitative result has no boundedness input. |
| uniform-limit | `mem_of_tendstoUniformlyOn` (KAM/Wave/Analytic/UniformLimit.lean:109) | PASS | Closed-set specialization includes the real subspace. |
| uniform-limit | `norm_fderiv_le_div_of_tendstoUniformlyOn` (KAM/Wave/Analytic/UniformLimit.lean:116) | PASS | Quantitative clause adds pointwise limit bound and positive δ. |

## Immutable file hashes

SHA256 values for the 14 audited module files at the package HEAD; names below are relative to `KAM/Wave/Analytic/`.

| File | Physical lines | SHA256 |
|---|---:|---|
| `Cauchy.lean` | 170 | `fa4d00e319207dd946acb7168c0ef12f54ef978e2ca589a9e151e3a3f6882e99` |
| `Complexification.lean` | 63 | `245fdd04ecff886f07ea8fa48513fe1d5e28662692eb221da2faa5560be0aac8` |
| `ComplexificationLp.lean` | 122 | `759d165d576979c31e0d5ded5af1538ddac31a53fe1eabb6daf1d7aa21f48a85` |
| `DegreeSeries.lean` | 197 | `dec265d0147c21df8546b4f405f09caff93fb3bd50e0a3226ed1019d9940543a` |
| `Flow/Gronwall.lean` | 134 | `c21ab25c296b89f0914472d2fdc77017af15a53c2d87271f73508d591e91e627` |
| `Flow/Holomorphic.lean` | 142 | `fe4b771879aa490f952e1a521d2aabd9e8dc6442ef9ee936aa11cfe8fef8bef3` |
| `Flow/Integral.lean` | 85 | `b01429b77597eadd349368b47cb57d7195d931d9af0012ef1bcdd6012b4385a1` |
| `Flow/Limit.lean` | 145 | `07393342944147a64146bc06c4e80f18dbb680c58ec130a70894c91f23441c55` |
| `Flow/Picard.lean` | 192 | `6fc2d1be2d5a23d779b103f10dcb9409081c96da7162848605a6744d73ef445f` |
| `Flow/PicardHolo.lean` | 149 | `c35e220d44c93653c2fa09bd005d3afd000c0ddb96a5d742ed5cacdf49ed0b3e` |
| `HoloAnalytic.lean` | 202 | `df4a675726b1395899229865f83c0923a5a9870733894c025f2692d6f6eb024e` |
| `Separable.lean` | 85 | `ed8b6b2fe33d2e5af99542e959d253bf964af593812da91b3d19769cbccb2e2e` |
| `TorusAnalytic.lean` | 68 | `6c7ffd731e5d1d6f6cb3681c303d3be836fc373ec2b613aba136b2877187437b` |
| `UniformLimit.lean` | 122 | `7199f6b5129b1601bc9bd0d6e5cbf695bdf74b120a11b55589c1cb0bae6a20ca` |

## Suspected source defects, deviations, and closeout

No new defect in the audited current blueprint subsection was found. The existing source-gap at pinned `inp` lines 918–924 quotes the P96-K A.4 mean-value step and explains that an open V need not contain the segment joining two trajectories. This audit verifies the blueprint's convex-ball repair; it does not independently re-audit the original PDF. No network source was used. F1 is omitted formalization, not an alleged source erratum. Averaged-word multilinear grouping and closed-interval within derivatives are the implementation deviations explained above.

Report-only audit is complete: all 107 explicit declarations are classified, the required verification has finished, and the final worktree check is recorded below. Package acceptance remains blocked by F1/F2; those findings were not repaired. No campaign theorem, graph node promotion, frozen seal, embedding injectivity, W5 margin instantiation, or W6/W8 consumer theorem is certified by this report.

Final recheck: `inp` advanced concurrently to `4a46fd6476e6cef375650b0ff949c4f74c735aaa`. Re-read its analytic subsection: it has the same SHA256 shown above; the `git diff inp...HEAD` file inventory is unchanged. Package HEAD remains fixed at `c87c7a34db8e1e56aacb97a01d60c8a659271955`. Final `git status --short` shows only `?? docs/tracks/W/audits/W1-ANALYTIC-audit-1.md`; tracked files are unchanged by the audit. The scratch probe and audit-only scratch logs/census/diff were removed after extracting the evidence. `git diff --check` and report whitespace/placeholder checks passed. No errata ledger or other report was modified.
