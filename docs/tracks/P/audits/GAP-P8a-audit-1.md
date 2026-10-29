# GAP-P8a independent audit 1

**Overall verdict: FAIL for literal graph-node closure.** The Lean proofs checked successfully, but four named exports omit parts of their assigned source conclusions. This is a statement-completeness failure, not a detected kernel soundness failure. Do not mark those four nodes PROVED on this package alone.

Audited checkout: `/root/code/KAM-inp-gp8a`, HEAD `783cc44515e0ccb5f2985575755988696591436f`; comparison ref `inp` = `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`. Audit date: 2026-10-29.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, this worktree's GAP-P8a handoff including AUDIT FOCUS, GAP-PLAN-P.md's GAP-P8a section, the relevant P810 design table/conventions/departures, track P statement P7 item 4, all nine graph records' SOURCE_HYPOTHESES/SOURCE_QUANTIFIERS/SOURCE_CONCLUSION, and their cited blueprint statements/proofs.

The complete `git diff inp...HEAD` adds AnalyticNodes.lean (435 lines) and ModelTransferNodes.lean (471 lines). The audited file is **only** `KAM/Planetary/SecularForm/ModelTransferNodes.lean`, read in full against that diff. AnalyticNodes is an imported dependency assigned a separate audit, not independently certified here. The explicit user path overrides the generic brief's main-worktree output path. Only this report was added; audit probes were confined to `.lake/abi-scratch/` and removed.

There are **no provider exports, frozen theorem targets, or SIGNED declarations** in this unsigned graph-gap slice. Provider/frozen type equality and seal-body probes are therefore not applicable; this audit does not seal P-G, P-PLANAR, P-FIXED or any other anchor. Relevant frozen definitions read include HasSecularBirkhoffForm, SecularAverage, Assemble and HamiltonianVectorField. The imported frozen closure consists only of SEALED definitions, with no frozen theorem assumption.

## Per-node verdicts

Names below are in `KAM.Planetary.SecularForm`; line numbers refer to ModelTransferNodes.lean. Each row was checked against its graph record and the indicated blueprint lines, not just its handoff description.

| Node | Declaration | Verdict | Source comparison |
|---|---|---|---|
| `stepP:p8:id-diff` | `identification_diff`, L35 | PASS | Graph L15942; blueprint L191. For arbitrary chart-valid slow point, states the squared total momentum difference, continuous single-angle momenta, their assembly identity and continuity of the difference. Physical/source premises only. |
| `stepP:p8:id-avg` | `identification_avg`, L67 | PASS | Graph L15972; blueprint L192. Correct radian normalization and both delta forms, with kappa=G*m0. No integrability output imported as a premise. |
| `stepP:p8:id-int` | `identification_int`, L95 | PASS | Graph L16001; blueprint L193. Integrability iff on slowDom; subtraction guarded by actual integrability; both perturbations integrable on an internally obtained positive real polydisc. |
| `bpP:p8:identification` | `identification_full`, L166 | FAIL | Graph L15910; blueprint L182–189. Correct continuity/average/iff/guarded subtraction and unconditional polydisc Hamiltonian identities, but the parent's required pointwise difference formula is absent from its conclusion. F3. |
| `bpP:p8:same-jets#jets` | `same_jets_jets`, L335 | FAIL | Graph L16059; blueprint L197–201, L206. Correct all-order slow tensors with all action derivatives, uniform quartic remainder and derivative identities. It does not state the secular Hamilton equations, constant actions or the mu-scaled fast-frequency identity required by (b). F2. |
| `bpP:p8:same-jets#transfer` | `same_jets_transfer_full`, L361 | PASS | Graph L16091; blueprint L202, L206. Literal frozen HasSecularBirkhoffForm iff, unchanged Omega/beta, P0-delta; whole oscillator-disc containment is sourced. Composition holds for every action-preserving map into the polydisc, strictly stronger than requiring a symplectic map. |
| `bpP:p8:same-jets` | `same_jets_full`, L258 | FAIL | Graph L16030; blueprint L196–204. Genuinely bundles jets, remainder, transfer and composition at one common radius. Still lacks (b)'s explicit dynamical conclusions, as does its jets projection. F2. |
| `stepP:p8:q4-c` | `quartic_c_node`, L379 | PASS | Graph L16247; blueprint L234 and L224. Gives both diagonal radialR1 identities on positive separated actions; factor G generalizes the source units G=m0=1. Does not assert equality with the unrepaired printed CP11 coefficient or pretend to compute the mixed coefficients. |
| `bpP:p8:quartic` | `quartic_full`, L413 | FAIL | Graph L16121; blueprint L216–229. Correct six-coefficient existence, analytic two-action dependence, fixed/moving fourth jets, radial diagonals, pair scaling and sufficient separated subdomain. Missing literal alpha-analyticity of W's Taylor coefficients and actual pair quartic conversion; its final generic conditional conversion has a missing constant term. F1. |

PASS denotes the unsigned node's audited statement/proof, not frozen-anchor seal readiness.

### F1: quartic bundle substitutes a conditional helper for the actual conversion

At L444–456, the last conjunct quantifies arbitrary `A A' B c W` and assumes

```text
W(v) - (A |v_i|² + A' |v_j|² + B v_i·v_j) - sum c_m M_m(v) = O(||v||^5).
```

This is a useful conditional helper, but does not state the source conclusion for `W(v)=dimensionlessPair(alpha,v_i,v_j)`. No conjunct identifies this W, supplies its Taylor coefficients from analyticity, relates these c's to the earlier existential coefficient family, or equates the resulting quartic polynomial to the actual pair jet with prefactor `-G*m_i*m_j/a_j`. These are required by blueprint L221 and graph L16121 SOURCE_CONCLUSION. Re-exporting an arbitrary expansion premise inside a conjunction does not build the needed dependency output internally.

Moreover, the premise omits `W(0)`. Evaluating its Big-O bound at zero forces **W(0)=0**; the audit probe proves this in Lean. The actual circular inverse-distance average has a nonzero constant term (positive for 0<alpha<1), so one must either explicitly center W or carry that constant. Neither centering nor a connection to dimensionlessPair is supplied by this export. The existing `quartic_sqrt_chart_conversion_const` (Quartic/Conversion.lean L443) carries the constant and prefactor. The existing `quartic_pair_chart_conversion` (Quartic/PairChart.lean L159) actually supplies coefficients for dimensionlessPair and the pair-polynomial identity. They are imported transitively but not assembled into the named node's conclusion. The scope rule prevents repairing this here.

Also, L430 states only `AnalyticOnNhd ℝ dimensionlessPair separatedDomain`. There is no statement of analyticity on the **whole** interval alpha in (0,1) of its v=0 Taylor coefficients (all orders), explicitly requested by GAP-PLAN-P exports item 6 and blueprint L221. This follows by analytic calculus, but the named unsigned export does not state it. Do not replace this obligation by analytic dependence of the separate canonical c coefficients in L415–417; those are different functions/carriers.

### F2: derivative identities do not literally state part (b)

`same_jets_full` L272–276 and `same_jets_jets` L349–353 state equality of slow Frechet derivatives and the action derivative offset of S. Those are correct prerequisites. Their statements never introduce the averaged Hamiltonians or coupling mu, never assert the displayed equations `dot xi_i = mu*partial_eta_i S`, `dot eta_i = -mu*partial_xi_i S`, never assert zero action components, and never state the fast-frequency difference `mu*partial_Lambda_i delta`.

Blueprint L201 says: “the secular equations ... are identical; Lambda is constant in both, and the frequencies ... differ by mu partial ... delta.” The corresponding graph conclusions require those claims. The handoff expressly acknowledges using fderivs of S instead. Under this audit's **literal unsigned export** rule, derivability by linearity or the structural absence of a lambda argument is not the missing statement. A component/vector-field wrapper of the actual averaged Hamiltonians can discharge this without any new ODE existence theorem. This is an export gap, not evidence that the claimed dynamical consequence is false.

The common radius and source-only assembly are correct. The Frechet tensor representation of multi-index jets is the documented design representation, and the common `coeffs` gives the same quadratic matrix; these are not separate findings. The same sigma/Omega consequence is algebraic from that common matrix, but it does not repair the missing dynamical clause.

### F3: the parent identification export drops its difference identity

Blueprint L185 and graph L15910 require

```text
hat f_mov(lambda,w') - hat f_fix(lambda,w') = |sum_i p^(i)|²/(2*m0).
```

`identification_full` L167–175 retains continuity, average delta, integrability iff and the guarded secular identity but omits this pointwise equality. It **is** correctly proved and exported by `identification_diff` L35–44, so no mathematical proof is missing from the slice. Nevertheless the handoff names identification_full as the parent node's literal conclusion, and it is a proper substatement. Under AUDIT FOCUS this parent must remain unclosed until the formula is included or an explicit accepted composite interface replaces the named parent export. Its unconditional real-polydisc averaged-Hamiltonian clauses are correct.

## Premises, quantifiers, definitions and completeness

- Data n contains only G,m0,m, their positivity and n>0, exactly the physical standing assumptions. slowDom is the real product-chart domain; x order is (xi,Lambda,eta), frozen assemble order is (I,phi,p,q)=(Lambda,lambda,eta,xi). No norm/carrier substitution was found.
- The exports construct identification, radius/integrability, quadratic_form and analytic dependencies inside proofs. No main theorem assumes those proved outputs. The exception in F1 is precisely the unattached generic expansion conditional used to stand for the requested source conversion.
- Radii/C are chosen from D,a before points, derivative orders, V,r0,mu0,P0,Omega,beta or chi; no wider constant dependence was found. Minima of positive radii preserve positivity and shrink domains. The design explicitly allows existential radii (P810-LEAN-DESIGN.md L347); the simultaneous same-jets radius is shared by both models and all bundled clauses. Selecting a smaller radius is not by itself a failure.
- All-order Frechet tensor equality with all action derivatives is a faithful stronger tensor formulation of the multi-index statement. Max norm in the uniform quartic remainder is the design's finite-dimensional norm convention. The q4-c G factor is a valid unit-generalization. Omitting symplecticity in composition strengthens the source claim without changing its domain requirements.
- **New definitions classification: none.** The audited file introduces no def, abbrev, structure, instance or new axiom. Its local embeddings fix the appropriate slow/action coordinates; its local radius is min of valid radii. The named imported objects inspected are genuine physical perturbations and frozen averages, literal action/axis maps, six invariant monomials, the radial derivative formula and the parameter-free separated pair integral. No new fallback/junk object is used to prove a conclusion. Nonintegrable averages are explicitly guarded before subtraction.
- GAP-PLAN-P maps exactly these nine nodes to ModelTransferNodes; all nine have rows above. The slice is **incomplete** for the four FAIL nodes. No other closed-node skip list is supplied by the handoff. The related previously closed quartic proof cuts are indeed PROVED: q4-str at graph L16154, q4-a at L16186, q4-b at L16218. Their LEAN_REF entries name quartic, scaling, diagonal and actual pair-conversion results. No BYPASSED claim was needed. The nine target records remain NOT_STARTED in this checkout; this report changes no graph state.

## Independent verification

All Lean-related checks were run sequentially in this worktree with `LEAN_NUM_THREADS=1` and `nice -n 5`; the compile-gate build completed before kernel replay, which completed before lint (including its internal ABI Lean invocation), which completed before the scratch Lean probe. No lake clean/update/cache operation or package-directory mutation was performed.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp8a KAM.Planetary.SecularForm.ModelTransferNodes
```

Exit **0**. Gate output:

```text
[inp-gate] slot 1 acquired 01:55:50 for KAM.Planetary.SecularForm.ModelTransferNodes
Build completed successfully (9206 jobs).
```

The 9206 count includes Lake replays, not a scratch library rebuild. Output contains inherited unused-variable/simp warnings in dependency modules; no error or warning is attributed to ModelTransferNodes.lean.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.ModelTransferNodes
```

Exit **0**, exact output:

```text
replaying KAM.Planetary.SecularForm.ModelTransferNodes
```

There is one audited lemma module and no separate provider module. This replay certifies its elaborated declarations, not the source fidelity of its imported separately audited dependency.

### Axiom and missing-constant probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-gp8a-probe.lean
```

The scratch file imports ModelTransferNodes and runs `#print axioms` on **all nine new public theorems**, followed by an example proving that the exact L446–447 expansion premise implies W(0)=0. The example uses `hW.bound`, `self_of_nhds` and simplification of the six zero monomials. No resource overrides. The first probe attempt needed an additional finite-sum simplification; that scratch-only failure was corrected before the final run.

Exit **0**, exact output:

```text
'KAM.Planetary.SecularForm.identification_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.same_jets_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.same_jets_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.same_jets_transfer_full' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_c_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_full' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The missing-constant example elaborates successfully with no additional output.

### Lint and static checks

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1196 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The **only** failure is the expressly permitted generated-root staleness; root regeneration belongs to the orchestrator and is not a package finding. No forbidden-token, EuclideanSpace, line-length, module-format or errata-render drift complaint. The audited file has 471 lines, maximum line length 98 characters, copyright/module/public imports/docstring/public noncomputable section. No resource overrides. An independent public-name scan across KAM found no other declaration with any of these nine short names; namespace scope is KAM.Planetary.SecularForm, with no harmful root shadow.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0**, no output. Recursive local KAM import inspection found 160 KAM modules; the frozen imports are all SEALED definitions and there is no provider or frozen theorem import (hence no DRAFT_SORRY dependency). Build, replay and the nine axiom lists agree with that finding.

## Source issues, deviations and limits

No new suspected defect in a pinned source or frozen declaration was discovered; the audit did not rederive CP11's printed quartic formulas. Blueprint L238 already documents the CP11 (B.6) alpha-exponent issue. This package uses radialR1 and does not assert the unrepaired printed formula. The mixed coefficients remain the declared Part 11b forward obligation, not an audit failure here.

The deviations needing repair are the unsigned-export omissions F1–F3. In particular, F1 does not show the existing conditional conversion theorem is false: it shows that it is not the requested source-specific conversion. Symplecticity omission and the G factor are valid strengthenings; shrinking a radius is documented and valid. No protected file was edited, no source gap was silently repaired, and no graph or campaign status was changed. The report is the only audit deliverable; no commit was made.
