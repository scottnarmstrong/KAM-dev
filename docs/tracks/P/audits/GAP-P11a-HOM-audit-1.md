# GAP-P11a-HOM independent audit 1

Overall verdict: **FAIL for literal graph closure**. Five of seven requested nodes pass; the two
real-Lipschitz nodes require a source clarification described below. This is a statement-fidelity
failure, not a proof-soundness failure. No frozen theorem anchor is claimed or sealed by this package.

Audited HEAD `ef583e869e5263fb1a9476da3b2c222b287f5a94` against current `inp`
`4d8a6848e381c8baaa9072e8d9867e3fc7a36f2a`, using `git diff inp...HEAD`.
The complete diff consists of three new files, 816 added lines:

- `KAM/Planetary/MaximalStep/HomologicalNodes.lean` (311 lines; H below).
- `KAM/Planetary/MaximalStep/RealLipschitzNodes.lean` (278 lines; R below).
- `KAM/Planetary/WeakKAM/LipSumNodes.lean` (227 lines; L below).

Read AGENTS, PLAN, DECISIONS, the supplied package brief and handoff/AUDIT FOCUS,
`docs/tracks/P/statement.md`, the P11A design (including its signature appendix), the live
`/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, and GAP-PLAN-P2 §§GAP-P11a2-hom/GAP-P11a14.
For each node below I read its full NODE record and its cited blueprint statement/proof.
The explicit user instruction controls the report destination over the generic brief's main-worktree path.
Only this report was edited outside `.lake/abi-scratch/`; no state-changing git operation was used.

## Per-node verdicts and literal contracts

All declaration names below have prefix `KAM.Planetary.`.

| Node | Declaration / locator | Verdict | Contract comparison |
|---|---|---|---|
| `stepP:p11a:hm-div` | `hm_div_node`, H:35 | PASS | DEPGRAPH:23474; p11a2:187. Gives D/2 on all B and all nonzero modes of size ≤ T. The derivative bound implies L ≥ 0 at the quantified point b; no new sign premise and no assumed extended divisor. Stronger: no reality premise. |
| `stepP:p11a:hm-bracket` | `hm_bracket_node`, H:244 | PASS | DEPGRAPH:23626; p11a2:197. Both equalities are explicit for every b and phase point. Uses the constructed solutions and proves the B-divisor internally from source E-divisors. No assumed solving equation. Stronger: does not need norm bounds or reality. |
| `bpP:p11a:homological-maximal` | `homological_maximal_node`, H:274 | PASS WITH NOTES | DEPGRAPH:23437; p11a2:172–198. Existential scalar/vector solutions, full-angle zero-mean polynomial class and uniqueness, (a)–(e), and final bracket are present. Reality of omega has been moved into the implication in the output specification; applying that implication with the source reality premise recovers (d). Neither L ≥ 0 nor M ≥ 0 nor a B-divisor is assumed. |
| `stepP:p11a:rl-const` | `rl_const_node`, R:205–245 | FAIL | DEPGRAPH:23943; p11a2:241, with parent p11a2:229–235. The chain is proved, but only after the extra premise `hM1 : 0 ≤ M1`. This is not implied by the standalone source coefficient bound. See F1. The general polynomial source also allows degree zero; this export requires T > 0. See F2. |
| `bpP:p11a:real-lipschitz` | `real_lipschitz_node`, R:249–272 | FAIL | DEPGRAPH:23853; p11a2:229–242. Dynamic estimates, equivariance, displacement, and coefficient chain have the right content, but the whole conjunction is restricted by the same sign premise and positive-cutoff restriction. See F1/F2. |
| `stepP:p11a:pl4-terms` | `pl4_terms_node`, L:189 | PASS | DEPGRAPH:26906; p11a4:90–92. Separate g4^j and (2qg4)^j rates, exact coefficients, and g4 = g1·2^tau. Source situation S at p11a4:30–34 explicitly uses the adapted radius. Source schedule data precede epsilon and then j. No dependency output is a node premise. |
| `stepP:p11a:pl4-sum` | `pl4_sum_node`, L:209 | PASS | DEPGRAPH:26936; p11a4:94. Summability plus every intermediate inequality is stated. `46/1000` is exactly 0.046. The threshold and adapted schedule are those of S. No summability or budget conclusion is assumed at this export. |

**Precisely failing nodes:** `stepP:p11a:rl-const`, `bpP:p11a:real-lipschitz`.

Quantifier/dependence check: the homological family binds all source data before its existential
solutions, with estimates uniform in b, theta, mode and derivative order. The universal b/mode
order in hm-div is commuted relative to the graph's shorthand; these are independent universal
quantifiers and this does not change the proposition. Scalar/vector data and M bounds are also
interleaved differently in Lean's argument list, without moving an existential constant or
changing dependence. Reality is conditional exactly as explained above, rather than silently assumed.
The real-flow export uses t in [-1,1] before theta and k, equivalent to |t| ≤ 1.
The pl4 exports put d, epsilon and its source bounds before the stage index or infinite sum.
There is no wider constant dependence.

### F1 — sign premise is a necessary repair, not a consequence of the literal standalone hypotheses

R:206 and R:250 add `hM1 : 0 ≤ M1`. The blueprint p11a2:233 says:

> If |phi-hat_(1,i,k)| ≤ M1 exp(-2 pi |k|_1 r*)/(pi D) ... then Lambda ≤ Lambda_R.

Its source paragraph and NODE record do not impose a norm bound on the arbitrary real polynomial
in this lemma, nor do they say M1 is nonnegative. Referencing the coefficient estimate from the
homological proposition explains intended use; it does not add that proposition's full input data
to this lemma. The handoff explicitly requests a ruling to interpret the sign as implicit. Neither
the supplied overnight ruling nor GAP-PLAN-P2 gives that ruling.

Counterexample to the literal source inference: N = 1, T = 1/2, phi = 0, r* = D = 1,
M1 = -1. There is no nonzero integral mode with |k|_1 ≤ 1/2, so the stated nonzero-mode decay
hypothesis is vacuous. Lambda = 0, whereas
`2 T M1 Lambda_(r*) / D = -Lambda_1 < 0`, since `Lambda_1 = coth(pi)-1 > 0`.
Both the row-sum chain and the parent's last conclusion therefore fail without a sign condition.
The Lean theorem correctly excludes this example; it consequently does not establish the unamended
literal node. This is also a suspected blueprint defect at p11a2:233/241, not evidence of an unsound
Lean proof.

Judgment on the handoff's norm-bound explanation: if M1 is an actual bound on a nonempty domain,
`0 ≤ norm(value) ≤ M1` does imply the sign. For the intended homological application, N ≥ 1,
nonempty E, and positive strip/tube widths suffice. Those data are absent from the standalone
real-polynomial exports and their source lemma; E is even allowed empty in the homological source.
Calling a real parameter a bound cannot replace the missing logical attachment. An explicit owner
ruling/source amendment making M1 ≥ 0 standing data would resolve this finding. No such amendment
was made by this audit.

### F2 — the general real-polynomial statement includes the constant case

The polynomial definition p11a2:25 admits T ≥ 0, and p11a2:230 does not add T > 0.
R:205/249 require `hT : 0 < T`, including for the dynamic clauses and first row-sum estimate.
Thus T = 0 is not covered by these named exports. This is harmless for applications that retain
homological T > 0, but is a further narrowing of the independent literal lemma. A constant real
vector field has the stated global flow and derivative/displacement bounds, so this is a missing
case rather than a false source claim. The positive r* and D premises are legitimate for the
referenced homological decay estimate; putting them before the first, unconditional clause only
limits that clause's standalone reuse.

## Public declarations, definitions and completeness

No new declaration in these three files is SIGNED in P11ASignatures or the design's exact-type
appendix. Thus there is no changed signed ABI to compare and no provider/frozen seal probe to run.
These are expressly UNSIGNED literal node exports. The seven-node offload table is exhausted above;
`c2-conv#bracket` is intentionally outside the new export scope. Existing signed dependencies were
not changed. The design's homological local coefficient, bound, average/parameter and reality steps
are visibly used in H:111–174; they are not new assumed inputs at the mapped node export.
The original C7 global/variational suppliers remain imported; this audit does not newly certify
other package scopes.

| Public theorem | Verdict | Meaning / scope |
|---|---|---|
| `hm_div_node` | PASS | Literal node above. |
| `hmMaxSolution_of_empty` | PASS | Tube of empty E is empty at every radius; all on-domain obligations are vacuous. |
| `hm_diff_at` | PASS | Explicit conditional supplier for the finite solve; B-divisor is allowed here. |
| `hmMaxSolution_solve` | PASS | Conditional scalar assembly, distinct name; takes the divisor bound and M ≥ 0. Not a replacement node export. |
| `hmMaxSolution_solve'` | PASS | Removes M ≥ 0 by evaluating the datum or treating empty E. |
| `hm_bracket_solve` | PASS | Conditional bracket supplier with the B-divisor. Node wrapper discharges it. |
| `hm_bracket_node` | PASS | Literal node above. |
| `homological_maximal_node` | PASS WITH NOTES | Literal source recovery and reality implication as above. |
| `rtp_support` | PASS | Finite cutoff support. |
| `rtp_coeff` | PASS | Genuine torus coefficients of finite Fourier polynomial. |
| `rtp_entire` | PASS | Entire finite Fourier sum. |
| `rtp_contDiff` | PASS | Real C2 regularity derived from finite sums. |
| `rtp_periodic` | PASS | Integer-vector periodicity derived from characters. |
| `rtp_value_le` | PASS | Global boundedness derived from finite coefficient sums. |
| `rtp_fderiv_le` | PASS | Directional derivative estimate; zero mode drops out. |
| `rtpRowSum_nonneg` | PASS | Nonnegativity of actual finite row sum. |
| `rtp_row_le_iSup` | PASS | Finite-family upper bound. |
| `iSup_rtpRowSum_nonneg` | PASS | Includes the empty Fin case under real supremum conventions. |
| `rtp_fderiv_norm_le` | PASS | Real induced sup operator norm bound, no dimension factor. |
| `iSup_fderiv_le` | PASS | Bounded supremum of derivative norms. |
| `fderiv_bddAbove` | PASS | Establishes boundedness before supremum use. |
| `value_bddAbove` | PASS | Establishes value supremum boundedness. |
| `rl_const_node` | FAIL | Literal node applicability, F1/F2; theorem sound under its own premises. |
| `real_lipschitz_node` | FAIL | Literal node applicability, F1/F2; theorem sound under its own premises. |
| `pl4_terms_ctx` | PASS | Conditional arithmetic supplier; context is discharged in node wrapper. |
| `pl4_sum_ctx` | PASS | Conditional arithmetic/summation supplier; context is discharged in node wrapper. |
| `pl4_terms_node` | PASS | Literal separate-rate node. |
| `pl4_sum_node` | PASS | Literal intermediate-sum node. |

Four new definitions, all exposed under the public noncomputable section:

| Definition | Classification / whole-carrier behavior |
|---|---|
| `HmZeroMeanTrig`, H:48 | Honest predicate: holomorphic, periodic, self-truncated, mean zero on univ × B. All clauses guarded by B; empty B is correctly vacuous. No junk branch. |
| `HmMaxSolution`, H:58 | Honest output specification, not an input hiding a hard step. Contains all scalar clauses, domain-local uniqueness, conditional reality and coefficient decay. Reality can be specialized with the source omega-real hypothesis. |
| `RealTrigPolyDeg`, R:35 | Honest finite Fourier polynomial predicate with real-valued codomain. Outside the degree ball coefficients vanish; the degree ball is finite. `rtp_coeff` identifies the witnesses with torus coefficients, so this is not arbitrary Fourier data. |
| `rtpRowSum`, R:139 | Actual finite sum of norms of actual nonzero torus coefficients. No selected surrogate. |

There are no other new def/abbrev/structure declarations. The inherited `p11RealFlow` has an
identity fallback off the global-solvability carrier (GlobalRealFlow:94), but R proves smoothness
and boundedness from the polynomial and invokes the genuine global-flow estimate; the fallback
is unreachable under the node's hypotheses. Supremum bounds are proved before use. The finite
solve's total division is used only at source nonzero divisors; zero/out-of-cutoff modes vanish.
There are no conclusion-shaped node hypotheses. In particular, conditional suppliers with `hdiv`
or `WeakBudgetCtx` are not the named graph exports; the wrappers prove those dependencies.

Deviation from the offload plan: H imports StepReal/StepBound instead of locally reproving
`coeff_zero_real` and `fderiv_pi_apply` (GAP-PLAN-P2:240). This is disclosed by the handoff and
has no quarantine or axiom consequence, but increases import scope. No source or frozen text was
edited to accommodate it.

## Independent checks

All Lean/Lake invocations initiated by this audit were serialized with `LEAN_NUM_THREADS=1`
and `nice -n 5`; no resource overrides, package updates, clean, cache fetch, or root regeneration.

Targeted gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-g11hom KAM.Planetary.MaximalStep.HomologicalNodes KAM.Planetary.MaximalStep.RealLipschitzNodes KAM.Planetary.WeakKAM.LipSumNodes
[inp-gate] slot 1 acquired 03:04:11 for KAM.Planetary.MaximalStep.HomologicalNodes KAM.Planetary.MaximalStep.RealLipschitzNodes KAM.Planetary.WeakKAM.LipSumNodes
Build completed successfully (9174 jobs).
exit 0
```

The build replayed pre-existing dependency linter warnings (unused variables/simp arguments and
style warnings in Parameter, Stability, DividedDifference, Divisor, Homological, AffineLie,
StepRealFlow and WeakKAM suppliers). No warning names a new audited module.

Axiom probe: imported exactly the three audited modules into
`.lake/abi-scratch/GAP_P11a_HOM_Audit.lean`, then printed every new public theorem:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAP_P11a_HOM_Audit.lean
'KAM.Planetary.hm_div_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hmMaxSolution_of_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hm_diff_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hmMaxSolution_solve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hmMaxSolution_solve'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hm_bracket_solve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hm_bracket_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.homological_maximal_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_entire' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_value_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_fderiv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtpRowSum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_row_le_iSup' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iSup_rtpRowSum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rtp_fderiv_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iSup_fderiv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.value_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rl_const_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_lipschitz_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pl4_terms_ctx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pl4_sum_ctx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pl4_terms_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pl4_sum_node' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

Kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.HomologicalNodes KAM.Planetary.MaximalStep.RealLipschitzNodes KAM.Planetary.WeakKAM.LipSumNodes
replaying KAM.Planetary.WeakKAM.LipSumNodes
replaying KAM.Planetary.MaximalStep.RealLipschitzNodes
replaying KAM.Planetary.MaximalStep.HomologicalNodes
exit 0
```

Lint (exit 1 solely for the permitted generated-root exception):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1218 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The brief and explicit handoff exempt this stale-root message; it is not a package finding.
No root file was regenerated.

Protected paths: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` emitted nothing,
exit 0. `git diff inp...HEAD --check` emitted nothing, exit 0. Module headers, copyright,
public imports, docstrings and public sections are present. Maximum line lengths are respectively
99, 97 and 99 characters; file lengths 311, 278 and 227, all within caps. No banned proof escape,
resource override or EuclideanSpace appears. All declarations stay inside KAM.Planetary;
no new root declaration/shadow and no public helper short name reused in other KAM source files
was found by scanning the full declaration inventory.

Transitive import scan: 128 KAM modules, zero providers, zero frozen theorem modules, hence zero
DRAFT_SORRY imports. The 14 frozen definition modules reached (ActionNbhd, ComplexStrip,
FrequencyMap, both HamiltonianVectorField variants, IsDiophantine, IsPrimaryOnStrip,
IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm, Planetary Phase/CircularPoint/CircularTube)
are all SEALED in the current manifest. Their definitions were read; their carriers/conventions
match the uses here. No anchor-sealing or campaign theorem closure follows from these leaf results.

Counterexample sanity probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAP_P11a_HOM_Counterexample.lean
(no output)
exit 0
```

This independently elaborated the two potentially delicate facts used in F1:
`k ≠ 0 → ¬ modeSize k ≤ 1/2` for `k : Fin 1 → ℤ`, and `0 < p11Lambda 1 1`.
The first uses the integer-coordinate bound; the second uses a positive single-mode exponential
sum bounded by Lambda. The zero field, its zero derivative and empty row sum then give the
counterexample described above. This probe checks these facts, rather than claiming a formal
refutation of an unavailable source theorem declaration. Both probe files and their temporary
logs were deleted after incorporating the results into this report.

## Handoff / remaining uncertainty

Do not close the two real-Lipschitz graph nodes on this report. An explicit sign ruling or amended
source contract is needed for F1, and the degree-zero scope needs coverage or an explicit restriction
for F2. The five passing nodes need no new dependency output premise. No suspected defect in a
pinned external paper was established: F1 concerns the project's own blueprint lemma (labelled
“Ours”). Other source adaptations/errata remain inherited, not independently re-audited here.
No Lean proof failure or default-heartbeat design signal occurred.
