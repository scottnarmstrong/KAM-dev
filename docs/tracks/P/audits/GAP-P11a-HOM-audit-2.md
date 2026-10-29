# GAP-P11a-HOM independent audit 2

Overall verdict: **PASS WITH NOTES under the explicit round-2 ruling**. All seven requested
nodes are established under that ruling; **no failing nodes remain**. The real-Lipschitz
nodes retain a candidate source erratum, pending owner review. This is a leaf-package audit,
not a frozen-anchor seal or a proof of a planetary headline.

Audited HEAD `10b98454366091b50d6402f44c2b42e378ed07e1` against branch `inp`
`cda2ca291d9606c00a7ae5ba7fe376fb8218b3b4`, using the complete `git diff inp...HEAD`.
The committed diff has five new files, 1128 added lines: the three Lean modules below,
audit 1 (268 lines), and the handoff (40 lines). The handoff also had a pre-existing
uncommitted update containing the controlling OVERNIGHT 03:15 ruling; it was read and preserved.

Scope: only `KAM/Planetary/MaximalStep/HomologicalNodes.lean` (H, 311 lines),
`KAM/Planetary/MaximalStep/RealLipschitzNodes.lean` (R, 282 lines), and
`KAM/Planetary/WeakKAM/LipSumNodes.lean` (L, 227 lines). The handoff's R line count of
278 predates the repair. Read AGENTS, PLAN, DECISIONS, the supplied package brief,
the handoff/AUDIT FOCUS, audit 1, relevant Track P statement conventions, P11A design/node
mapping and signature appendix, `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`,
and GAP-PLAN-P2 sections GAP-P11a2-hom/GAP-P11a14. Each of the seven complete NODE records
and its cited blueprint statement/proof was read independently. The explicit user path overrides
the generic brief's main-worktree destination. Only this report was edited outside audit scratch.

## Node contracts

All declaration names have prefix `KAM.Planetary.`. Blueprint locators are in
`blueprint-P/parts/`; DG means `docs/graph/P/DEPGRAPH.md`.

| Node | Export | Verdict | Literal source comparison |
|---|---|---|---|
| `stepP:p11a:hm-div` | `hm_div_node`, H:35 | PASS | DG:23474; p11a2-cutoff-step.tex:187. Gives D/2 for all b in B and all nonzero modes of size at most T. Derives L nonnegative at b from the actual derivative bound. No extended B-divisor premise. Stronger: omits unused source reality/data premises. |
| `stepP:p11a:hm-bracket` | `hm_bracket_node`, H:244 | PASS | DG:23626; p11a2:197. Both bracket equalities, all b in B and all phase points. Uses constructed p11Solve solutions; derives the B-divisor from E-divisors. No solving equation or derivative output assumed. Stronger: norm bounds and reality are unnecessary. |
| `bpP:p11a:homological-maximal` | `homological_maximal_node`, H:274 | PASS WITH NOTES | DG:23437; p11a2:172–198. Existential scalar/vector solutions, full-angle zero-mean polynomial class, domain-local uniqueness, clauses (a)–(e), and final bracket. Reality is an implication in the output specification; source reality specializes it. Neither nonnegative L/M nor the extended divisor is assumed. |
| `stepP:p11a:rl-const` | `rl_const_node`, R:208 | PASS WITH NOTES | DG:23943; p11a2:241, parent 229–235. Full two-step row-sum chain with actual Fourier coefficients. Now assumes 0 ≤ T and covers constants. Nonnegative M1 is the expressly accepted round-2 candidate erratum, not inferred from vacuous coefficient decay. |
| `bpP:p11a:real-lipschitz` | `real_lipschitz_node`, R:253 | PASS WITH NOTES | DG:23853; p11a2:229–242. Actual flow derivative, lattice equivariance, displacement, and both coefficient clauses. No derivative-bound dependency output is an input. Same accepted sign qualification; T = 0 included. |
| `stepP:p11a:pl4-terms` | `pl4_terms_node`, L:189 | PASS | DG:26906; p11a4-limit-family.tex:90–92. Both separate rates g4^j and (2 q g4)^j, with exact coefficients and g4 = g1·2^tau. Adapted schedule matches situation S at p11a4:30–34. |
| `stepP:p11a:pl4-sum` | `pl4_sum_node`, L:209 | PASS | DG:26936; p11a4:94. Summability and every intermediate inequality are exported, including (32/31) Q0 Xi (2/CQ + 1/32), 0.046·2^-10, and 2^-10/16. 46/1000 is exact. |

Quantifiers: the exports are not textual copies of the source binder lists. In hm-div, the
independent universal mode/parameter quantifiers are commuted; the homological inputs interleave
M0/M1 with the other fixed real parameters. All source data still precede the existential
solutions. Their bounds are uniform in parameter, angle, mode and derivative order as required;
no constant gains a wider dependence. R binds polynomial/source scalar data before t and theta;
t in Icc(-1,1) is exactly |t| ≤ 1, with all integer translations. L binds source data d, then
positive small epsilon, then j or the infinite sum. These reorganizations preserve dependence.

The homological source assumes omega real. The current main export does **not** take omega
reality as an input; HmMaxSolution:76–82 contains the implication from omega-real and datum-real
to solution/average-real. Specializing it recovers source (d); the remaining conclusions hold
without reality. This is an equivalent source recovery and a stronger non-reality result,
not a missing reality proof. Audit 1's prose saying omega reality is also a node premise is
inaccurate for the current declaration.

Completeness: all seven gap exports requested by the controlling offload plan are present.
The older design maps hm-coeff/hm-a/hm-bc/hm-d locally into the homological proof; H:120–174
establishes their finite solution, estimates, averages, parameter derivatives and reality.
Global/variational flow suppliers are used after their regularity/boundedness inputs have been
proved in R. The older design's signed homological/flow suppliers are unchanged and outside
the modification scope. No new declaration is SIGNED in the live signature file or design
appendix, so exact signed-ABI and provider/seal-body probes have no new subject here.
`c2-conv#bracket` and the other GAP-P11a14 sub-batch are outside this package's requested slice.

## Audit-1 findings and explicit premise judgments

**F1 is retained as an erratum note, not a round-2 failure.** The handoff ends:

> the premise 0 <= M1 of rl-const/real-lipschitz is accepted as a candidate source erratum

It explicitly says owner review remains and that this is not a round-2 finding. R:205–207
also documents that qualification. The sign is not logically forced by the standalone literal
source: p11a2:233 says "If" the nonzero Fourier coefficients satisfy the decay bound, "then"
Lambda ≤ Lambda_R. It does not require a separate norm bound on a nonempty domain.
For N=1, T=1/2, the zero field, rs=D=1 and M1=-1, the decay condition is vacuous,
Lambda=0 but 2 T M1 Lambda_1 / D = -Lambda_1 < 0. Thus p11a2:233/241 needs the stated repair.
For an actual norm bound on a nonempty domain the sign does follow by evaluating the bound;
that attachment is absent from this standalone lemma. The ruling, rather than a claim of
implication from the old hypotheses, authorizes the present sign premise. No owner approval
or source-text amendment is asserted by this report.

**F2 is repaired.** Compared with ef583e86, the derivative helpers and both node exports now
use `0 ≤ T` instead of `0 < T`; their proofs use nonnegative multiplication and need no
division by T. The defining source polynomial convention p11a2:25 is T ≥ 0. Independent Lean
probes specialized both named exports at T=0: the derivative supremum is ≤ 0 and the whole
dynamic conjunction elaborates. No special constant-field fallback replaces the proof.

Other disclosed premises: rs>0 and D>0 are the source context for the homological coefficient
estimate and Lambda_rs. They are immaterial to the first row-sum/dynamic clauses: these clauses
can be recovered alone by instantiating rs=D=1 and M1=0, without any decay hypothesis. The
coefficient decay itself is explicitly the source's conditional last claim, not a hidden proof
dependency assumed by an unconditional node. L constructs WeakBudgetCtx using free_radius and
weakBudgetCtx_of, so neither budget outputs nor summability are node premises. H's conditional
suppliers may take a B-divisor, but its named node wrappers discharge it. Empty E is handled
explicitly; M nonnegative is derived only when a norm bound can actually be evaluated.

## Every other new public theorem

These are conditional suppliers or elementary supporting facts, with distinct names. None
stands in for a source node with an undisclosed added premise.

| Declaration | Locator | Verdict / mathematical role |
|---|---|---|
| `hmMaxSolution_of_empty` | H:88 | PASS; all parameter-domain clauses are vacuous because every thickening of empty E is empty. |
| `hm_diff_at` | H:99 | PASS; finite solve differentiable in angles under explicit nonzero-divisor context. |
| `hmMaxSolution_solve` | H:111 | PASS; scalar assembly under B-divisor and nonnegative M, explicitly conditional. |
| `hmMaxSolution_solve'` | H:177 | PASS; removes the M sign premise by empty/nonempty E split. |
| `hm_bracket_solve` | H:195 | PASS; derivative/bracket assembly under B-divisor, discharged by node wrapper. |
| `rtp_support` | R:42 | PASS; finite cutoff support. |
| `rtp_coeff` | R:49 | PASS; witness coefficients equal genuine torus coefficients. |
| `rtp_entire` | R:56 | PASS; finite Fourier sum is entire. |
| `rtp_contDiff` | R:60 | PASS; real C2 regularity from finite Fourier representation. |
| `rtp_periodic` | R:73 | PASS; integer-vector periodicity from characters. |
| `rtp_value_le` | R:86 | PASS; global finite coefficient bound. |
| `rtp_fderiv_le` | R:104 | PASS; derivative bound with zero mode removed and T nonnegative. |
| `rtpRowSum_nonneg` | R:143 | PASS; finite sum of coefficient norms. |
| `rtp_row_le_iSup` | R:146 | PASS; finite-family supremum bound. |
| `iSup_rtpRowSum_nonneg` | R:149 | PASS; nonnegative supremum, including empty Fin n. |
| `rtp_fderiv_norm_le` | R:152 | PASS; induced Pi max operator norm, no extra dimension factor. |
| `iSup_fderiv_le` | R:191 | PASS; derivative supremum bound. |
| `fderiv_bddAbove` | R:196 | PASS; establishes boundedness before supremum use. |
| `value_bddAbove` | R:200 | PASS; global value supremum is bounded. |
| `pl4_terms_ctx` | L:37 | PASS; exact separate rates in an explicitly conditional context supplier. |
| `pl4_sum_ctx` | L:109 | PASS; geometric series and exact intermediate numeric chain in that context. |

## Definitions and whole-carrier behavior

| Definition | Classification |
|---|---|
| `HmZeroMeanTrig`, H:48 | Honest domain-local predicate: jointly holomorphic, periodic, self-truncated, zero average on C^n × B. Off-domain values are unconstrained, as in the source. |
| `HmMaxSolution`, H:58 | Honest output specification; not an assumed conclusion bundle. Includes full-angle equation, uniqueness on B, estimates, conditional reality and coefficient decay. Correctly vacuous for empty E. |
| `RealTrigPolyDeg`, R:35 | Honest finite Fourier polynomial predicate. Support lies in a finite degree ball; rtp_coeff identifies the witnesses with actual torus coefficients. Real codomain enforces reality. |
| `rtpRowSum`, R:139 | Actual finite sum of norms of actual nonzero torus coefficients, not a selected surrogate. |

All four definitions are exposed by the public noncomputable section. There are no other new
def/abbrev/structure declarations. Inherited total division in p11Solve is used only at proved
nonzero divisors; zero/outside-cutoff modes vanish. Inherited p11RealFlow (GlobalRealFlow:94)
has an identity branch when no global solution exists, but R proves C2 regularity and global
boundedness before applying real_lipschitz; p11_bounded_global_flow/p11RealFlow_spec make that
branch unreachable here. Real suprema are used with proved upper bounds. No junk branch
supports a claimed result.

Deviation: H imports StepReal and StepBound instead of locally reproving coeff_zero_real and
fderiv_pi_apply as requested by GAP-PLAN-P2:240. This is disclosed in the prover handoff.
It expands the import scope but causes no quarantine or axiom failure. No new deviation was
introduced by the audit. No new suspected defect in an external pinned paper was established;
the retained sign defect is in the project's blueprint lemma labelled "Ours".

## Independent verification

All Lean/Lake invocations initiated by this audit were serial, with LEAN_NUM_THREADS=1 and
nice -n 5. No clean, package update, cache fetch, resource override, source repair, generated-root
regeneration, or state-changing git operation was performed.

Targeted compile gate (exit 0; output excerpt):

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-g11hom KAM.Planetary.MaximalStep.HomologicalNodes KAM.Planetary.MaximalStep.RealLipschitzNodes KAM.Planetary.WeakKAM.LipSumNodes
[inp-gate] slot 1 acquired 03:17:17 for KAM.Planetary.MaximalStep.HomologicalNodes KAM.Planetary.MaximalStep.RealLipschitzNodes KAM.Planetary.WeakKAM.LipSumNodes
Build completed successfully (9174 jobs).
```

The gate replayed pre-existing dependency warnings for unused variables/simp arguments and style;
none names one of the three audited modules. No default-heartbeat elaboration failure occurred.

Fresh axiom probe, importing exactly the three modules and printing all 28 new public theorems:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-g11hom-2-probe.lean
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

The same invocation elaborated two additional T=0 specializations: rl_const_node's first
inequality with right-hand side zero, and real_lipschitz_node's entire dynamic conjunction.
They produced no errors or additional output.

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

The brief and explicit handoff exclude the stale-root message from package findings.
No generated file was edited. The literal lint exit remains recorded above.

Other independent checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: no output, exit 0.
- `git diff inp...HEAD --check` and `git diff --check`: no output, exit 0.
- Source scan: all module/copyright/import/docstring/public-section conventions present;
  lengths H/R/L = 311/282/227, maximum line widths 99/97/99. No forbidden proof escape,
  heartbeat/recursion/synthesis override, or EuclideanSpace token in any audited module.
- Full KAM declaration scan: all 32 new theorem/definition short names are unique relative
  to other KAM files. All new declarations remain in KAM.Planetary; no root shadow is introduced.
- Transitive source-import scan: 128 KAM modules; zero providers, zero frozen theorem modules,
  zero DRAFT_SORRY imports. The 14 imported frozen definition modules are all SEALED in the
  current manifest: ActionNbhd, ComplexStrip, FrequencyMap, HamiltonianVectorField,
  HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero,
  RealHamiltonian, SymplecticForm, Planetary Phase, CircularPoint, CircularTube.
  Their definition bodies were read; domains, Pi norms, period-one characters and Hamiltonian
  sign conventions agree with the audited uses. No frozen theorem/type or seal body is changed.

The report and the original handoff modification are the only worktree-status entries after
verification. Temporary probe and audit log files were removed from `.lake/abi-scratch/`.

## Handoff

All seven named graph gaps pass under the supplied round-2 ruling. The retained qualification
is precisely the accepted nonnegative-M1 source repair for `stepP:p11a:rl-const` and
`bpP:p11a:real-lipschitz`; owner review remains pending. The unchanged blueprint/graph should
not be represented as already amended or owner-approved. Degree-zero coverage is now proved.
No further package code change is requested by this audit, and no frozen anchor or headline
is certified seal-ready by these leaf results alone.
