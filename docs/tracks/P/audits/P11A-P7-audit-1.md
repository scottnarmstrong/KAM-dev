# P11A-P7 independent audit 1

Date: 2026-10-29 UTC. **Verdict: PASS WITH NOTES for the round-1 deliverables only.**
No seal is proposed: this slice exports infrastructure, not a provider or frozen theorem.
The six signed declarations pass fidelity; the unsigned specification passes its exact
parametric-body check; all delivered estimates and mean identities pass proof review.
The notes concern the permitted generated-root lint exception, compiler warnings, and
module placement. They do not promote `avg_slow` or the physical headline to proved.

## Snapshot and authority

Worktree: `/root/code/KAM-inp-p11ap7`; branch `inp-p11ap7`.
HEAD: `474bdfa20f639d7584b711767e778bcf8b0b5187`.
The observed `inp` tip was `44a569f406eb196ae7190782caf2a172a0b9a91e`.
The initial working tree was clean. During the audit the shared inp ref advanced to
`9343898cd21e2f7181069e48a2ce217073e714a8`. A final fresh `git diff inp...HEAD`
was byte-identical to the initial comparison (SHA256
`4615078cd2ab5dfc9f474674e8a3aa436993e9ef99583322d763dfcd15e1c4ff`);
both merge bases and the audited HEAD remained unchanged. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the named handoff,
track P statement, P11A design/node table, and the relevant preparation blueprint.
The prompt's explicit absolute output path overrides the generic brief's main-worktree instruction.

Used the lean-statement-audit skill for literal-body, premise, and semantic checks.
No manifest entry exists for these new infrastructure exports; frozen-provider type and
seal-body tests are consequently N/A. Imported frozen carriers retain their manifest authority.

Inspected `git diff inp...HEAD` (1739 lines including headers; 11 files, 1673 insertions).
Git warns `multiple merge bases, using 983fa887bea1c786de978aeffbbab517432a16f3`.
The other merge base is `b4370089886077a54092c2a0c9693d877ff400ee`.
The diff contains Fast, FastBridge, FastDivisor, FastParams, LogBounds, the five Slow modules,
and the handoff. The Fast files are inherited P5 dependencies; their diff was inspected for
context, but this verdict audits only the five files specified in AUDIT FOCUS.

The handoff at lines 45–47 explicitly rules that `avg_slow` and its steps are split into
P7b/P7c/P7d and **are not findings here**. Thus the old design rows at
`docs/tracks/P/design/P11A-LEAN-DESIGN.md:171–175` do not enlarge this audit.
The present slice supplies the listed data and inputs to `as-osc`; it does not establish
that entire graph step. No unsigned export here uses a graph node's name to claim its
unproved literal conclusion. `secular_extract` explicitly claims only extracted components.

## Signed declarations and parametric specification

Authority: `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean:958–1036`.
SHA256 of that signature file:
`fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.

A fresh Python comparison removed whitespace only from each complete declaration,
including structure fields and deriving clause. All six signed declarations matched.
For `P11SlowSpecOf`, the comparison changed the declaration name, replaced the D
parameter by C and Fast parameters, and deleted exactly
`let C := p11SecularData D` and `let Fast := p11FastData D eps`.
The remaining complete header/body matched after whitespace removal, with no changed
conjunct, constant, domain, quantifier, derivative order, or witness scope.

```text
p11Rescale TOKEN_MATCH True
p11PreparedBox TOKEN_MATCH True
p11K2 TOKEN_MATCH True
p11s2 TOKEN_MATCH True
P11SlowData TOKEN_MATCH True
p11PartialVec TOKEN_MATCH True
P11SlowSpecOf PARAMETRIC_TOKEN_MATCH True
```

A temporary Lean probe copied the five signed definitions under fresh `audit_` names,
then checked `example : @audit_<name> = @<name> := rfl` for each. The structure was
checked textually in full (not equated with a separately created inductive type).
The probe also copied the entire transformed signed specification and checked
`example : @audit_SlowSpecOf = @P11SlowSpecOf := rfl`. All elaborated successfully.
This verifies the claimed definitional compatibility without introducing the absent
signed wrapper or importing draft signatures with proof holes. A future actual wrapper
must still be checked when it lands.

## Declaration ledger

All names below are in `KAM.Planetary`. Locations are relative to
`KAM/Planetary/Preparation/`. PASS refers to the literal delivered declaration,
not completion of its eventual consuming graph node.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| sec-E data | `p11Rescale` (SlowData.lean:31) | PASS | Signed rescaling, both action blocks scaled; positions unchanged. |
| sec-E data | `p11PreparedBox` (SlowData.lean:34) | PASS | Signed closed real cube. |
| sec-D data | `p11K2` (SlowData.lean:36) | PASS | Signed cutoff, exact coefficient and logarithm. |
| sec-D data | `p11s2` (SlowData.lean:38) | PASS | Signed minimum of the two action radii. |
| sec-D outputs | `P11SlowData` (SlowData.lean:40) | PASS | Exactly six function fields; no assumed output properties. |
| J jets | `p11PartialVec` (SlowData.lean:49) | PASS | Exact fixed coordinate order, including zero orders. |
| parametric output | `P11SlowSpecOf` (SlowData.lean:54) | PASS | Exact transformed signed body; no existence claim. |
| Cauchy helper | `p11Step` (SlowCauchy.lean:33) | PASS | Literal directional coordinate derivative. |
| Cauchy helper | `p11Step_differentiableOn` (SlowCauchy.lean:36) | PASS | Holomorphic differentiation on the open set. |
| Cauchy helper | `p11Step_iterate_differentiableOn` (SlowCauchy.lean:41) | PASS | Induction over repeated coordinate differentiation. |
| Cauchy helper | `iteratedDeriv_line` (SlowCauchy.lean:49) | PASS | Local line chain rule for the same derivative order. |
| Cauchy helper | `p11Step_iterate_bound` (SlowCauchy.lean:73) | PASS | Sharp one-variable circle estimate, other coordinates fixed. |
| Cauchy helper | `p11Runs` (SlowCauchy.lean:113) | PASS | Literal left fold over coordinate runs. |
| Cauchy helper | `p11Runs_nil` (SlowCauchy.lean:116) | PASS | Empty run is the original function. |
| Cauchy helper | `p11Runs_append` (SlowCauchy.lean:118) | PASS | Append gives the outer iterated coordinate derivative. |
| Cauchy helper | `p11Runs_differentiableOn` (SlowCauchy.lean:122) | PASS | Holomorphy preserved by every run. |
| Cauchy helper | `foldl_step_replicate` (SlowCauchy.lean:129) | PASS | Replication/fold equals function iteration. |
| Cauchy helper | `p11PartialVec_eq_runs` (SlowCauchy.lean:135) | PASS | Run presentation equals the signed ordered definition. |
| Cauchy helper | `p11Runs_bound` (SlowCauchy.lean:152) | PASS | Distinct coordinate runs give factorial product and total radius power. |
| as-osc input | `p11PartialVec_norm_le` (SlowCauchy.lean:198) | PASS | Exact sharp multi-index bound; no commutation premise or dimension factor. |
| polarization helper | `p11_eq_zero_of_diag_of_symm` (SlowJets.lean:32) | PASS | Real and imaginary restricted forms vanish by real polarization. |
| as-osc input | `p11_jets_vanish_of_pow_bound` (SlowJets.lean:46) | PASS | All multilinear jets of order below four, not just diagonal evaluations. |
| mean domain | `p11WorkingDom_isOpen` (SlowMean.lean:32) | PASS | Four strict inequalities and open-strip preimage. |
| as-osc input | `secular_extract` (SlowMean.lean:47) | PASS | Literal projections from the secular specification; slow frequency bound uses order zero. |
| as-osc input | `p11FastMean_differentiableOn` (SlowMean.lean:69) | PASS | Joint parameter holomorphy of the actual torus integral. |
| as-osc input | `p11C_eq_fastMean` (SlowMean.lean:103) | PASS | Quartic error at zero pins C to the mean. |
| as-osc input | `p11C_differentiableOn` (SlowMean.lean:112) | PASS | Restrict the joint holomorphic mean to the zero fibre. |
| as-osc input | `p11R4` (SlowMean.lean:121) | PASS | Actual mean minus constant and quadratic terms. |
| as-osc input | `p11Gbar` (SlowMean.lean:125) | PASS | Actual G minus mean; already represents epsilon times g-bar. |
| as-osc input | `p11G_decomp` (SlowMean.lean:128) | PASS | Exact algebraic decomposition, with no spec assumed. |
| as-osc input | `p11R4_differentiableOn` (SlowMean.lean:137) | PASS | Holomorphic difference including C and Omega terms. |
| as-osc input | `p11R4_bound` (SlowMean.lean:164) | PASS | Exact MF/rz^4 quartic bound on the full stated fibre ball. |
| as-osc input | `p11R4_jets` (SlowMean.lean:174) | PASS | Applies the proved quartic-to-jets theorem for every admissible J. |

The facade `Slow.lean:8–17` correctly publicly imports all four implementation modules
and explicitly labels itself partial. It declares no theorem and claims no seal.

## Premise and semantic audit

Reference S is `Holomorphic.lean:73–145`, the expanded `P11SecularSpec`.
Reference B is `blueprint-P/parts/p11-cp09-preparation.tex:170–181`, especially the
quartic remainder and Cauchy argument in `stepP:p11:as-osc`.
Reference C is the polydisc Cauchy estimate used there (the signed J-jet clause is
`P11ASignatures.lean:995–1000`). Reference Q is polarization of a symmetric jet,
as implemented by the imported `PGAssembly/JetsPolar` theorem.

The following table records each logical input in the new theorem families. Shared
rows apply to every declaration in the named family with that binder. No field is
accepted merely because it is bundled: S was expanded and the proof's projections
were checked against its analytic, radius, derivative, and quartic-error clauses.

| Declaration family | Binder | Bin | Authority / interpretation |
|---|---|---|---|
| Cauchy analytic lemmas | hU | SOURCE | C: open holomorphic domain |
| Cauchy analytic lemmas | hg | SOURCE | C: holomorphy of original function |
| iteratedDeriv_line conclusion | line-membership antecedent | SOURCE | Restriction evaluated where the line lies in U |
| p11Step_iterate_bound, p11Runs_bound, p11PartialVec_norm_le | hR | SOURCE | C: strictly positive Cauchy radius |
| same three | hcl | SOURCE | C: closed polydisc contained in holomorphy domain |
| p11Step_iterate_bound | hiS | SOURCE | Internal induction invariant: new coordinate not yet differentiated |
| p11Step_iterate_bound | hB | SOURCE | Internal invariant: bound on the partially fixed polydisc |
| p11Step_iterate_bound conclusion | hy1 | SOURCE | Internal invariant: differentiated coordinates fixed at centre |
| p11Step_iterate_bound conclusion | hy2 | SOURCE | Internal invariant: remaining coordinates within radius |
| p11Runs_bound, p11PartialVec_norm_le | hM | SOURCE | C: actual norm bound on g, not a derivative bound |
| p11Runs_bound | hnd | SOURCE | Internal invariant: no repeated run coordinates |
| p11Runs_bound conclusion | fixed-coordinate antecedent | SOURCE | Internal invariant discharged at J in the final theorem |
| p11Runs_bound conclusion | free-coordinate antecedent | SOURCE | Internal invariant discharged at J in the final theorem |
| p11_eq_zero_of_diag_of_symm | hs | SOURCE | Q: symmetry of the multilinear form |
| p11_eq_zero_of_diag_of_symm | hd | SOURCE | Q: diagonal vanishing |
| p11_jets_vanish_of_pow_bound | hr | SOURCE | B: positive fibre radius |
| p11_jets_vanish_of_pow_bound | hF | SOURCE | B: holomorphic fibre function |
| p11_jets_vanish_of_pow_bound | hb | SOURCE | B: quartic growth bound, not vanishing jets |
| p11_jets_vanish_of_pow_bound conclusion | j < 4 | SOURCE | B: exact range of jet orders |
| secular_extract and six other spec-dependent mean lemmas | hC | STANDING | S: existing secular package; no slow-averaging result assumed |
| p11C_eq_fastMean, p11R4_bound, p11R4_jets | hJ | SOURCE | S/B: J in ball of radius 2rC |
| p11R4_bound | hz | SOURCE | S/B: fibre norm below rz |
| p11R4_jets conclusion | j < 4 | SOURCE | B: exact range of vanishing jets |

All remaining binders are data or typing, not logical premises: natural dimensions
n,m, sets U,S, functions g,F, points J,y,J0,z,p, radii/bounds R,M,B,r,s,rz,
coordinate i, order k,j, list P, multi-index alpha, maps C,Fast, and multilinear form M.
For the generic Jets section, E, NormedAddCommGroup E, NormedSpace Complex E,
and FiniteDimensional Complex E are TYPING within the stated finite-dimensional
context. FiniteDimensional is unused in the polarization helper (compiler warning),
but is consistent with that context and hides no conclusion. The implicit physical
D is standing data of S. It includes n>=2, positive physical constants and masses;
no slow estimate, mean regularity, jet vanishing, or KAM result is a field of D.
The algebraic fold lemmas, openness lemma, and decomposition have zero logical premises.
The data structure C contains numeric/function data only; P11FastData contains
map,G,f1 only. P11SlowData contains six output functions only.

Logical-input schema counts in the table: SOURCE=22, STANDING=1, RULED=0,
EXCESS=0 (rows shared across families, not a count of elaborated binder occurrences).
For the principal sharp Cauchy export the logical occurrence counts are SOURCE=5,
STANDING=0, RULED=0, EXCESS=0; for the quartic-to-jets export SOURCE=4
(including the quantified j<4 antecedent), STANDING=0, RULED=0, EXCESS=0;
for the R4-jets export SOURCE=2 (hJ and j<4), STANDING=1, RULED=0, EXCESS=0.
No produced analytic obligation is assumed in those exports.

In detail, the Cauchy induction fixes a coordinate after estimating its circle;
Nodup is discharged for List.ofFn. The Pi norm closed ball is exactly a closed
polydisc, so no Euclidean norm conversion or hidden dimensional loss occurs.
Closed containment is available for the planned J-jet use: a centre strictly within
s1/4 plus a closed radius s1/4 remains strictly inside s1/2.

The jets proof applies one-variable decay along every complex line with
radius r/||y|| and constant M||y||^4, handles y=0 and order zero, then uses
symmetry of the analytic jet and real/imaginary polarization. It proves the
whole continuous multilinear map is zero. The mean proof integrates the literal
unit-cube torus mean. Positivity of sigma places real angles in the working strip;
compact parameter integration supplies joint holomorphy. Evaluating the original
quartic inequality at z=0 establishes C=FastMean, so C holomorphy is proved,
not imported as an extra premise. MF/rz^4 uses proved rz>0.

## Definition classification

| Definition | Classification and full-carrier assessment |
|---|---|
| p11Rescale | Literal signed affine rescaling, including its degenerate eps=0 evaluation |
| p11PreparedBox | Literal signed Cartesian product of closed intervals |
| p11K2 | Literal signed real formula; total real log/division conventions, no fallback branch |
| p11s2 | Literal signed real minimum/formula; no altered exponent or off-domain branch |
| P11SlowData | Literal signed output data carrier, with derived Inhabited only |
| p11PartialVec | Literal signed fold; zero entries and n=0 follow the same formula |
| P11SlowSpecOf | Authorized output specification, exactly parametric signed body; not an input gate or existence proof |
| p11Step | Literal fderiv applied to Pi.single, on the entire function carrier |
| p11Runs | Literal fold of function iterates, including the empty list |
| p11R4 | Literal subtraction formula, no choice or artificial extension |
| p11Gbar | Literal subtraction formula; no extra epsilon inserted |

For every row: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL;
CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.
These definitions perform no classical witness selection. Their analytic theorems
apply on the actual source domains; total fderiv/log conventions are not used to
claim a bound or holomorphy off those domains. This output specification is the
explicitly authorized signed contract, not a new hypothesis replacing its proof.

## Independent checks

All Lean/Lake commands were serial, with LEAN_NUM_THREADS=1 and nice -n 5.
No subagents, source repairs, git mutations, clean build, cache update, or package edits.
Scratch probes were confined to `.lake/abi-scratch/` and removed after use.

Build command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap7 KAM.Planetary.Preparation.Slow
```

Exit 0. Output included:

```text
[inp-gate] slot 1 acquired 00:41:13 for KAM.Planetary.Preparation.Slow
Build completed successfully (9342 jobs).
```

This targeted facade build covers all four imported modules; most jobs were cached/replayed.
Package warnings: SlowCauchy:88 deprecated if_false, :104 unused simp argument;
SlowJets:42 deprecated zero_apply name, :32 unused FiniteDimensional instance,
:63 two unused simp arguments; SlowMean:96 prefer have to haveI.
Dependency warnings were replayed as well. None is a proof error or forbidden override.

Probe command (exit 0, no errors):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP7Audit.lean
```

It also ran #print axioms on **all 22 new public theorems**, including helper exports.
Exact output:

```text
'KAM.Planetary.p11Step_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Step_iterate_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.iteratedDeriv_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Step_iterate_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Runs_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Runs_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Runs_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.foldl_step_replicate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PartialVec_eq_runs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Runs_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PartialVec_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_eq_zero_of_diag_of_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_jets_vanish_of_pow_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WorkingDom_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secular_extract' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11FastMean_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11C_eq_fastMean' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11C_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11G_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11R4_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11R4_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11R4_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel command (one invocation; exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.SlowData KAM.Planetary.Preparation.SlowCauchy KAM.Planetary.Preparation.SlowJets KAM.Planetary.Preparation.SlowMean KAM.Planetary.Preparation.Slow
```

Exact output:

```text
replaying KAM.Planetary.Preparation.Slow
replaying KAM.Planetary.Preparation.SlowMean
replaying KAM.Planetary.Preparation.SlowJets
replaying KAM.Planetary.Preparation.SlowCauchy
replaying KAM.Planetary.Preparation.SlowData
```

Lint command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1071 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failing item is the generated-root notice expressly permitted by the
brief; KAM.lean was not regenerated. Module hygiene, frozen-anchor guard and
all 144 elaborated frozen ABI hashes passed. Thus lint is PASS WITH NOTES
under this audit contract, not a claimed literal exit-zero lint run.

Static checks: all definitions/theorems occur under the public exposed section
and namespace KAM.Planetary. The facade is import-only and passes the aggregator
exception in the module checker; it exports no local body needing a public section.
A recursive local-import traversal found 296 project modules, including 58 frozen
files, no Provider module, and no DRAFT_SORRY anchor. The scoped files directly
import no frozen theorem. Short-name search over all other KAM Lean sources found
no collision among the 33 new named declarations, including iteratedDeriv_line,
foldl_step_replicate and secular_extract. No root namespace declaration or shadow.
The source lint also checks forbidden escapes, EuclideanSpace, resource overrides,
module headers, exposure, and line lengths.

| Scoped file | Total lines | Maximum characters per line |
|---|---:|---:|
| SlowData.lean | 119 | 98 |
| SlowCauchy.lean | 214 | 99 |
| SlowJets.lean | 91 | 96 |
| SlowMean.lean | 186 | 100 |
| Slow.lean | 17 | 91 |

No file approaches 1500 lines. `git diff --check` exited 0 with no output.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no patch
(only the multiple-merge-base warning quoted above). None of these protected paths
was changed by this audit.

## Notes, source defects, and remaining scope

No suspected defect in the pinned mathematical source or signed declaration was
found in this slice; no mathematical deviation was introduced by the auditor.
The source's quartic remainder, normalization by 2*pi, open polydisc domains,
and all-order J-jet factorial/radius constants are retained.

Placement note: design line 200 maps p11Rescale and p11PreparedBox to Prepared;
they are delivered in SlowData as explicitly briefed in the handoff at line 40.
Prepared must import these declarations rather than redefine them. This is an
acknowledged module-placement difference, not a mathematical correction.

The blueprint's as-osc statement includes the construction of Z, its derivative
bounds and the weighted f2 estimate. Those full conclusions are not established
by the present helper exports. The split ruling at handoff line 45 expressly
assigns those steps to later packages; this report records no proof closure for
them. Likewise no avg_slow, P11SlowSpec wrapper, chosen slow data, prepared
Hamiltonian, or physical theorem is sealed here. Future integration needs fresh
producer-to-consumer checks; the unused or narrowed existing upstream contracts
are not silently strengthened by this report.

The package's old 650-line forecast (design line 736) is planning evidence only;
the delivered five modules total 627 lines and remain individually below the cap.
The prover's forecast for remaining work was not independently validated.

Report-only handoff: this Markdown report is the only repository change. All
report conclusions refer to the pinned local snapshot and scoped module bodies.
