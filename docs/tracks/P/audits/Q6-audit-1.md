# Q6 independent package audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.weak_kam_quantitative` and the complete Q6 design slice. No material proof, signature, premise, norm, constant-dependence, or coverage defect was found. Q6 is helper infrastructure, not a frozen-anchor provider; no frozen theorem is sealed by this verdict. The notes concern inherited comparison noise, generated-root integration, and the intentionally separate K5/K6 API.

## Scope and authority

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-p11c-q6`.
HEAD: `0093556d45c79be33ac36f8f7b706fe86ffeae6a`.
Comparison ref `inp`: `a2464f937a8b578ae414ec08331359284ec94a78`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, Q6-handoff.md and its AUDIT FOCUS,
P11C-LEAN-DESIGN.md (especially sections 3-5, Q6 and the node table), its independent design audit,
the signed `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`, the quantitative blueprint
`blueprint-P/parts/p11a5-quantitative-theorem.tex`, and track P's statement/conventions.
Inspected the frozen definitions used at this boundary, the input/output interfaces, Q4/Q5,
and the upstream data, threshold, evaluation, Lipschitz, displacement, tori, limit and selection exports.
No external pinned PDF was independently re-audited; this is the requested Lean package audit.

Only these production files were audited:

| File under KAM/Planetary/Quantitative | Lines | SHA-256 |
|---|---:|---|
| AssemblyData.lean | 106 | ca9ff14ed8b5c1ebe4e28718346b63ed3cabb0a1a73c81423e613897b33fbaa8 |
| AssemblyTori.lean | 68 | c29916712be1bd886c961203215159df9ab4b19d7a6a06c531c91b2543896953 |
| Assembly.lean | 229 | 34396cb0e38b5d215621f199bfce743bc40c00536704bba4c096e82b55aaa250 |

Signed file SHA-256: `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`.

## Comparison and scope notes

`git diff inp...HEAD` reports multiple merge bases and selects
`c3296afb40a1279f679848a94071b4e640aa8780`. Its full inventory is 14 files,
1614 insertions and 34 deletions: the three Q6 files, four inherited PlanarAssembly files,
KAM.lean, two graph files and four B19/P12-C audit/handoff documents.
The graph changes concern upstream B19 evaluation, not new Q6 topology claims.

The brief's protected-path command
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
it shows five inherited root imports (four PlanarAssembly modules and WeakKAM.Evaluation).
Frozen files, manifest and README have no diff. This is recorded literally, not called an empty check.
`git diff 1083e8c6..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty;
`git diff --stat 1083e8c6..HEAD` contains exactly the three Q6 files, 403 insertions.
The five Q6 commits follow merge `1083e8c6` and touch no protected path.
These inherited integration changes are outside the user's explicit three-file audit scope.

`KAM.lean` additionally needs orchestrator regeneration to include the new modules. The brief
explicitly permits its stale-root lint message. Neither root file nor any production source was edited.

## Signed statement, hypotheses and definitions

The declaration text of `weak_kam_quantitative` through its type is **identical** to signed
P11CSignatures.lean:249-254. An independently copied signature under the fresh name
`q6_audit_signed` elaborated with the body
`by exact weak_kam_quantitative N mu tau s C1`. Both directions of
`example : type_of% @q6_audit_signed := @weak_kam_quantitative` and its converse elaborated.
There is no frozen provider/type or seal-body obligation for Q6: the design explicitly assigns
no provider to this scope. The fresh declaration checks the corresponding explicit-binder application.

The only new definition is `p11c_cDelta` (Assembly:32): a total, explicit real numerical formula,
exactly `selectionCDelta` after substituting `(N,mu,tau,s,C1)`. It has no choice, conditional fallback,
new norm instance, bundled proof assumption, or dependence on K,beta,M,M0,thickness,rho,h,f.
Lean's total log/division/rpow conventions outside the valid region are harmless: positivity is proved
on N>=1, s>0, C1>=1. The theorem chooses 1 only in the incompatible-data branch and explicitly
proves that Valid data with the fixed s,C1 cannot occur there. No theorem relies on a junk value.
No new abbrev, structure, instance, or root-level declaration is introduced.

`p11c_selData_exists` (AssemblyData:70-102) uses exactly NumericalValid and QuantitativeInput.
It chooses `m0=d.M0` and constructs SelectionData with ds.h=h and qbcOfSelection ds m0=d
by reflexivity. The final input clause bounds every diagonal vector derivative, and Real.sSup_le
first bounds selectionDGVector and then selectionM₀ by d.M0. Positivity of d.M0 comes from
NumericalValid; positivity of the actual supremum is never added. The finite-type lower bound
uses a witnessed unit direction, with boundedness supplied by p11c_dg_bdd before le_csSup.
The order-zero case has its own constant bound. Euclidean length, thickening and scalar are
identified explicitly; the top derivative bound still uses independent unit directions and the
Hessian still has its signed max-to-max operator norm. No M0 bridge premise is smuggled in.

The positive branch obtains one `SelectionEvaluationOutput`, not independent incompatible
witnesses. The inspected route is:
`evaluation_bilipschitz` (Evaluation:301) -> `lipschitz_family` (ParameterLipschitz:223)
-> `displacement` (Displacement:246) -> `limit_torus` (Tori:49)
-> `limit_map` (Limit:178) -> `parameter_selection_adapted` (Selection:335).
`free_radius` supplies admissibility and the adapted schedule along this route and directly in Q6's
action-domain estimate. Thus using evaluation rather than directly invoking every intermediate
export implements U11a3/U11a4. The source standing situation is not assumed through the output alias
`situation`. All family, Diophantine, displacement and Lipschitz clauses are outputs.

The zero branch needs f=0 only on the complex source domain. It proves real-domain agreement,
then uses openness to transfer differentiability and fderiv/vector-field equality, including the
orbit clause. No equality outside the analytic domain is assumed.

## Complete node coverage

Locators are in p11a5-quantitative-theorem.tex; A=Assembly, D=AssemblyData, T=AssemblyTori.

| Graph node | Lean realization | Verdict | Reason |
|---|---|---|---|
| bpP:p11a:weak-kam-quantitative, L72-91 | weak_kam_quantitative; QuantitativeFamily; Q4 exports | PASS | Exact signed K1-K4 theorem plus the designed separate K5/K6 data lemmas. |
| stepP:p11a:qt-order, L93 | A:32-51,203-225; thresholds and Valid | PASS | Uniform cDelta chosen before varying data; numerical positivity, positive volume and source premises retained. |
| stepP:p11a:qt-reduce, L95 | D:70-102; A:143,216 | PASS | Exact data reconstruction; actual M0<=input M0; polyBudget_threshold_le applies without extra premise. |
| stepP:p11a:qt-zero, L97 | A:179-200,213-215 | PASS | zero_case and local Hamiltonian transfer; zero displacement; K6 follows also at eps=0. |
| stepP:p11a:qt-iter, L99 | A:143-155; upstream adapted selection route above | PASS | Same Hinf, Kinf, frequencies and internally selected free radius. |
| stepP:p11a:qt-k2, L101 | A:54-76,95-135,156,158-160 | PASS | Domain margin, real differentiability, analytic primary lattice torus, injective derivative, Lagrangian and orbit clauses, Diophantine frequencies. |
| stepP:p11a:qt-k3, L103 | A:150-162,218-220 | PASS | Defect equals evaluation minus (theta,b); both bounds of the signed min with the same uniform cDelta. |
| stepP:p11a:qt-k4, L105 | A:78-92,163-176 | PASS | Both joint max-norm Lipschitz inequalities, Borel cell image, coarse volume bound and compact closed-cell image. Lower bound yields injectivity since 1-2^-10>0. |
| stepP:p11a:qt-k5, L107 | Quantitative.Budget.p11c_budget:159; qb_poly in BudgetPower | PASS | Deliberately separate data theorem, exact signed renamed budget; not an extra assembly hypothesis. |
| stepP:p11a:qt-k6, L109 | Q4 displacement_power_flat:168 composed with family.displacement | PASS | Uniform replacement-beta constant, exponent 1/2 and loss (mu+1)/rho; consumer composition elaborated independently. |

The design (section 5) deliberately splits K5/K6 from the assembly statement. `Assembly` does not
re-export `Quantitative.Budget`; a consumer needing K5/K6 must import that module as well.
This is an integration note, not a missing proved node: the existing Q4 file contains both exact
signed declarations, and the combined-import probe checked their copied signature applications and
composed the family's displacement with displacement_power_flat at the actual beta.
The resulting bound is `||Q.torus b theta-(theta,b)|| <= cD*eps^(1/2)*d.beta^(-p11c_G0 d)`
for all b in Q.good and theta, from Valid, cDelta>0 and eps>=0 only.
No unsigned helper is substituted for a stronger graph-node export. Q7's physical-interface theorem
is outside Q6's assigned slice; this audit does not claim Q7 or the planetary headlines are closed.

## Every new public declaration

Names below are in KAM.Planetary; locations abbreviate the three audited files.

| Declaration | Location | Verdict | Reason |
|---|---|---|---|
| `p11c_euclid_eq` | AssemblyData:29 | PASS | Exact Euclidean finite-sum length; no ambient norm change. |
| `p11c_selectionReal_eq` | AssemblyData:32 | PASS | Definitional equality of real inclusions. |
| `p11c_thick_eq` | AssemblyData:34 | PASS | Same closed Euclidean thickening on the entire carrier. |
| `p11c_scalar_eq` | AssemblyData:40 | PASS | Same finite-type scalar and exponent. |
| `p11c_dg_bdd` | AssemblyData:45 | PASS | Order zero is constant in the direction; positive orders use independent-direction M bound. |
| `p11c_mem_thick` | AssemblyData:63 | PASS | Uses the point itself and nonnegative thickness. |
| `p11c_selData_exists` | AssemblyData:70 | PASS | Constructs ds and m0=d.M0, with exact data equality and actual supremum bound; no new premise. |
| `p11c_asm_isOpen_domain` | AssemblyTori:28 | PASS | Preimage of the open action neighbourhood. |
| `p11c_asm_diffAt` | AssemblyTori:32 | PASS | Holomorphy on open complex domains restricts to real differentiability. |
| `p11c_asm_transfer` | AssemblyTori:53 | PASS | Conditional locality helper: agreement on an open set preserves derivatives and vector field. |
| `p11c_cDelta` | Assembly:32 | PASS | Explicit uniform constant, definition classified below. |
| `p11c_cDelta_eq` | Assembly:38 | PASS | Definitional equality to selectionCDelta. |
| `p11c_cDelta_pos` | Assembly:41 | PASS | Positive for N>=1, s>0, C1>=1, without assumptions on varying data. |
| `p11c_asm_action_lt` | Assembly:54 | PASS | Adapted-radius and action-displacement bounds keep actions inside the original real domain. |
| `p11c_asm_cell` | Assembly:78 | PASS | Half-open angle cube times parameters, correct phase order. |
| `p11c_asm_closed_cell` | Assembly:83 | PASS | Closed angle cube times parameters, correct phase order. |
| `p11c_asm_zpow10` | Assembly:89 | PASS | Exact integer-power conversion. |
| `p11c_asm_zpow18` | Assembly:90 | PASS | Exact integer-power conversion. |
| `p11c_asm_zpow2N` | Assembly:91 | PASS | Exact dimension-dependent integer-power conversion. |
| `p11c_asm_lattice` | Assembly:95 | PASS | All six literal lattice-torus clauses, actual realHamiltonian and open real domain. |
| `p11c_asm_family` | Assembly:138 | PASS | One evaluation output supplies all K1-K4 clauses on Hinf; threshold comparison is proved upstream. |
| `p11c_asm_zero_family` | Assembly:179 | PASS | Local vanishing of f transfers the zero-case family to the same actual Hamiltonian. |
| `weak_kam_quantitative` | Assembly:203 | PASS | Exact signed statement; cDelta precedes d,h,f,eps; positive and zero branches complete. |

## Independent checks

All audit-owned Lean/Lake/kernel invocations were sequential, with `LEAN_NUM_THREADS=1` and
`nice -n 5`. Lint's ABI subprocess inherited those settings. No clean, update, cache fetch,
package mutation, resource-budget override, or git mutation was performed.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q6 KAM.Planetary.Quantitative.Assembly
```

Exit 0. Output began `[inp-gate] slot 1 acquired 01:00:11 for KAM.Planetary.Quantitative.Assembly`
and ended `Build completed successfully (9248 jobs).` Replayed upstream warnings concerned
unused variables/simp arguments and deprecations; no warning was reported in the three Q6 files.
The target builds both imported Q6 helper modules.

2. Copied signed declaration, bidirectional exact-type examples and all 22 axiom probes:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q6Audit.lean
```

Exit 0. Exact axiom output:

```text
'KAM.Planetary.p11c_euclid_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_selectionReal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_thick_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_scalar_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_dg_bdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_mem_thick' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_selData_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_isOpen_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_diffAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_cDelta_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_cDelta_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_action_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_closed_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_zpow10' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_zpow18' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_zpow2N' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_asm_zero_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.weak_kam_quantitative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. One kernel-replay invocation covering all three modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.Assembly KAM.Planetary.Quantitative.AssemblyData KAM.Planetary.Quantitative.AssemblyTori
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.Quantitative.AssemblyTori
replaying KAM.Planetary.Quantitative.AssemblyData
replaying KAM.Planetary.Quantitative.Assembly
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 **only for the permitted stale generated root**. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1167 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

5. K5/K6 signature and consumer-composition probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q6Consumer.lean
```

Exit 0. Imports Assembly and Budget; fresh copies of the signed p11c_budget and
 displacement_power_flat declarations use their actual exports as bodies; the composition described
above elaborates. Complete output:

```text
'KAM.Planetary.p11c_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.displacement_power_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

6. Static checks: all three files have copyright, module, public imports, module docstring and
public section; p11c_cDelta is in the exposed noncomputable section. File lengths are 106/68/229;
no line exceeds 100 Unicode characters. No forbidden proof token, resource override or
EuclideanSpace occurs in the files. A declaration-name scan of every other KAM Lean source found
no reused short name among the 23 new declarations. All are namespaced KAM.Planetary; no harmful
root shadow or new instance was found. `git diff --check inp...HEAD` exited 0 with no whitespace
finding (only the multiple-merge-base diagnostic). Protected-path results are recorded above.

7. Recursive project-import scan from Assembly found 202 KAM modules, no provider import,
and exactly 26 frozen definition modules. Matching manifest entries by their exact `path` found
all 26 SEALED and none DRAFT_SORRY, with no unmatched module. No frozen theorem module is
imported. The axiom results independently confirm no sorryAx enters the proved exports.

## Defects, deviations and handoff limits

No new suspected pinned-source or blueprint mathematical defect was found. No hypothesis,
quantifier, carrier, norm, constant dependence, threshold, or native Hamiltonian was repaired by this
audit. Existing P11C design-audit notes on provenance/module scheduling do not obstruct Q6's
boundary; the p11c_budget rename follows the explicit design ruling. The source's full K1-K6
conclusion is accounted for by the designed split, not attributed to weak_kam_quantitative alone.

The protected root diff is inherited, and stale root regeneration remains the orchestrator's task.
No production edit is requested for the mathematical Q6 slice. This verdict does not certify other
packages merely because they occur in the comparison history or build closure, and does not seal
any DRAFT_SORRY headline.

The only lasting audit edit is this report at the user-specified absolute worktree path.
Disposable probes and logs under `.lake/abi-scratch/` were removed after their evidence was copied here.
