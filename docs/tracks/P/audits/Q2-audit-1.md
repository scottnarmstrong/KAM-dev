# Q2 independent package audit 1

**Overall verdict: FAIL for complete blueprint-slice coverage; PASS for the two signed numerical statements.** `qb_comp` and `qb_mono` match the authoritative signatures and their numerical proofs are sound. The remaining blocking obligation is the explicit `adm_params` numerical reconciliation: the comparison is with a local projection, not yet with the delivered upstream admissibility threshold. No frozen theorem anchor or provider is owned by Q2, so frozen seal-readiness and frozen seal-body tests are not applicable.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-q2`. Audited HEAD: `9d0803d036bac482cb940f65896280ef2419aef2`. Initial comparison ref `inp`: `00afab9de5797d50e1a1b8123a8101c6fd5f8bbb`. Scope: **only `KAM/Planetary/Quantitative/BudgetCompare.lean`**. Dependency files are read to assess meaning, import closure and consumer applicability; this is not a separate audit verdict on BudgetPositivity, Q1 or B07.

Read AGENTS, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, Q2 handoff, P11C design and its audit, the canonical P11C signatures, Track P statement, the relevant blueprint and node inventory, Q1 threshold formulas, upstream WeakKAM data/schedule/cutoff/admissibility definitions, and the ten transitively imported frozen definitions. The user's exact absolute report destination overrides the generic brief's main-worktree destination. Only this report is a lasting edit; probes are confined to this worktree's `.lake/abi-scratch/` and removed afterwards.

## Blocking finding F1: the upstream comparison attachment is unpaid

**FAIL, coverage/consumer applicability; no counterexample to either signed theorem.** Design `docs/tracks/P/design/P11C-LEAN-DESIGN.md:192` assigns Q2 “qb_comp, qb_mono; Q1, adm_params numerical equality”. The U11a3 row at line 50 says “`p11c_oldThreshold` and mollifier constants are literal numerical projections to identify with upstream, not a second iteration”; section 3, line 39, requires reconciliation before dependent dispatch. The prior design audit explicitly says its approval does not skip the upstream reconciliation gates.

The literal blueprint `blueprint-P/parts/p11a5-quantitative-theorem.tex:40` compares with the **File 11a-3 threshold**, and step `stepP:p11a:qb-comp` at line 48 starts “Let T0,t0,Xi,lambda_max be those of Definition ... adm-params”. The production export at `BudgetCompare.lean:334–359` instead concludes the canonical signed inequality

```lean
0 < thresholds d ∧ thresholds d ≤ p11c_oldThreshold { d with M0 := M0' }
```

Its `qbc_old_eq` at line 274 is `rfl` for the local Q1 definition, expanded into `qbcOldT`, `qbcOldt`, `qbcOldX` and `qbcLam`. It mentions no upstream declaration. The module's 42-module KAM import closure contains no WeakKAM module. A repository-wide search for `oldThreshold` and `selectionAdmissible` finds no bridge between them. The actual upstream `KAM/Planetary/WeakKAM/Admissible.lean:59–64` defines `selectionAdmissible` and `adm_params`; `adm_choice` at lines 256–280 and `free_radius` at lines 316 onward require `ε ≤ selectionAdmissible d`. The local inequality cannot yet discharge that premise in Lean.

There is no obvious contradictory formula: `selectionCN`, `selectionVarpi`, `selectionCQ`, the normalized bump/cutoff constants, `selectionCDio`, `selectionGamma`, `selectionThetaMax`, and the differently associated minima have corresponding numerical formulas. But their equality is not all definitional: max commutation, inverse/rpow forms, regrouped beta powers and min association need justification. In particular upstream M0 is `selectionM₀`, an actual derivative supremum, whereas Q1 stores an independent positive upper bound M0. A receiving adapter must relate these objects and show the comparison applies to the upstream data, retaining the required positivity (or explicitly handle a zero actual M0). Q2 does not supply or consume such an adapter.

Required repair: establish the numerical projection/equality with the delivered upstream threshold under the actual data correspondence, then expose or use the resulting comparison at the consumer boundary. Alternatively an explicit authorized reassignment of this reconciliation must retain the graph stop until its receiving consumer proves it. Do not add the desired threshold inequality as a hypothesis. No source, signature or node mapping was silently changed in this audit.

This finding respects the SIGNED exception in AUDIT FOCUS: the prover correctly follows the narrower signature, so **`qb_comp` passes signature fidelity**. The missing designed attachment prevents certifying the full qb-comp graph node or the complete Q2 slice. The signed `budget` consumer in the signature file (lines 180–186) receives exactly the numerical clauses it requests; that syntactic fit does not establish the upstream weak-KAM applicability required by the blueprint.

## Declaration and node inventory

All names below are in `KAM.Planetary`; line numbers refer to BudgetCompare. PASS is at the declaration's actual numerical scope.

| Node / role | Lean declaration and line | Verdict | Reason |
|---|---|---|---|
| Shared three-branch expression | `qbcLam` :24 | PASS | Literal common minimum, including all denominators and powers. |
| New-threshold expansion | `qbc_lambdaFlat_eq` :29 | PASS | Definitional equality with Q1 lambdaFlat. |
| Branch comparison helper | `qbcLam_mono` :33 | PASS | Explicit scalar order/positivity assumptions; no hidden analytic conclusion. |
| Closeness branch | `qbc_thetaMax_mono` :63 | PASS | Both rho branches; beta increases and M0 decreases. |
| Fixed exponents | `qbc_varpi_eq` :81 | PASS | mu/tau equality suffices. |
| Cutoff positivity helper | `qbc_tbar_sum_nonneg` :85 | PASS | NumericalValid gives nonnegative logarithmic term. |
| Product identity | `qbc_s_mul_tbar` :89 | PASS | Uses s>0 to cancel denominator. |
| qb-mono (ii) | `qbc_s_tbar_anti` :95 | PASS | Log inequality proves s*tbar antitone on (0,1], without assuming its sign. |
| Signed product order | `BudgetOrder` :134 | PASS | Exactly the eleven canonical numerical comparisons, including max diameter. |
| qb-mono (i) | `qbc_cDio_anti` :139 | PASS | Correct beta, M, thickness and diameter directions; positive gap. |
| qb-mono (i) | `qbc_gamma_mono` :166 | PASS | Both min branches improve in the specified order. |
| qb-mono (ii) | `qbc_tbar_anti` :184 | PASS | Monotonic logarithm and reciprocal s. |
| qb-mono (iii) | `qbc_tflat_mono` :204 | PASS | Negative rpow exponent and decreasing C1 handled with positive denominators. |
| qb-mono (iii) | `qbc_xibar_anti` :222 | PASS | Uses the proved s*tbar comparison; reciprocal terms have the correct signs. |
| `stepP:p11a:qb-mono`; budget (b) | `qb_mono` :238 | PASS | Exact SIGNED type; all directions in blueprint line 50 established. |
| Old numerical cutoff | `qbcOldT` :264 | PASS | Actual max with A0, not abs A0. |
| Old numerical collar | `qbcOldt` :267 | PASS | Actual two-branch formula. |
| Old numerical weight | `qbcOldX` :270 | PASS | Contains both collar/strip ratios. |
| Local old-threshold expansion | `qbc_old_eq` :274 | PASS WITH NOTE | rfl for p11c_oldThreshold; not an upstream equality, F1. |
| qb-comp cutoff branch | `qbc_oldT_bounds` :279 | PASS | 1≤T≤tbar. |
| qb-comp collar branch | `qbc_oldt_bounds` :291 | PASS | 0<t, tflat≤t≤1. |
| qb-comp weight branch | `qbc_oldX_bounds` :312 | PASS | 0<X≤xibar, retaining both ratios. |
| Signed budget (a) | `qb_comp` :334 | PASS numerical statement | Exact SIGNED type, positivity and all three minorant comparisons. |
| `stepP:p11a:qb-comp`; budget (a) upstream application | No reconciliation declaration/application | FAIL coverage | File 11a-3 receiving threshold not identified, F1. |
| `bpP:p11a:budget` Q2 contribution | `qb_comp`, `qb_mono` | FAIL complete attachment | Numerical clauses proved; F1 remains. Polynomial/beta clauses belong to Q3/Q4 and are not Q2 omissions. |

No unsigned export is named after another graph node. Distinct helper names are retained; there is no substitution of a conditional helper for a source theorem.

## Definitions and proof review

Exactly five new definitions, no abbreviations, structures or instances:

- `qbcLam`: total real arithmetic expression for a minimum of three branches, parametrized independently to reuse one order proof. It does not assert positivity on arbitrary real inputs. Its helper theorem explicitly supplies the positive denominators needed for its use.
- `BudgetOrder`: Prop-valued numerical product order, definitionally identical to canonical signatures lines 124–127. Equality of mu/rho/tau fixes exponents and cutoff constants. K is compared by its existing Pi max-norm diameter, exactly as designed.
- `qbcOldT`, `qbcOldt`, `qbcOldX`: total scalar aliases for Q1's comparison projection. Max, min, division and real powers are the intended Lean total operations on their whole carriers. Theorems use NumericalValid to establish all relevant positivity/nonzero conditions; no fallback value is exploited.

The mathematical core is faithful to blueprint lines 48 and 50. `qbcLam_mono` proves each min branch is ordered, then qb_comp squares nonnegative lambdaFlat and divides by the same positive 2*N*C1. Decreasing M0 changes only thetaMax. qb_mono combines antitone cDio and tbar, monotone gamma/tflat/thetaMax, and antitone xibar; it squares nonnegative lambdaFlat and compares the denominators using decreasing C1.

The potentially delicate product s*tbar is established directly from `1 - 1/x ≤ log x`, s≤s'≤1, N≥1 and pi<16, rather than using an invalid product of two independently ordered factors. NumericalValid is a source-data predicate, not a bundled conclusion. The extra scalar hypotheses in `qbcLam_mono` are appropriate for a separately named general helper and are discharged at both uses. No conclusion-shaped premise, new norm instance, enlarged constant dependence or unguarded singular case was found.

## Import, naming, formatting and comparison hygiene

A recursive source-import scan counted 42 KAM modules, with **no providers and no frozen theorem imports**. The ten frozen imports are all manifest-state **SEALED definitions**: actionNbhd, complexStrip, hamiltonianVectorField, hamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, omegaZero, symplecticForm, and Planetary.Phase. No DRAFT_SORRY anchor enters the closure. The literal definitions retain `Fin n → ℝ/ℂ` and the existing canonical phase/symplectic conventions. There is no frozen theorem for Q2 to type-match or seal; copied canonical helper signatures are the applicable test.

All 23 new declaration short names were searched against other KAM Lean sources: no duplicate declaration found. All are scoped under KAM.Planetary, with no `_root_` declaration or harmful root shadow. The file is 361 lines, maximum Unicode line width 97, with copyright, `module`, public imports, module docstring and an exposed public noncomputable section. The forbidden-pattern scan returned no matches for sorry/admit/axiom/unsafe/opaque, EuclideanSpace, set_option or `_root_`. No resource override or default-heartbeat design failure occurred.

The required full `git diff inp...HEAD` was inspected. Git warns:

```text
warning: inp...HEAD: multiple merge bases, using e631fe0e7ba0a70ccfa647c4c28194642c373eba
```

At the initial inp ref it contains five additions: BudgetCompare (361 lines), BudgetPositivity (209), inherited WeakKAM/Admissible (358), and inherited B07 audit/handoff (175/28). `git show --stat HEAD` isolates the Q2 commit to BudgetCompare and BudgetPositivity, 570 inserted lines. The pre-existing untracked Q2 handoff is preserved. The historical B07 audit describes an older 324-line source; its findings were not blindly applied to the current 358-line upstream file, which now includes `adm_choice_initial`.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
# empty, apart from the merge-base warning
exit 0

git diff --check inp...HEAD -- KAM/Planetary/Quantitative/BudgetCompare.lean
# no whitespace diagnostics, apart from the merge-base warning
exit 0

git diff --check inp...HEAD
docs/tracks/P/audits/B07-audit-1.md:175: new blank line at EOF.
exit 2
```

The last issue is inherited documentation whitespace outside the audit scope. It does not affect Q2 proof or module hygiene, and was not repaired.

## Independent Lean checks

All audit-launched Lean/Lake operations were sequential, with `LEAN_NUM_THREADS=1` and niceness 5. The build used the prescribed compile gate. No clean, update, cache retrieval, library rebuild from scratch, generated-root regeneration, state-changing git command or production source edit was performed.

### Targeted build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q2 KAM.Planetary.Quantitative.BudgetCompare
[inp-gate] slot 2 acquired 19:49:32 for KAM.Planetary.Quantitative.BudgetCompare
Build completed successfully (9088 jobs).
exit 0
```

A compile-slot wait preceded acquisition. No warnings or errors were emitted in this independent build.

### Exact signatures, explicit applications, and axioms

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q2Audit.lean
exit 0
```

The disposable probe copied the canonical qb_comp and qb_mono types under fresh names and supplied explicit bodies `by exact KAM.Planetary.qb_comp d hd M0' h0 hM` and `by exact KAM.Planetary.qb_mono d d' hd hd' h`. Bidirectional `type_of%` examples checked type equality with the actual exports. The signed BudgetOrder body was copied independently and compared by `rfl`. Both theorem headers are also textually identical to the signature file modulo whitespace. No canonical sorry body was imported or copied into a proof. There were no probe errors or warnings.

`#print axioms` was run on **every one of the 18 public theorems** in the audited module. Exact output:

```text
'KAM.Planetary.qbc_lambdaFlat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbcLam_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_thetaMax_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_varpi_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_tbar_sum_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_s_mul_tbar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_s_tbar_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_cDio_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_gamma_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_tbar_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_tflat_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_xibar_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qb_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_old_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_oldT_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_oldt_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_oldX_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qb_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.BudgetCompare
replaying KAM.Planetary.Quantitative.BudgetCompare
exit 0
```

One invocation, with the audited lemma module. No provider exists in this package. BudgetPositivity is an imported dependency, not a second audited package or separate replay target; the 18 axiom closures above include the dependencies used by the audited exports.

### Repository lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (900 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The **only** failing condition is the stale generated KAM.lean, expressly permitted by the audit brief. All module checks, the frozen-anchor guard and all 144 elaborated ABI hashes pass. The root was left untouched. Thus lint is PASS WITH NOTES within the authorized exception; it does not remove coverage finding F1.

## Uncertainties, source defects, deviations and deliverable

No new suspected pinned-paper erratum was found. No external PDF was independently re-audited; this package proves local numerical inequalities against the pinned blueprint/design contracts. F1 is an unpaid design-to-upstream attachment, not a demonstrated false inequality or a defect attributed to a paper. The design's previously recorded stale Part-11 minorant citation (design line 178) and CP11 B.6 candidate (line 183) are outside Q2 and were not used to justify its proofs. No source repair or additional mathematical deviation was introduced.

Per-anchor verdict: **not applicable** (no frozen anchor/provider). Per-export verdict: **PASS** for signed qb_comp and qb_mono; **FAIL** for full qb-comp source/graph coverage until F1 is discharged. The remaining Q3/Q4 polynomial claims were neither required of this module nor certified here. No theorem closure beyond these numerical exports is claimed.

The live inp ref advanced during validation to `d343cead359c794f416340f529531719f7b449d2`. Repeating the protected-path diff still selects the same merge base and is empty. Audited HEAD and production source stayed unchanged. This report is the sole audit-created lasting file, at the user's exact requested path. All audit-owned probes/logs under this worktree's `.lake/abi-scratch/` are removed; the pre-existing untracked handoff is preserved. No commit was made.

Input SHA-256 values:

```text
BudgetCompare.lean: 41c233e56a78b52dfb03f21e4aa4c7b206c55ff5604c4dcdc5e6f4fa0a1cc11f
P11CSignatures.lean: 34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079
P11C-LEAN-DESIGN.md: 51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36
p11a5-quantitative-theorem.tex: f4ea938ec9baf0a280fded708fc7b2bbac4584a6347ad9d49da1291c73ad9b1d
```

Final validation: `git diff --check` exits 0; `git diff --no-index --check /dev/null /root/code/KAM-inp-p11c-q2/docs/tracks/P/audits/Q2-audit-1.md` exits 0. Final status contains only the new report and the pre-existing Q2 handoff. No tracked changes or audit-owned scratch files remain.
