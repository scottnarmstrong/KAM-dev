# Q2 independent package audit 2 (delta)

**Verdict: PASS WITH NOTES. F1 is resolved at the explicitly stated positive-actual-M0 boundary.**
The signed `qb_comp` and `qb_mono` remain unchanged and pass. The new adapter proves equality with
the delivered B07 threshold and uses `qb_comp` at that boundary. No frozen anchor/provider is owned
by Q2, so frozen seal-readiness and seal-body probes are not applicable. This is numerical Q2
coverage, not completion of weak KAM, Q3/Q4, or a campaign theorem.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-q2`.
Audited HEAD: `e30f45b8c4c77ec8e16da92ec77644533127f38e`.
Delta base: `e0658f79`. Initial `inp`: `d69dedecde7104870d7281ffe9dba51228f5e523`.
The user's exact absolute report destination overrides the generic brief's main-worktree destination.
Only this report is a lasting audit edit; temporary probes use `.lake/abi-scratch/`.

Read the package brief, AGENTS, PLAN, DECISIONS, Q2 focus/handoffs, audit 1, P11C design and design
audit, canonical signatures, relevant Track P statement/blueprint clauses, Q1 formulas and delivered
B07 definitions/consumer. Audit 1's unchanged mathematical review is carried forward; this round
independently checks the delta, signatures, boundary applicability and hygiene.

## Delta and statement preservation

`git diff e0658f79..HEAD` consists of **one new file, 137 insertions, zero deletions**:
`KAM/Planetary/Quantitative/BudgetAdmissible.lean`. Thus “only appends” means an additive new module,
not an appended section in BudgetCompare. Every previously tracked file is unchanged. In particular,
BudgetCompare and BudgetPositivity compare byte-for-byte equal to e0658f79.

The full `git diff inp...HEAD` was inspected, including inherited B07 and audit documentation.
It contains eight added files, 1487 inserted lines. Git warns of multiple merge bases and selects
`e631fe0e7ba0a70ccfa647c4c28194642c373eba`. This inherited history is distinct from the 137-line delta.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty except that warning.
No protected or generated file was edited.

The **complete** qb_comp and qb_mono declaration headers are textually identical to the canonical
signature file modulo whitespace; BudgetOrder's complete definition is likewise identical.
Disposable Lean probes copy both canonical signatures, explicitly apply the production exports,
and check types in both directions using `type_of%`. No canonical draft proof is imported.

## F1 reconciliation and consumer applicability

Design `P11C-LEAN-DESIGN.md:50,192` requires literal numerical identification with upstream
adm_params; blueprint `p11a5-quantitative-theorem.tex:48` compares against File 11a-3.
The new module imports the actual `KAM.Planetary.WeakKAM.Admissible`, rather than reconstructing
another disconnected threshold.

`qbcOfSelection` (line 28) copies all eleven numerical/geometric fields from SelectionData:
mu/rho/tau/vartheta/s/beta/M/C1/epsLoss/K and independent upper bound M0=m0. The equality specializes
M0 to **the actual `selectionM₀ d`**, the upstream derivative supremum (`Admissible.lean:28`).
The compact set and its ambient Pi max-norm diameter are preserved literally.

The projection chain proves normalized mollifier and extension-constant equality, exponent/log
identity, T0, cDio, gamma, t0, Xi and thetaMax equality. It explicitly handles beta rpow splitting
under beta>0, negative half power versus inverse sqrt, max commutation, and min association.
The main equality (lines 114–122) expands `qbcLam` and **the actual selectionLambdaMax**, including
all three branches and C1*t0/8, and identifies their squared thresholds. The difference between
integer 2^(-10) and inverse-power notation is proved. No standalone lambda-equality export is
needed: the full lambda expression is identified within the threshold-equality proof.

`qbc_comp_selectionAdmissible` (lines 128–135) calls the unchanged `qb_comp` with
`M0' := selectionM₀ d`, then rewrites using the proved equality. The record update from that
application is definitionally the same qbcOfSelection correspondence at actual M0. Its conclusion
is literally `0 < thresholds _ ∧ thresholds _ ≤ selectionAdmissible d`.

**Scope note N1:** this comparison helper assumes NumericalValid of the projected upper-bound
data, `0 < selectionM₀ d`, and `selectionM₀ d ≤ m0`. These are explicit numeric/source-data
conditions, not a desired admissibility conclusion. The equality theorem itself has no extra
hypotheses beyond SelectionData. Neither this audit nor the module proves positivity of actual
M0 from SelectionData or covers actual M0=0 in the comparison helper. This retains the positive
M0' boundary of the approved signed qb_comp (as requested by audit 1); consumers must discharge
these premises. It must not be cited as an unconditional comparison for all SelectionData.

An independent disposable consumer probe supplies `0 ≤ ε` and `ε ≤ thresholds _`, composes with
the new inequality, invokes **upstream `adm_choice`**, and extracts
`SelectionAdmissibility d (adm_params d ε)`. This checks the receiving boundary, including the
nonnegative-ε premise and the actual conjunction structure of adm_choice. The probe was:

```lean
example {n : ℕ} (d : SelectionData n) (m0 ε : ℝ)
    (hd : (qbcOfSelection d m0).NumericalValid) (h0 : 0 < selectionM₀ d)
    (hM : selectionM₀ d ≤ m0) (he : 0 ≤ ε)
    (hε : ε ≤ thresholds (qbcOfSelection d m0)) :
    SelectionAdmissibility d (adm_params d ε) := by
  exact (adm_choice d ε he
    (hε.trans (qbc_comp_selectionAdmissible d m0 hd h0 hM).2)).2.1
```

A7 remains upstream's
separate initial theorem, as documented in B07; it is not silently included here.

## Declaration and node table

All declarations below are in KAM.Planetary, in BudgetAdmissible unless specified.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Data projection | qbcOfSelection (28) | PASS | Literal field correspondence; M0 is explicit. |
| Mollifier identity | qbc_bump_eq (41) | PASS | Same normalized function, whole real carrier. |
| Cutoff identity | qbc_cutoffConstant_eq (45) | PASS | Derivative integrals, finite products and suprema retained. |
| Schedule exponent | qbc_varpi_sel (55) | PASS | Same exponent; no new premise. |
| Cutoff logarithm | qbc_A0_sel (61) | PASS | Same CN and varpi. |
| T projection | qbc_oldT_sel (67) | PASS | Literal selectionT₀. |
| Diophantine constant | qbc_cDio_sel (73) | PASS | Positive beta justifies rpow_add. |
| Frequency scale | qbc_gamma_sel (84) | PASS | Literal selectionGamma, inverse sqrt identity. |
| Collar projection | qbc_oldt_sel (95) | PASS | Literal selectiont₀. |
| Weight projection | qbc_oldX_sel (102) | PASS | Literal selectionXi, both reciprocal ratios retained. |
| Closeness projection | qbc_thetaMax_sel (109) | PASS | rfl at actual selectionM₀. |
| qb-comp / budget (a), reconciliation | qbc_oldThreshold_eq_selectionAdmissible (114) | PASS | Full upstream threshold equality. |
| qb-comp / budget (a), application | qbc_comp_selectionAdmissible (128) | PASS WITH NOTE N1 | Uses qb_comp at upstream boundary with positive actual M0. |
| Signed comparison | BudgetCompare.qb_comp (334) | PASS | Unchanged exact approved signature. |
| qb-mono / budget (b) | BudgetCompare.qb_mono (238) | PASS | Unchanged exact approved signature and round-1 proof. |

No unsigned declaration impersonates a stronger graph node. Q2's numerical equality/application
obligation is now supplied as an additive adapter. Q3/Q4 polynomial and beta claims are outside
this delta; the entire budget proposition is not certified by this table.

## Definition classification and hygiene

The sole delta definition is qbcOfSelection: a total record projection plus a freely supplied M0
bound. It has no fallback/junk branch, new instance, proof-valued output field, assumed estimate,
or hidden norm change. Existing qbcLam/BudgetOrder/qbcOldT/t/X are unchanged from audit 1.

All 13 new declaration short names were searched against other KAM Lean files: no duplicate.
Everything is scoped under KAM.Planetary; no root shadow. BudgetAdmissible has 137 lines, maximum
Unicode width 96; BudgetCompare has 361 lines, maximum width 97. Both meet the 100-character
and 1500-line caps. Module header, copyright, public imports, docstring and exposed public
noncomputable section are present. Forbidden-token/resource-override/EuclideanSpace scans have
no matches. No heartbeat failure or override occurred.

The new import closure contains 67 KAM modules, no provider and no frozen theorem. Its twelve
frozen definition modules are all manifest-state SEALED: ActionNbhd, ComplexStrip, FrequencyMap,
HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals,
OmegaZero, RealHamiltonian, SymplecticForm, and Planetary.Phase. No DRAFT_SORRY dependency enters.

## Independent checks

All Lean/Lake commands were sequential, with LEAN_NUM_THREADS=1 and nice -n 5. The build used
the prescribed compile gate; its wait was allowed to finish. No clean/update/cache operation,
root regeneration, production source edit or state-changing git was performed.

### Targeted build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q2 KAM.Planetary.Quantitative.BudgetAdmissible
[inp-gate] slot 3 acquired 21:21:02 for KAM.Planetary.Quantitative.BudgetAdmissible
✔ [9113/9113] Built KAM.Planetary.Quantitative.BudgetAdmissible (19s)
Build completed successfully (9113 jobs).
exit 0
```

The build replays existing warnings in upstream Schedule, CutoffTensor, CutoffScale, Cutoff,
FourierCutoffTail, StripBudget and Admissible (unused binders/simp arguments, deprecated API,
and haveI style). No warning/error is attributed to the new adapter. The final committed source,
including the prover's removal of diagnostic print commands, was independently built here.

### Signature, boundary and axiom probe

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q2Audit2.lean
exit 0
```

The exact-type and explicit-application probes passed, as did the concrete adm_choice consumer
probe described above. Every one of the twelve new public theorems and both signed main exports
was queried. Exact output:

```text
'KAM.Planetary.qbc_bump_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_cutoffConstant_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_varpi_sel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_A0_sel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_oldT_sel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_cDio_sel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_gamma_sel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_oldt_sel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_oldX_sel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_thetaMax_sel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_oldThreshold_eq_selectionAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qbc_comp_selectionAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qb_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.qb_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.BudgetAdmissible KAM.Planetary.Quantitative.BudgetCompare
replaying KAM.Planetary.Quantitative.BudgetCompare
replaying KAM.Planetary.Quantitative.BudgetAdmissible
exit 0
```

One invocation, both audited lemma modules; no provider module exists.

### Repository lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (901 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the generated-root staleness explicitly permitted by the brief.
Module checks, frozen-anchor guard and all 144 ABI hashes pass. The generated root was left
untouched. No substantive lint failure was waived.

## Source defects, limits and artifacts

No new suspected pinned-source erratum, blueprint contradiction or mathematical deviation was
found. This delta audits a numerical attachment; no external paper/PDF was independently audited.
The prior audit's source-provenance notes remain outside scope. N1 is an explicit applicability
limit, not a silently removed premise. There is no frozen theorem to seal in this package.

Input SHA-256:

```text
BudgetAdmissible.lean: 89878f3e59ea562c510d2ec44cfab2be5faccf857a0850eb2225611056f056e6
BudgetCompare.lean: 41c233e56a78b52dfb03f21e4aa4c7b206c55ff5604c4dcdc5e6f4fa0a1cc11f
P11CSignatures.lean: 34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079
```

Final validation: `git diff --check` and `git diff --check e0658f79..HEAD` both exit 0 with
no output. `git diff --no-index --check /dev/null
/root/code/KAM-inp-p11c-q2/docs/tracks/P/audits/Q2-audit-2.md` exits 1 with no whitespace diagnostics
(the report is an added file). The full historical `git diff --check inp...HEAD` exits 2 solely
for the inherited `B07-audit-1.md:175: new blank line at EOF`, plus the merge-base warning.
This inherited documentation issue is unchanged and outside the delta.

During validation inp advanced to `b8e023179635e643629844d102983e478c955c1e`; the repeated full
comparison uses the same merge base, same eight files, and empty protected-path diff. HEAD and
production source stayed unchanged. Final status contains only this untracked report. The
sole audit-created probe `.lake/abi-scratch/Q2Audit2.lean` has been removed. No commit was made.

Report: `/root/code/KAM-inp-p11c-q2/docs/tracks/P/audits/Q2-audit-2.md`.
