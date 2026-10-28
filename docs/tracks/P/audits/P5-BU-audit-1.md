# P5-BU independent package audit 1

Verdict: **PASS WITH NOTES**, for the action-budget infrastructure slice; independent validation receipts are recorded below. No frozen anchor is proved or made seal-ready by this package. P-G (`KAM.Planetary.properlyDegenerateKAM`) remains outside this slice; its frozen body is `by sorry`, and the provider/type/seal-body comparison is therefore not applicable to P5-BU. This report does not certify the separate P5-FAM package or the campaign theorem.

## Authority and scope

Audited HEAD `3b850defc4f8ded6be790b1ce8f460825dad6cc0`, against `inp` at `b8e023179635e643629844d102983e478c955c1e`, using the required `git diff inp...HEAD`. Git reports two merge bases (`0f347d6926a79e37d59d1e5fd044af61862721ae` and `1005e6394f3da22fb5263f98658969aa2071587c`) and chooses the first. The complete diff comprises ten new modules, including four Family modules. Per the explicit AUDIT FOCUS, the verdict covers only the six `KAM/Planetary/PGAssembly/ActionBudget*.lean` files (850 lines total). Family is inspected only at its consumed interface.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, P5-BU-handoff, P45 design/node ownership table and design audits 1–4, Track P statement, blueprint Parts 4–5 interfaces and the budget at `blueprint-P/parts/p5-pg-assembly.tex:278–288`, the frozen P-G statement, its relevant frozen definitions, PGData, Parameters, Family's measure clause, and P4 TwoScale/MeasureData. The user's exact worktree-local report path overrides the generic brief's main-worktree destination.

Authoritative signature file: `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, SHA256 `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304`. The four signed definitions at lines 1197–1215 and `budget`'s entire statement at lines 1217–1222 are byte-identical to production. A fresh renamed signature/body probe checks the definitions by `rfl`, applies `budget d` to the copied signed statement, and checks both directions with `type_of%`. No signature stub is used as a proof premise.

## Node completeness

| Node | Implementation / locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p5:budget` | `ActionBudget.lean:43`, `budget` | PASS | Literal signed conjunction: positive explicit budget followed by the unchanged unit-cell missed-set estimate, constants fixed before r and mu. |
| `stepP:p5:bu-read` | `ActionBudget.lean:73–106` | PASS | Destructures the proved family specification, uses clause 6, and proves the inclusion into the enlarged missed set using rK>0. |
| `stepP:p5:bu-dio` | `ActionBudgetDio.lean:122`, `budget_dio` | PASS | Exact relative D\\D0 bound with coefficient `4^(b+1)*2*pi*k0*(5*U1+4*U2)*sqrt r`; actual frozen real frequency, alpha_i=2*pi*gamma_i. |
| `stepP:p5:bu-collar` | `ActionBudgetCollar.lean:50,93`, `budget_collar_fast`, `budget_collar` | PASS | Fast Cantor collar and full relative collar; retains `8*(A+Cdio*Cgamma)/vol V + b*k1/16`. |
| `bpP:p5:budget#constant` | `ActionBudgetDefs.lean:29–48`; `budget` | PASS | Exact explicit formula, data-only dependence, justified denominators and strict positivity. |

All five rows assigned to ActionBudget by design lines 202–205 and 223 are established. The unsigned `budget_dio` and `budget_collar` exports state their nodes' actual conclusions; the auxiliary `budget_collar_fast` explicitly states only its fast component.

## Declaration-by-declaration review

All names below are in `KAM.Planetary`. Locations are relative to `KAM/Planetary/PGAssembly/`.

| Declaration | Location | Verdict | Statement / definition assessment |
|---|---|---|---|
| `kamMeasureConstant` | ActionBudgetDefs:29 | PASS | Signed explicit P3 constant. |
| `pgMeasureUpper1` | ActionBudgetDefs:31 | PASS | Signed numerical upper bound with half-volume denominator. |
| `pgMeasureUpper2` | ActionBudgetDefs:40 | PASS | Signed slow lattice constant. |
| `pgBudget` | ActionBudgetDefs:43 | PASS | Signed explicit sum, no existential replacement. |
| `jetBeta_mulVec_real` | ActionBudgetReal:29 | PASS | Actual real beta matrix multiplication under the isometric inclusion. |
| `jpTheta_realSlice` | ActionBudgetReal:38 | PASS | Actual slow-frequency formula on V. |
| `blockFast_freq_append` | ActionBudgetReal:50 | PASS | Unconditional unfolding identity for the original frequency. |
| `jpGrad_real_eq` | ActionBudgetReal:61 | PASS | Reverse real-slice derivative equality. |
| `real_N1` | ActionBudgetReal:68 | PASS | Both required fast-action Lipschitz estimates; mu factor retained. |
| `real_N2` | ActionBudgetReal:106 | PASS | Slow-action Lipschitz estimate for fast frequency; mu retained. |
| `real_N3` | ActionBudgetReal:124 | PASS | Transposed real beta lower bound; frozen hsymm supplies transpose equality. |
| `pgMu1` | ActionBudgetData:30 | PASS | Positive explicit minimum of mu0 and the S4 reciprocal bound. |
| `pgMu1_pos` | ActionBudgetData:34 | PASS | Strict positivity of that actual minimum. |
| `pgMeasureData` | ActionBudgetData:43 | PASS | P4 record on arbitrary certified compact positive-volume core; N1/N2/N3 are proved from PGData. |
| `budget_facts` | ActionBudgetData:88 | PASS | Derives all parameter guards, half inner-core and quarter checked-core measures from rstar/kh_dyn. |
| `measure_c1_nonneg` | ActionBudgetData:117 | PASS | Nonnegative real c1 on a certified core. |
| `measure_c1_le` | ActionBudgetData:130 | PASS | Upper bound when core volume is at least half vol V; normalization premise is internal and proved at use. |
| `twoScale_smul_inv` | ActionBudgetDio:28 | PASS | Both two-scale inequalities transported through division by 2*pi; no unnecessary positivity assumptions on gamma or tau. |
| `dio_real` | ActionBudgetDio:47 | PASS | Scalar arithmetic estimate with explicit source bounds; no full budget is assumed. |
| `checkedCore_subset` | ActionBudgetDio:99 | PASS | Definitional inclusion, valid for every r and mu. |
| `actionShell_volume` | ActionBudgetDio:102 | PASS | Total `ofReal ell` formula for open product shell, including empty-shell parameter values. |
| `volume_pgActionDomain` | ActionBudgetDio:111 | PASS | Product formula using admissibility for nonnegative ell. |
| `budget_dio` | ActionBudgetDio:122 | PASS | Complete resonance node, not just an assumed resonance invoice. |
| `one_add_pow_sub_one_le` | ActionBudgetCollar:29 | PASS | Proved numerical inequality for every n and x>=0. |
| `checkedCore_isClosed` | ActionBudgetCollar:40 | PASS | Compact inner core and continuous fast frequency; r>0 suffices. |
| `budget_collar_fast` | ActionBudgetCollar:50 | PASS | Collar union inclusion plus actual one-scale Diophantine estimate. |
| `budget_collar` | ActionBudgetCollar:93 | PASS | Applies domain_collar_helper; proves fast and slow enlargement bounds. |
| `pgMeasureUpper1_nonneg` | ActionBudget:32 | PASS | Direct nonnegativity of the signed constant. |
| `budget` | ActionBudget:43 | PASS | Exact signed theorem; combines the two proved losses and the family estimate. |

## Definitions, hypotheses and adversarial checks

The six new definitions are the four signed constants and `pgMu1`, `pgMeasureData`. There are no new abbrevs, structures, instances, totalized inverses or fallback branches. `kamMeasureConstant` is meaningful on every natural dimension. The three signed data constants depend only on PGData, with a,b>0 already in that source record. `volume_V_pos`, boundedness of V, and the core lower bounds justify their real denominators. In particular tau=n+1 makes the lattice-tail exponent denominator tau+1-n equal 2. The denominator in pgMu1 is strictly positive by LN>=1, LB>=1, Lg>=1 and a>0. The arbitrary-core record has precisely the compactness, subset and positive-volume typing certificates that P4 requires; it does not smuggle any N1/N2/N3 or resonance conclusion into a premise.

The new real N1/N2/N3 proofs use the actual frozen coefficient values on V, not arbitrary off-domain extension values. N3 explicitly uses symmetry, rather than silently interchanging beta and its transpose. The isometric real inclusion preserves the Pi max norm. D\\D0 is included in the resonances on the inner core, with both thresholds multiplied by 2*pi, and `twoScale_smul_inv` supplies the required period-one dictionary. The P4 application uses lambda=l2top, proves 0<lambda<=1, mu<=pgMu1, shell containment and measurability, and bounds its normalized c1 using the half-core measure. The quarter-volume estimate converts the inner-core result to volume D. No unproved hard estimate is assumed.

The collar proof justifies checkedCore measurability and finite measure, controls the fast collar by the boundary layer plus the actual bad-frequency set in V, and bounds the slow shell factor by the proved numerical power inequality and r_k. The positive-volume clause displayed in the blueprint is available from `budget_facts`' quarter-volume bound, ell>=r^2/4>0, and `volume_pgActionDomain`; the fresh probe also derives `0 < volume (pgActionDomain d r mu)` from exactly these exports. It is not a missing source hypothesis.

The signed budget intentionally uses raw tori in the input unit cell. Physical output-cell transport belongs to P5-CT; P5-LO's signed `lower`/`pgLoss` interfaces consume exactly this raw budget and the same explicit constant. Those downstream modules are not present in this worktree, so their eventual implementations are not certified here. Design audit 1's F5 (arbitrary budget witness) remains repaired: both component upper constants and their explicit sum are retained.

The transitive production import traversal reaches 345 local modules and **no provider and no frozen theorem module**. Thus no DRAFT_SORRY theorem import or SEALED-theorem manifest exception is used. Imported frozen definitions were checked at their source interfaces; PGData preserves the original frozen P-G assumptions. All 29 new public short names were searched against other KAM source declarations; no reuse or harmful root shadow was found. Every new declaration is scoped inside KAM.Planetary.

## Notes, defects and scope limits

No blocking mathematical, statement-fidelity, definition or hygiene defect was found in this slice. The split into six focused modules is a harmless structural implementation choice; the largest is 218 lines. All lines are at most 99 characters.

The handoff's suggested source imprecision about lambda is unnecessary: `blueprint-P/parts/p5-pg-assembly.tex:140` defines `lambda2'=lambda2-2*lambda1` and `ell=lambda2'-lambda1`; `Parameters.lean:55` sets precisely these values, and `ActionBudgetDio.lean:138–142` uses l2top=ell+l1=lambda2'. Blueprint line 286's choice is therefore exact. This is a handoff clarification, not a paper erratum or a Lean deviation.

No newly suspected defect in a pinned external paper was identified. The inherited CP10/CP11 allegations in the design were not independently re-adjudicated against PDFs by this package audit. The Track P statement and frozen theorem comments still contain historical pending-approval language; DECISIONS D20 and the manifest govern the approved frozen interface. No source, graph, manifest, frozen file, generated root or README was edited.

## Independent validation receipts

All Lean/Lake invocations from this audit were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean, update, cache retrieval, heartbeat override or source mutation was issued.

1. Targeted compile gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5bu KAM.Planetary.PGAssembly.ActionBudget
[inp-gate] slot 3 acquired 21:29:07 for KAM.Planetary.PGAssembly.ActionBudget
Build completed successfully (9391 jobs).
exit 0
```

The replay log includes inherited unused-variable warnings and axiom informational messages in dependencies. There are no errors or warnings located in the six audited modules. Full log: `/tmp/maud-p5bu-build.log`.

2. Fresh signed-body/type equality, definition equality, positive action-domain volume and complete axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5BUAudit.lean
exit 0
```

The successful run has no errors or warnings, and prints the following 29 axiom receipts. Log: `/tmp/maud-p5bu-probe-final.log`.

```text
'KAM.Planetary.pgMeasureUpper1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.one_add_pow_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.checkedCore_isClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.budget_collar_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.budget_collar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgMu1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgMu1_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgMeasureData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.budget_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measure_c1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measure_c1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.kamMeasureConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgMeasureUpper1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgMeasureUpper2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgBudget' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.twoScale_smul_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.dio_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.checkedCore_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.actionShell_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_pgActionDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.budget_dio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jetBeta_mulVec_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jpTheta_realSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.blockFast_freq_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.jpGrad_real_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_N1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_N2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_N3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An earlier auditor scratch attempt used private `import` before `public section` and failed with private-import visibility errors (log `/tmp/maud-p5bu-probe.log`). Changing only that scratch line to `public import` resolved the probe. Those failed elaboration recovery messages are not production sorries and are not validation evidence; the clean rerun above is the receipt.

3. Kernel replay, one invocation for all six lemma modules (no provider in this slice):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.ActionBudget KAM.Planetary.PGAssembly.ActionBudgetDefs KAM.Planetary.PGAssembly.ActionBudgetReal KAM.Planetary.PGAssembly.ActionBudgetData KAM.Planetary.PGAssembly.ActionBudgetDio KAM.Planetary.PGAssembly.ActionBudgetCollar
replaying KAM.Planetary.PGAssembly.ActionBudgetCollar
replaying KAM.Planetary.PGAssembly.ActionBudgetDio
replaying KAM.Planetary.PGAssembly.ActionBudgetData
replaying KAM.Planetary.PGAssembly.ActionBudgetReal
replaying KAM.Planetary.PGAssembly.ActionBudgetDefs
replaying KAM.Planetary.PGAssembly.ActionBudget
exit 0
```

Full log: `/tmp/maud-p5bu-kernel.log`.

4. Source lint, including the elaborated frozen ABI probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (947 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

This is **PASS WITH NOTES under the brief's explicit generated-root exception**: the sole failing diagnostic is the stale generated `KAM.lean`. Module checks, forbidden-token/line-size checks, frozen-anchor guard and all 144 ABI hashes pass. No generated file was repaired. Full log: `/tmp/maud-p5bu-lint.log`.

5. Integrity checks:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
# empty stdout; only the documented multiple-merge-base warning on stderr
git diff --check inp...HEAD
# exit 0; only the same merge-base warning
git diff --check
# exit 0
```

Code-masked token inspection found none of `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option` in the six audited files. File line counts: ActionBudget 108, ActionBudgetCollar 179, ActionBudgetData 158, ActionBudgetDefs 51, ActionBudgetDio 218, ActionBudgetReal 136. Their maximum line widths respectively are 96, 98, 97, 97, 97, 99. All six have copyright, module, public imports, module documentation and an exposed public section.

Scratch `P5BUAudit.lean` was deleted after verification. Final status contains only the pre-existing untracked `P5-BU-handoff.md` and this new report; tracked files remain unchanged. Report formatting was checked for trailing whitespace, balanced fences and a terminal newline. No state-changing git command was run. The report is complete at the requested absolute path inside this package worktree.
