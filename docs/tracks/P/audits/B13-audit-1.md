# B13 independent package audit 1

Date: 2026-10-28. Auditor: maud-p11b-b13-1. **Verdict: PASS WITH NOTES** for the B13 scalar-budget package. All required independent checks are complete; repository lint has the two explicitly recorded out-of-scope failures. No frozen anchor is claimed sealed by this package.

## Scope and authority

Reviewed only `KAM/Planetary/WeakKAM/BudgetsStage.lean` and `KAM/Planetary/WeakKAM/Budgets.lean`, against `inp`, the B13 handoff's AUDIT FOCUS, design row B13 and its node table, both P11B design audits, the amended canonical signatures, and the literal p11a3/p11a4 blueprint statements/proofs. Read AGENTS.md, PLAN.md, DECISIONS.md and the package audit brief first. Read the track-P statement conventions and all frozen definitions in the import closure. No frozen theorem occurs in that closure, so provider/frozen-anchor equality and seal-body probes are inapplicable; the signed infrastructure declarations are checked directly instead.

The user's exact report destination overrides the brief's generic instruction to write in the main inp worktree. This report is `/root/code/KAM-inp-p11b-b13/docs/tracks/P/audits/B13-audit-1.md`.

Snapshot:

- HEAD: `6f7490d1bdba50ea07ef99de165e2aeaab55484f`.
- Comparison ref inp: `e631fe0e7ba0a70ccfa647c4c28194642c373eba`.
- `git diff inp...HEAD --stat`: Admissible.lean +324, Budgets.lean +542, BudgetsStage.lean +302. Admissible is B07 and outside this audit; its supplied interfaces are inspected only as dependencies.
- Budgets SHA256: `8276cf79b6985f52ea2dedce32cb9a8ad33b8a917f0dcc17d74c3ff6dd340e47`.
- BudgetsStage SHA256: `4068d837ca8aae9932e115a21612c443d0cdb5a816570e6180da6dd93494e87c`.
- `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` SHA256: `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`.

## Refutation results and completeness

Both signed exports, `KAM.Planetary.exported_sums` (Budgets:500) and `KAM.Planetary.param_lip_sum` (Budgets:530), have exactly the canonical statement text after whitespace normalization. The former uses the amended parenthesized tsum body at canonical lines 638–639. All seven signed scalar definitions also have identical normalized declaration text. Independent elaboration copies each canonical theorem type under a fresh name, with the proof `by exact <export> d ε he hsmall`; it also compares every copied scalar definition to the production definition by `rfl`. No draft signature module or its sorry bodies is imported.

The scalar slice is complete under the revised design's ownership. The node table's older `exported_sums (local es_4)` row at design:103 must be read together with the explicit revised B10 ownership at design:284 and the added signed helper at design:882: `selection_iteration_parameter_first` supplies E4. B13 neither constructs maps nor advertises that analytic clause. This package does not close the entire four-clause blueprint lemma independently of B10.

| Node / clause | Lean supplier | Verdict | Exact coverage |
|---|---|---|---|
| `bpP:p11a:exported-sums`, E1–E3 scalar slice | `exported_sums`, `wbud_exported` | PASS | Exact amended signed export; source raw scalar premises suffice. |
| `stepP:p11a:es-1` | `wbud_stage` (Stage:182–298) | PASS | All five stagewise bounds, plus nonnegativity; g₁≤1/32 supplied by `wbud_ratios`. |
| `stepP:p11a:es-2` | `wbud_geo`, `wbud_nums`, `wbud_sums_Aα`, `wbud_exported` | PASS | All four source sum bounds with exact 2⁻¹², 3ς₀Q₀/CQ and s₀Q₀/16 constants. |
| `stepP:p11a:es-3`, collar tail | `wbud_tail` (Budgets:429–461) | PASS | All ν, literal shifted sum divided by t_(ν+1), bounded by 2⁻¹⁰. Internally proves the stronger bound 2⁻¹⁰/16. |
| `stepP:p11a:es-3`, real tail | `wbud_tsum_shift_le`, real nonnegativity from `wbud_stage`, E2 in `wbud_exported` | PASS WITH NOTE | Source tail ≤2⁻¹⁰ is a consequence of the stronger total ≤2⁻¹², not a separate signed conjunct. Independently elaborated scratch consequence checks recoverability. |
| `stepP:p11a:es-4` | B10 `selection_iteration_parameter_first` | OUTSIDE B13 | Explicit revision-2 design allocation; no B13 proof credit claimed. |
| `bpP:p11a:param-lip-sum` | `param_lip_sum`, `wbud_lip` | PASS | Exact adapted-radius signature, summability and sum ≤2⁻¹⁰/16. |
| `stepP:p11a:pl4-terms` | `wbud_lip_term`, `wbud_div_t`, `wbud_ratios` | PASS | Separate g₁/2 and g₁q numerator rates, divided by exact geometric t_(j+1). |
| `stepP:p11a:pl4-sum` | `wbud_lip`, `wbud_nums` | PASS | Both resulting rates ≤1/32; 32/31 geometric factor retained. |
| Adapted scalar budgets | `weakBudgetCtx_of` applied to `free_radius`; `wbud_exported` | PASS | General theorem covers adapted a as well as fixed a; no iteration, map or good set premise. |

There are no additional unsigned exports named after graph nodes that weaken their literal conclusions. The `wbud_*` helpers have distinct implementation names and openly conditional statements. Their source-premise bundles are constructed in both signed exports, rather than passed to those exports by a consumer. No hard step is hidden in a new input field: `WeakBudgetHyp` contains positivity, cutoff-loss and the source increment/collar inequalities; `WeakBudgetCtx` adds the upstream proved admissibility and schedule/data identities. The weighted smallness assumption belongs to admissibility A4 and is supplied by B07. This audit does not replace B07's separate audit.

## Constants and definition classification

The handoff's Ξ deviation is sound and stronger than the estimate used in the blueprint. Set w=2^(τ+1)≥2, p=t₀/ς₀≥0, q=ς₀/t₀≥0 and r=T₀ς₀≥0. The literal source definition is Ξ=w(1+p+q+r), so Ξ≥2+p and Ξ≥2r. `wbud_Xi_le` proves these directly (Budgets:112–144). Consequently

- map sum ≤(32/31)Q₀(2+p)/16 ≤(2/31)Q₀Ξ ≤(2/31)2⁻¹⁰ <2⁻¹²;
- real sum ≤(32/31)(16/162)rQ₀ ≤(128/2511)Q₀Ξ <2⁻¹²;
- parameter sum ≤(32/31)(2/162+1/32)Q₀Ξ =(113/2511)Q₀Ξ <2⁻¹⁰/16.

These inequalities use C_Q≥162 and π≤4. The source's looser `2+t₀/ς₀≤2Ξ` (p11a3:353) remains valid; no source bound is weakened and no extra premise is added. The proof of the collar tail uses t_(j+ν+1)≤t_(ν+1) and actual summability before manipulating tsum; it does not exploit the zero convention for nonsummable series.

All new object definitions are literal total real scalar formulas, with the same divisions and exponentiation as the canonical signatures: `selectionΛ`, `selectionA`, `selectionAlpha`, `selectionKappa`, `selectionMapBudget`, `selectionRealBudget`, `selectionQactual`. They introduce no maps, suprema, replacement norms, instances or fallback branches. Real division is total outside positive-radius schedules, as in the signature; every theorem requiring denominator cancellation proves positivity first. In particular, the homological formula at r=0 is not used as a lattice-sum bound. The fixed-radius export admits ε=0 while its s₀ and ε₀ remain positive; the adapted export requires ε>0, preserving positivity of sqrt(2ε/(nC₁)). The two new structures are source-premise bookkeeping propositions, not definitions of a theorem's desired output. No new abbrev is present.

## Every new public declaration

All names below are in `KAM.Planetary`. Stage abbreviates BudgetsStage only in prose; table locators give the actual filename.

| Declaration | Locator | Verdict | Reason / classification |
|---|---|---|---|
| `selectionΛ` | `BudgetsStage.lean:28` | PASS | Literal homological lattice factor; same total real formula as signature. |
| `selectionA` | `BudgetsStage.lean:31` | PASS | Literal angle displacement budget; retains cutoff error and π denominator. |
| `selectionAlpha` | `BudgetsStage.lean:35` | PASS | Literal action displacement budget (n+1)sA/σ. |
| `selectionKappa` | `BudgetsStage.lean:37` | PASS | Literal weighted field budget 2(n+1)A/σ. |
| `selectionMapBudget` | `BudgetsStage.lean:39` | PASS | Literal unscaled derivative budget 2κ+κs/σ. |
| `selectionRealBudget` | `BudgetsStage.lean:41` | PASS | Literal real-flow exponent with radius r−d. |
| `selectionQactual` | `BudgetsStage.lean:46` | PASS | Literal actual Q; distinct from power-law majorant Qsharp. |
| `selectionΛ_one_le` | `BudgetsStage.lean:50` | PASS | Positivity-guarded quotient bound. |
| `selectionΛ_nonneg` | `BudgetsStage.lean:56` | PASS | Natural powers; includes n=0 correctly. |
| `selectionΛ_anti` | `BudgetsStage.lean:62` | PASS | Decreasing on positive radii. |
| `selectionΛ_le_pow` | `BudgetsStage.lean:78` | PASS | Power majorant on 0<r≤1. |
| `WeakBudgetHyp` | `BudgetsStage.lean:93` | PASS | Only positivity, cutoff loss, increment and collar source premises. |
| `weakBudgetHyp_of_adm` | `BudgetsStage.lean:112` | PASS | Constructs premise bundle from admissibility and schedule identities. |
| `wbud_T_pos` | `BudgetsStage.lean:127` | PASS | Stage cutoff positivity. |
| `wbud_σ_pos` | `BudgetsStage.lean:132` | PASS | Positive strip loss. |
| `wbud_σ_le_one` | `BudgetsStage.lean:137` | PASS | Strip loss ≤1 from strip≤1. |
| `wbud_D_pos` | `BudgetsStage.lean:144` | PASS | Positive finite divisor. |
| `wbud_s_pos` | `BudgetsStage.lean:150` | PASS | Positive action radius. |
| `wbud_ε_pos` | `BudgetsStage.lean:156` | PASS | Positive geometric perturbation budget. |
| `wbud_d_pos` | `BudgetsStage.lean:162` | PASS | Positive Fourier loss via loss_choice. |
| `wbud_E_bounds` | `BudgetsStage.lean:170` | PASS | Nonnegative cutoff error ≤1/8. |
| `wbud_stage` | `BudgetsStage.lean:182` | PASS | Full E1, plus nonnegativity; Q≤Q₀g₁ʲ. |
| `wbud_tsum_le` | `Budgets.lean:26` | PASS | Conditional geometric comparison with explicit 32/31 tail constant. |
| `wbud_tsum_le_zero` | `Budgets.lean:46` | PASS | Zero-shift specialization. |
| `wbud_tsum_shift_le` | `Budgets.lean:52` | PASS | Nonnegative summable tail ≤ whole sum. |
| `WeakBudgetCtx` | `Budgets.lean:60` | PASS | Admissibility, standing bundle, and fixed schedule/data equalities only. |
| `weakBudgetCtx_of` | `Budgets.lean:69` | PASS | Builds context from raw admissibility; no requested sums assumed. |
| `wbud_Q₀_nonneg` | `Budgets.lean:79` | PASS | Nonnegative initial Q. |
| `wbud_ratios` | `Budgets.lean:90` | PASS | q,g₁,g₄ rate bounds and exact g₁2^(τ+1)=2g₄. |
| `wbud_Xi_le` | `Budgets.lean:112` | PASS | Stronger Ξ bound and three other source lower bounds. |
| `wbud_geo` | `Budgets.lean:147` | PASS | Four nonnegative scalar budgets dominated at rate 1/32. |
| `wbud_nums` | `Budgets.lean:237` | PASS | All E2 numerical bounds and parameter-sum constant. |
| `wbud_t_pos` | `Budgets.lean:321` | PASS | Positive parameter collar. |
| `wbud_div_t` | `Budgets.lean:327` | PASS | Exact division by geometric collar; retains τ+1. |
| `wbud_lip_term` | `Budgets.lean:336` | PASS | pl4-terms: both separate geometric rates controlled by 1/32. |
| `wbud_lip` | `Budgets.lean:406` | PASS | pl4-sum: summability and exact 2⁻¹⁰/16. |
| `wbud_sums_Aα` | `Budgets.lean:413` | PASS | Angle/action summability and E2 constants. |
| `wbud_tail` | `Budgets.lean:429` | PASS | E3 collar tail from monotone collars and stronger whole sum. |
| `wbud_exported` | `Budgets.lean:464` | PASS | General E1–E3 scalar statement for every constructed context. |
| `exported_sums` | `Budgets.lean:500` | PASS | Exact amended signed statement; ε=0 allowed, fixed s₀ positive. |
| `param_lip_sum` | `Budgets.lean:530` | PASS | Exact signed adapted statement; ε>0, no iteration premise. |

## Independent validation receipts

All Lean/Lake commands below ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`. No concurrent audit Lean/Lake process, resource override, clean, update, cache fetch, or library-wide build was used. The targeted build waited for the prescribed compile gate.

1. Targeted build, exit **0**:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b13 KAM.Planetary.WeakKAM.BudgetsStage KAM.Planetary.WeakKAM.Budgets
   [inp-gate] slot 3 acquired 19:04:49 for KAM.Planetary.WeakKAM.BudgetsStage KAM.Planetary.WeakKAM.Budgets
   Build completed successfully (9106 jobs).
   ```

   No diagnostic in either audited file. Replayed upstream warnings concern Schedule, CutoffTensor, CutoffScale, Cutoff, FourierCutoffTail, StripBudget and Admissible (unused bindings/simp arguments, deprecations, and a haveI style suggestion). The job count is Lake's dependency accounting for the targeted invocation, not a request to rebuild the library.

2. Signature/definition/consequence/axiom probe, exit **0**:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B13Audit.lean
   ```

   Probe contains two fresh theorem declarations with canonical types and exact export-application bodies, seven copied scalar definitions with `rfl` equality checks, and a proof of the source's real-budget tail using `wbud_exported`, `wbud_stage` and `wbud_tsum_shift_le`. All succeed. The first harness attempt exited 1 because the copied real-valued definitions lacked the original noncomputable section; adding `noncomputable section` to the scratch harness fixed it. No production edit or statement change was needed. Final output is exactly the 32 axiom lines below; no warning or error:

   ```text
'KAM.Planetary.selectionΛ_one_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionΛ_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionΛ_anti' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionΛ_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.weakBudgetHyp_of_adm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_T_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_σ_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_σ_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_D_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_s_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_ε_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_d_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_E_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_tsum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_tsum_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_tsum_shift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.weakBudgetCtx_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_Q₀_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_ratios' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_Xi_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_geo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_nums' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_t_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_div_t' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_lip_term' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_sums_Aα' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wbud_exported' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exported_sums' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.param_lip_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation, exit **0**:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Budgets KAM.Planetary.WeakKAM.BudgetsStage
   replaying KAM.Planetary.WeakKAM.BudgetsStage
   replaying KAM.Planetary.WeakKAM.Budgets
   ```

4. Repository lint, exit **1**, with exact output:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
Lean lines over 100 characters:
/root/code/KAM-inp-p11b-b13/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (887 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   Both failing items predate this audit and lie outside the two B13 modules. Module-system checking, frozen guard and all 144 frozen ABI checks pass. The brief allows the generated-root exception; the separate frozen line-width issue is retained explicitly, not represented as a successful lint exit.

## Hygiene, notes, and source-defect ledger

Scoped mechanical checks pass: 302 and 542 total lines, maximum Unicode line widths 98 and 100 respectively; both files have copyright, `module`, public imports, module docstrings, exposed public noncomputable sections, and the intended namespace. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, resource override or other `set_option` occurs. No new notation, instance or root-namespace declaration occurs. A repository declaration scan found no reuse of any of the 41 new short names outside these two modules; module checks and elaboration provide additional confirmation. All 32 explicit public theorems have clean axiom lists as printed above.

Recursive import inspection found no provider and no frozen theorem, including no DRAFT_SORRY anchor. Only frozen definitions occur; no theorem manifest-state exception is needed. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has empty output. `git diff --check inp...HEAD` exits 0 with empty output.

Notes retained:

1. **Repository lint is not wholly green.** The pre-existing frozen AmdConfinement line-width failure is outside the requested B13-only audit. The stale generated root is expressly allowed by the audit brief. Neither was repaired: frozen files and generated roots are read-only in this audit. These facts account for PASS WITH NOTES rather than an unconditional repository-clean receipt.
2. **E4 ownership is explicit.** Design:103 says `exported_sums (local es_4)`, while the revision-2 implementation direction at design:284 says “Export E4 via `selection_iteration_parameter_first`”. The amended signatures and B13 handoff agree with the latter. The older table row is a documentation inconsistency to reconcile; it is not evidence of an omitted B13 signature proof. B10's actual E4 proof is outside this audit.
3. **The source's real tail is recoverable, not separately exported.** p11a3:346 includes “and Σ_(j≥ν) Λ_R,j ≤2⁻¹⁰”. The signed `exported_sums` exposes the stronger total real sum and stage nonnegativity. The independent consequence probe validates the literal tail with the existing public helpers. Consumers needing it must use that consequence; this report does not silently add a new production declaration.
4. **Prior precedence defect is resolved.** The old unparenthesized E3 signature was not used as authority: the current canonical lines 638–639 and production declaration both explicitly put A+alpha inside the tsum. No autoImplicit workaround, premise addition or theorem substitution occurs.

Suspected new pinned-source errata: **none**. No blueprint inequality is contradicted. The Ξ proof is a stronger valid arithmetic route with the original constants preserved. No auditor-introduced mathematical deviation or production change. Prior P11B design-audit N1 analytic bridge/real-collar release gates remain obligations of their respective packages; a scalar-budget PASS does not discharge them or any frozen planetary theorem.

Only this report is a repository deliverable; existing untracked `B13-handoff.md` is preserved. Scratch probes and audit logs under this worktree's `.lake/abi-scratch/` are deleted after their contents are recorded. No state-changing git command is used.
