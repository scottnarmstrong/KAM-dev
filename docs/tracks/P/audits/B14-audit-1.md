# B14 independent package audit 1

**Overall: PASS WITH NOTES.** All three signed declarations and the complete B14 composition slice pass. Notes concern the permitted stale generated root, replayed dependency warnings, and a moving `inp` reference with multiple merge bases. No B14 mathematical, signature, axiom or completeness failure was found.

## Scope and authority

- Date: 2026-10-28; worktree `/root/code/KAM-inp-p11b-b14`.
- Audited HEAD: `c8772e9761f9b01c04ae490d5a35975ebc95ca61`.
- Initial `inp`: `6671aafcf7763b616da28e69340b403fb2cc9121`; final comparison snapshot: `ec684b4ea4834e74ead53a406d997d653377ac3d`.
- Read AGENTS.md, PLAN, DECISIONS, the package brief, B14 handoff/AUDIT FOCUS, P11B design row B14 and node table, design audits 1 and 2, canonical signatures, relevant p11a4 blueprint statements/proofs and consumers, track-P statement, and relevant frozen carrier/domain definitions.
- Exact signed authority: `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean`, SHA256 `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63` (lines 667–717).
- Scope is **only** `KAM/Planetary/WeakKAM/CompositionStep.lean`, `CompositionBound.lean`, `Composition.lean`. The initial `git diff inp...HEAD` has 21 changed files / 3594 insertions, including inherited B10/B12 and B12 audit/handoff files. These dependencies were examined at B14 use sites and imported interfaces; they do not receive a new independent package-wide verdict here.
- No frozen theorem anchor or provider is implemented by B14. Per-anchor seal readiness: **not applicable**. This infrastructure audit seals no campaign theorem. The signed export `composition`: **PASS**; `SelectionComposition`: **PASS**; `sec_comp_data`: **PASS**.
- The explicit user destination overrides the generic brief's instruction to write in the main inp worktree. Only this report is a repository deliverable. The pre-existing untracked B14 handoff is preserved.

## Declaration and node ledger

All names below are in `KAM.Planetary`; filenames are relative to `KAM/Planetary/WeakKAM/`. Node abbreviations expand to `bpP:p11a:composition`, `bpP:p11a:sec-comp#data`, and `stepP:p11a:co-*`. The design maps co-* to local proof steps: no unsigned declaration masquerades as a signed graph-node export.

| Node | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| `co-dom` | `selectionCompDom` (CompositionStep.lean:28) | PASS | Exact stage domain abbreviation, on the whole carrier. |
| `co-dom helper` | `isOpen_selectionDomain` (CompositionStep.lean:32) | PASS | Openness from the strip, action ball and open parameter set; no positivity restriction needed. |
| `co-inc helper` | `convex_selectionFibre` (CompositionStep.lean:41) | PASS | Product of convex complex strip and action ball; convexity is only in the phase fibre. |
| `co-dom` | `selectionComp_r_step` (CompositionStep.lean:53) | PASS | Strip budget leaves the required sigma margin. |
| `co-dom` | `selectionComp_s_step` (CompositionStep.lean:61) | PASS | Monotone action radii from the geometric ratio. |
| `co-dom` | `selectionComp_t_step` (CompositionStep.lean:70) | PASS | Monotone collar radii from the schedule exponent. |
| `co-dom` | `selectionComp_nbhd_succ` (CompositionStep.lean:78) | PASS | Nested K and monotone t give nested complex collars. |
| `co-dom` | `selectionComp_dom_succ` (CompositionStep.lean:84) | PASS | Original and image phase points can both be placed in the previous fibre. |
| `co-dom` | `selectionComp_map_mem` (CompositionStep.lean:94) | PASS | X_nu maps the next domain to the previous one, with parameter fixed. |
| `co-dom helper` | `isOpen_selectionCompDom` (CompositionStep.lean:101) | PASS | Open actionNbhd; valid even when K is empty or not open. |
| `co-dom` | `selectionComp_holo` (CompositionStep.lean:106) | PASS | Joint holomorphy by induction on phase and shared parameter. |
| `co-deriv helper` | `selectionComp_diffAt` (CompositionStep.lean:118) | PASS | Open-domain joint holomorphy restricted to a fixed-parameter fibre. |
| `co-deriv helper` | `selectionComp_X_diffAt` (CompositionStep.lean:128) | PASS | Same restriction for X_nu on the next-stage domain. |
| `co-deriv` | `selectionComp_fderiv_succ` (CompositionStep.lean:139) | PASS | Actual fderiv_comp with differentiability established at the actual image point. |
| `co-deriv` | `selectionComp_derivative` (CompositionBound.lean:29) | PASS | D-1=(L-1)M+(M-1); op-norm submultiplicativity and 1+m <= exp m give exact exponential partial-sum bound. |
| `co-deriv` | `selectionComp_budget_sum_le` (CompositionBound.lean:76) | PASS | Nonnegative finite partial sum <= exported total <= 2^-12. |
| `co-deriv` | `selectionComp_small` (CompositionBound.lean:87) | PASS | exp(sum m)-1 <= 2^-11 using the rational exponential majorant; explicit positive denominator. |
| `co-disp` | `selectionComp_angle` (CompositionBound.lean:108) | PASS | Componentwise angle telescoping, exact finite sum of A. |
| `co-disp` | `selectionComp_action` (CompositionBound.lean:127) | PASS | Componentwise action telescoping, exact finite sum of Alpha. |
| `co-inc` | `selectionComp_increment` (CompositionBound.lean:146) | PASS | Mean value bound on the convex phase fibre; derivative norm <= 1+2^-11 and product max norm give literal increment constant. |
| `composition` | `SelectionComposition` (Composition.lean:29) | PASS | Signed record is text-identical; all ten added fields and inherited normal_form preserved on the same chain. |
| `sec-comp#data` | `sec_comp_data` (Composition.lean:74) | PASS | Signed definition is text-identical; shared-parameter finite composition. |
| `co-dom` | `selectionComp_domain` (Composition.lean:79) | PASS | Induction to D0, with K0=d.K and initial radii identified. |
| `co-dom` | `selectionComp_periodic` (Composition.lean:98) | PASS | Integer-angle equivariance by composition; shared parameter unchanged. |
| `co-dom` | `selectionComp_symplectic` (Composition.lean:115) | PASS | Fibre chain rule composes the canonical complex symplectic form identity. |
| `co-dom` | `selectionComp_real` (Composition.lean:131) | PASS | Inductively composes the actual real-output witnesses. |
| `composition helper` | `selectionComposition_of_output` (Composition.lean:150) | PASS | Distinct conditional assembly helper; context and iteration outputs are supplied internally by the source export. |
| `composition` | `composition` (Composition.lean:166) | PASS | Exact signed premises and adapted schedule; constructs budget context and uses parameter_selection_adapted, with no additional source premise. |

## Definition classification, hypotheses and consumer completeness

The only three new explicit non-theorem declarations are:

- `selectionCompDom`: transparent abbreviation of `selectionDomain (selectionr a ν) (selections a ν) (actionNbhd (K ν) (selectiont a ν))`. It is the intended stage domain for arbitrary schedules, sets and stages; no fallback.
- `SelectionComposition`: the exact signed output structure extending `SelectionOutput`. Its ten additional fields are outputs of `composition`, not assumptions placed on the source theorem. Its constructor is supplied all ten proofs by `selectionComposition_of_output`.
- `sec_comp_data`: the exact signed alias of `selectionCompose c b`. The underlying recursion in `Schedule.lean:204–207` starts at identity and appends `c.X j b` on the right, giving X0 o ... o X_(nu-1) with one common b. No changed ambient type, norm, junk value or off-domain derivative fallback is used.

All added definitions are in an exposed public noncomputable section. Ambient phase and parameter spaces are Pi/Prod spaces with max norms. The complex canonical form is `KAM.Canonical.symplFormC` (Setting.lean:65), the stated action-angle sign convention. Fibre derivatives are ordinary Frechet derivatives at points where differentiability has been proved; no use depends on fderiv's default value at a non-differentiable point.

The conditional helpers accept `WeakBudgetCtx` and `SelectionIteration`/`SelectionOutput` under distinct helper names. These express schedule data and already constructed upstream outputs. The source-facing `composition` has exactly the signed standing premises. It obtains adapted admissibility and radius positivity from `free_radius`, derives epsilon0=2*epsilon positivity and its budget context via `weakBudgetCtx_of`, and obtains the output from `parameter_selection_adapted`. It does not assume any composition conclusion. In `Budgets.lean:60–76`, the context consists of admissibility, scalar schedule hypotheses and identifications with the source data, not map/composition estimates.

The historical B12 audit-1 F1 (missing adapted selection) is not present at this B14 use site: current `Selection.lean:335–350` exports exactly the adapted `SelectionOutput`, built from `inductive_lemma_adapted` and `selectionOutput_of_iteration`. B14 uses that export at Composition.lean:175. This is verified by the successful B14 build and the clean transitive axioms of `composition`; it is not a separate re-audit of all B12 proofs.

The literal co-dom Hamiltonian clause is preserved through the parent: `SelectionOutput` extends `SelectionIteration`, whose `normal_form` at IterationRecord.lean:46–51 states the initial Hamiltonian evaluated at this same `selectionCompose` equals energy + frequency dot action + remainder. This field is retained by `{ o with ... }` at Composition.lean:152. A fresh Lean projection probe elaborated that identity on an arbitrary composition output and actual stage-domain point. There is no weakened replacement Hamiltonian.

The four co-* steps are complete: domain/holomorphy, exponential derivative recursion and absolute smallness, separate angle/action displacements, and increments with the exact `(1+2^-11)*max(A,Alpha)` constant. Canonical, periodic and real clauses are proved too. B15's signed `SelectionLimit` (signature:725 onwards) extends this very record, retaining the same chain, sets and frequency. Its zero-section increments, derivative bounds, equivariance and displacement inputs are all present. No extra consumer hypothesis or common positive action radius is introduced. The derivative estimate is in phase only, as the blueprint requires; joint holomorphy covers parameters. The mean value theorem is applied on the convex phase fibre with b fixed, so no convexity of a Cantor parameter set is assumed. Use of Mathlib's convex derivative estimate directly supplies the designated increments_open/ext-mvt role.

## Independent validation receipts

Commands were run from this worktree with at most one auditor-owned Lean/Lake invocation active at a time and `LEAN_NUM_THREADS=1`; every such invocation had `nice -n 5`. Lint's ABI subprocess inherited these settings. No clean, update, cache retrieval, source repair, generated-root regeneration, or state-changing git operation was used.

### Targeted build — exit 0

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b14 KAM.Planetary.WeakKAM.Composition
[inp-gate] slot 2 acquired 23:20:28 for KAM.Planetary.WeakKAM.Composition
Build completed successfully (9204 jobs).
```

This was the prescribed targeted incremental gate, not a library rebuild. Existing dependency diagnostics were replayed (unused binders/simp arguments and deprecated names in Schedule, CutoffTensor, CutoffScale, Cutoff, MaximalStep and Averaging dependencies, and IterationParam). No diagnostic named any of the three audited Composition files. No default-heartbeat design failure occurred.

### Exact signatures, inherited clause and axioms — exit 0

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B14Probe.lean
```

Mechanical canonical-source comparison returned:

```text
SelectionComposition exact text: True
composition exact statement: True
sec_comp_data exact text: True
Public explicit theorem axiom probes: 25
```

The probe copied the signed `composition` declaration header under a fresh name and supplied `by exact composition d ε he hsmall f hf`, then checked `example : type_of% @composition := @auditB14Composition`. It checked `sec_comp_data` by `rfl` and the inherited normal-form equality by `o.normal_form ν x hx`. There is no frozen-anchor seal body to test in B14. Complete axiom output:

```text
'KAM.Planetary.selectionComp_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComposition_of_output' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.composition' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_budget_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_increment' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_selectionDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.convex_selectionFibre' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_r_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_s_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_t_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_nbhd_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_dom_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_map_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_selectionCompDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_holo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_diffAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_X_diffAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.selectionComp_fderiv_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — exit 0

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.Composition KAM.Planetary.WeakKAM.CompositionBound KAM.Planetary.WeakKAM.CompositionStep
replaying KAM.Planetary.WeakKAM.CompositionStep
replaying KAM.Planetary.WeakKAM.CompositionBound
replaying KAM.Planetary.WeakKAM.Composition
```

### Source lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1076 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Exit **1**, solely from the brief-permitted generated-root staleness. Module validation, frozen-anchor guard and elaborated ABI checks all pass, as shown. No generated file was regenerated. No other lint failure is waived.

## Integrity, moving comparison branch and notes

The initial `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` was empty. Git warned of multiple merge bases and selected `9fc6965a034a91dede3a0eaedd019e922f0a7b80`. The explicit comparison `git diff 9fc6965a034a91dede3a0eaedd019e922f0a7b80..HEAD -- KAM/Frozen manifest KAM.lean README.md` is also empty.

During this audit another process advanced `inp`. A final live three-dot protected-path check selected the other merge base `141f86ac0975de0a2fe929d598b21a36fc8d47ad`, and is **not empty**: it shows the inherited P-G seal, its manifest state change and generated-root imports. Attribution from `git log 141f86ac..HEAD -- <protected paths>` identifies `9fc6965a` (P-G seal), `323b1a27` and `08692865` (root regeneration), not a B14 edit. Both merge bases are reported by `git merge-base --all inp HEAD`. These inherited differences are recorded explicitly; this report does not claim that the final live protected-path command literally passed. The stable initial-baseline protected comparison passes, and all audited B14 commits touch only Composition modules. No prohibited source repair is requested or performed.

The three-file B14 patch remained byte-identical across the moving-branch recheck: SHA256 `e65b37194d0c7625be47863f5f822e6a1b2665b5f7a9be0f477d066704889da1`. HEAD and the canonical signature stayed unchanged. This moving-base comparison artifact is a scope note, not frozen-anchor closure or a B14 mathematical failure.

Mechanical hygiene: no forbidden tokens (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`) or option overrides in the three files. Copyright, `module`, public imports, docstring and public section are present. The 28 explicit public declaration short names have no duplicate declaration in the KAM source tree; all live under `KAM.Planetary`, so no harmful root shadow was introduced. File sizes / maximum Unicode line widths: CompositionStep 152 / 98, CompositionBound 185 / 97, Composition 180 / 98. All are below 1500 lines and 100 columns. `git diff --check inp...HEAD` exited 0 on the initial comparison.

A recursive local import scan found 158 reachable KAM modules, **no provider import and no frozen theorem import**, including no DRAFT_SORRY anchor. All 14 reachable frozen definition modules are manifest SEALED (ActionNbhd, ComplexStrip, IsDiophantine, RealHamiltonian, FrequencyMap, HamiltonianVectorField, HamiltonianVectorFieldC, SymplecticForm, Planetary.Phase, OmegaZero, IsPrimaryOnStrip, IsRealOnReals, Planetary.CircularTube, Planetary.CircularPoint). The axiom probe independently confirms there is no sorryAx contamination.

## Source defects, deviations and limits

No suspected new blueprint or pinned-source erratum was found. The relevant source is blueprint-P/parts/p11a4-limit-family.tex:64–84: shared-parameter recursion, composition clauses and all four proof steps. In particular line 69's “H_nu=H_0 o Phi^nu” is supplied by the inherited normal_form, and line 83's convexity is used only on the fixed-parameter fibre. No premise, conclusion, law, norm or coefficient is silently changed. Prior design-audit upstream release conditions are not closed wholesale by this scoped audit; no frozen headline or later limit/tori theorem is claimed.

Only this audit report is retained as new audit output. Temporary probe, log, import-list and diff files under `.lake/abi-scratch/` are removed after incorporating their receipts. No Lean implementation, frozen file, manifest, generated root or handoff is edited.
