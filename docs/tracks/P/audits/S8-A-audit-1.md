# Independent S8-A audit 1

Overall verdict: **PASS WITH NOTES for the assigned S8-A design contract**. The literal
`KAM.Planetary.SecularForm.perturbation_analytic` signature is proved without added premises,
and the four scoped modules contain no proof escape. This is infrastructure, not a frozen-anchor
provider: **no frozen anchor is sealed or certified seal-ready by this package**. Full blueprint-node
closure is not claimed; the export/coverage qualifications below must accompany any graph update.

## Scope and authority

Audited worktree: `/root/code/KAM-inp-s8a`; HEAD `d8edd6b25140092bf56ed18bdc5332d5675b3763`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, S8-A handoff and AUDIT FOCUS,
P810 design Revision 2 including Appendix A and its proof/package plan, both design audits,
Track P statement, Part 8 proposition/proof cuts, relevant frozen definitions and the consumed
chart/parameter-integral interfaces. The user's exact report destination overrides the generic
brief's MAIN-worktree destination. No production or tracked source file was changed.

Only these modules are audited: `Analytic.lean` (121 lines), `AnalyticGeometry.lean` (259),
`AnalyticReal.lean` (120), `AnalyticRegularity.lean` (148), all under
`KAM/Planetary/SecularForm/`. Their 648 total lines contain 39 public theorems and 8 definitions.

Both `git diff inp...HEAD` and `git diff inp-s8p...HEAD` were inspected. Current refs are
`inp=05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2` and
`inp-s8p=050115ac18394a42e707e293b3e1be70311e256a`. Git warns that the former has multiple merge
bases and uses the latter hash. The scoped four-file diffs are identical. Both broad diffs contain
unrelated merged N12-06/P4-R0/P5-CG work and four generated root imports. The S8-A-only comparison
`git diff 0e90a6c...HEAD` (after the S8-P merge) contains exactly the four audited files;
its protected-path diff is empty. This limits the audit without silently asserting the broad
branch is a four-file patch.

## Contract and proof assessment

The original signature is absent from this worktree's `.drafts/`, but exists at
`/root/code/KAM-inp/.drafts/design/P810Signatures.lean`. Its SHA-256 is
`492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design audit 2;
its entire text occurs verbatim in the local design Appendix A. The main theorem's declaration
through the type (before `:=`) is byte-identical to that signature. The four designed definitions
`planetC`, `separationC`, `perturbationC`, `secularC` are also byte-identical. An independent
probe copied the signature under a fresh theorem name and closed it with
`exact perturbation_analytic D ha`; Lean accepted it. Frozen/provider equality and seal-body
probes are inapplicable because there is no provider or frozen theorem in scope.

| Node | Implementation | Verdict | Assessment |
|---|---|---|---|
| `bpP:p8:perturbation-analytic` / S8-A signature | `perturbation_analytic` | PASS WITH NOTES | Exact independently audited design contract; broader blueprint exports below remain separate. |
| `stepP:p8:pa-circ` | `planetC_center`, `re_separationC_center` | PASS | Literal circular chart, actual squared axis-gap lower bound. |
| `stepP:p8:pa-unif` | `separation_pair`, `exists_radius` | PASS | Compact cell times closed ball; finite intersection, periodic reduction; one radius before all angles, pairs, models. |
| `stepP:p8:pa-hol` | regularity and real-inclusion lemmas | PASS WITH NOTES | Holomorphy, joint continuity and exact two-model restriction proved; full perturbation periodicity is not a separate export. |
| `stepP:p8:pa-avg` | `secularC_inclusion`, `perturbation_analytic` | PASS WITH NOTES | Holomorphic and real-analytic average proved; all-order integral derivative identities are not exported here. |

The neighbourhood bounds are paid: `r<rho` controls the action difference by Lambda*/2 and
both eccentric coordinates by sqrt(Lambda*)/16; real angles have zero imaginary part. Circular
positions come from `poincare_circular` and the real agreement conjunct of
`poincare_holomorphic`, rather than from a substitute chart. Compact uniform continuity is
applied on the closed ball of radius rho/2 inside the open polydisc of radius 3*rho/4.
The pairwise radius is uniform on the cell and lifted to all real angles by periodicity;
`Filter.eventually_all` intersects the finite family. D.hn handles the nonempty infimum.

For i<j, strict axis ordering makes gap^2/2 positive. The derived hsep therefore excludes
the principal-power branch cut. The kinetic correction is a complex bilinear polynomial,
without conjugation; its real restriction is exactly the total-momentum squared term divided
by 2*m0. All appearances of hsep in local helper premises have distinct helper names and are
supplied by `exists_radius` in the main theorem. No analytic conclusion is bundled in Data.

The average consumes S8-P's `e_param_cslow` on the actual triple carrier. Openness is proved,
joint continuity is restricted to the compact angle cell, and holomorphy is supplied for every
angle. `KAM.analyticOnNhd_of_differentiableOn` supplies finite-dimensional complex analyticity;
restriction of scalars, the continuous real inclusion and real-part map give the actual real
secular function. `secularC_inclusion` unfolds the frozen `secularAverage`, preserving
`(p,q)=(eta,xi)`, the closed angle cell and `(2*pi)^(-n)`. Explicit integrability on that cell
prevents any use of the Bochner nonintegrable-zero convention on the promised real domain.

## Every new public declaration

Names below have prefix `KAM.Planetary.SecularForm`. Local helpers implement proof cuts rather
than substitute source results. Positivity/domain hypotheses on local helpers are supplied in
the parent proof; none changes the parent theorem's quantifiers or data dependence.

| Node / locator | Lean declaration | Verdict | Reason |
|---|---|---|---|
| S8-A / Analytic:34 | `inclusionLM` | PASS | Real-linear componentwise complex inclusion, with linearity proved. |
| S8-A / Analytic:44 | `inclusionCLM` | PASS | Continuous realization of inclusionLM by finite-dimensional continuity. |
| S8-A / Analytic:46 | `inclusionCLM_apply` | PASS | Definitional agreement with existing inclusion. |
| S8-A / Analytic:48 | `isOpen_realDisc` | PASS | Preimage of the exact open complex ball under continuous inclusion. |
| S8-A / Analytic:53 | `secularC_inclusion` | PASS | Complexification commutes with actual frozen normalized average. |
| S8-A / Analytic:65 | `perturbation_analytic` | PASS | Byte-identical checked design signature; all premises discharged from D and ordered positive axes. |
| S8-A / AnalyticGeometry:33 | `center` | PASS | Literal circular slow point; all-carrier definition. |
| S8-A / AnalyticGeometry:35 | `polydisc_eq_ball` | PASS | Exact equality for positive radius in the existing product/Pi norm. |
| S8-A / AnalyticGeometry:42 | `action_pos` | PASS | Standing positive physical data and positive axes imply positive actions. |
| S8-A / AnalyticGeometry:46 | `rho_pos` | PASS | Finite nonempty infimum; D.hn supplies nonemptiness. |
| S8-A / AnalyticGeometry:54 | `rho_le_half` | PASS | Literal infimum upper bound, valid for arbitrary axes. |
| S8-A / AnalyticGeometry:57 | `rho_le_sqrt` | PASS | Literal infimum upper bound, valid for arbitrary axes. |
| S8-A / AnalyticGeometry:60 | `planetC` | PASS | Byte-identical designed single-planet complex chart. |
| S8-A / AnalyticGeometry:62 | `separationC` | PASS | Byte-identical bilinear squared position difference; no conjugation. |
| S8-A / AnalyticGeometry:66 | `blockC` | PASS | Literal ((lambda,xi),(Lambda,eta)) block; no default branch. |
| S8-A / AnalyticGeometry:69 | `planetC_eq` | PASS | Definitional chart/block identity. |
| S8-A / AnalyticGeometry:72 | `blockC_mem_nbhd` | PASS | rho bounds prove every chart-domain inequality; no domain membership assumed. |
| S8-A / AnalyticGeometry:84 | `continuous_blockC` | PASS | Global continuity of the literal block map. |
| S8-A / AnalyticGeometry:89 | `continuousOn_planetC` | PASS | Composition with Poincare/Holomorphic on the proved neighbourhood. |
| S8-A / AnalyticGeometry:99 | `action_sq_div` | PASS | Actual axes/actions inverse identity under source positivity. |
| S8-A / AnalyticGeometry:107 | `planetC_center` | PASS | Actual circular position from real chart agreement and poincare_circular. |
| S8-A / AnalyticGeometry:127 | `re_separationC_center` | PASS | Circular squared distance at least the squared axis gap; stronger: no i<j guard. |
| S8-A / AnalyticGeometry:150 | `planetC_periodic` | PASS | Actual complex chart has period 2*pi for each real angle. |
| S8-A / AnalyticGeometry:167 | `exists_cell_planetC` | PASS | Independent periodic reduction of every angle to the compact cell. |
| S8-A / AnalyticGeometry:177 | `continuousOn_re_separationC` | PASS | Finite polynomial composition of jointly continuous chart components. |
| S8-A / AnalyticGeometry:190 | `separation_pair` | PASS | Compact uniform continuity produces a positive radius for each ordered pair. |
| S8-A / AnalyticGeometry:233 | `exists_radius` | PASS | Finite intersection constructs a common positive radius before all angles and pairs. |
| S8-A / AnalyticReal:29 | `planetBlock_assemble` | PASS | Exact frozen coordinate-order identity. |
| S8-A / AnalyticReal:34 | `planetC_inclusion` | PASS | Fifth conjunct of poincare_holomorphic gives actual real chart agreement. |
| S8-A / AnalyticReal:50 | `planetC_inclusion_fst` | PASS | Position matches bodyVector of the actual product chart. |
| S8-A / AnalyticReal:60 | `planetC_inclusion_snd` | PASS | Momentum matches bodyVector of the actual product chart. |
| S8-A / AnalyticReal:70 | `separationC_inclusion` | PASS | Complex square restricts to frozen real planeSq. |
| S8-A / AnalyticReal:79 | `cpow_planeSq` | PASS | Valid also at zero with Lean totalized inverses/powers; no collision fallback used for holomorphy. |
| S8-A / AnalyticReal:91 | `perturbationC_inclusion` | PASS | Literal fixed and moving fFix/fMov formulas, including self and cross kinetic terms. |
| S8-A / AnalyticRegularity:27 | `perturbationC` | PASS | Byte-identical pair potential plus Boolean-selected polynomial kinetic correction. |
| S8-A / AnalyticRegularity:31 | `secularC` | PASS | Byte-identical normalized complex Bochner angular average. |
| S8-A / AnalyticRegularity:37 | `differentiable_blockC` | PASS | Global complex differentiability of the slow block map. |
| S8-A / AnalyticRegularity:43 | `differentiableOn_planetC` | PASS | Chart holomorphy composed on the proved domain; positive-radius premise is local typing data. |
| S8-A / AnalyticRegularity:52 | `differentiableOn_planetC_fst` | PASS | Coordinate projection preserves complex differentiability. |
| S8-A / AnalyticRegularity:59 | `differentiableOn_planetC_snd` | PASS | Momentum coordinate projection preserves complex differentiability. |
| S8-A / AnalyticRegularity:66 | `continuousOn_planetC_fst` | PASS | Position-coordinate joint continuity. |
| S8-A / AnalyticRegularity:73 | `continuousOn_planetC_snd` | PASS | Momentum-coordinate joint continuity. |
| S8-A / AnalyticRegularity:80 | `differentiableOn_separationC` | PASS | Finite bilinear polynomial, with actual chart holomorphy. |
| S8-A / AnalyticRegularity:88 | `continuousOn_separationC` | PASS | Joint continuity of the bilinear squared separation. |
| S8-A / AnalyticRegularity:99 | `separationC_slit` | PASS | Positive ordered gap and local hsep put the actual separation in the slit plane. |
| S8-A / AnalyticRegularity:109 | `differentiableOn_perturbationC` | PASS | Principal cpow on the slit plane; polynomial kinetic term for true model. |
| S8-A / AnalyticRegularity:128 | `continuousOn_perturbationC` | PASS | Same compositions jointly continuous, for both Boolean models. |

## Definition classification

All eight definitions are classified in the declaration table. `center`, `blockC`, `inclusionLM`
and `inclusionCLM` are literal coordinate/linear-map adapters with no case split or choice of
analytic data. `planetC` uses the existing total complex chart on its full carrier;
`separationC` is its literal bilinear polynomial. `perturbationC` is the designed total
principal-cpow formula; the only conditional selects the two actual physical models.
`secularC` is the designed normalized total Bochner integral. Principal cpow and Bochner
integration have their usual total values outside the physical domain, but the proof never
uses a junk value to obtain regularity or physical agreement: slit-plane membership and
integrability are proved where required. `cpow_planeSq` also holds at zero by totalized
inverse/rpow conventions; no positive-distance conclusion is obtained from that zero case.
No new structure, abbrev, ambient instance, or replacement norm/carrier is introduced.
The existing Symplectic module is consumed only for its circular chart value; no symplecticity
assumption is used in place of holomorphy.

## Coverage notes, suspected defects and deviations

1. **Blueprint export boundary (not a counterexample to the checked design).**
   `blueprint-P/parts/p8-secular-form.tex:42` says “Psi(lambda,w') in W” and
   “N_R(rho_*) times R^n subset Psi^{-1}(W)”; line 43 says “2*pi-periodic in lambda”;
   line 44 asserts the all-order derivative-of-average identity, and `pa-avg` at line 51
   says “the derivative formula is [e-diff]”. The exact design signature at
   `P810-LEAN-DESIGN.md:633` does not explicitly export collision-free membership,
   full perturbation periodicity, or the derivative identities. The production theorem
   faithfully matches that signature. Chart periodicity and domain/separation ingredients
   are available here, and the generic finite-order differentiation theorem is owned by S8-P,
   but their full specializations are not supplied as public S8-A exports. Thus this audit
   permits the S8-A signature result and its proved cuts, not an assertion that every clause
   of the broader proposition is already a directly applicable Lean theorem. No false
   pinned-paper claim or new source erratum was found.
2. **Broad protected-path hygiene is not literally empty.** The requested
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` contains four added
   `KAM.lean` imports: CorrectorRegular, ComplexGlue, ResonanceSlow and SecularForm.Basic.
   The same occurs against inp-s8p. Frozen paths, manifest and README have no changes;
   the S8-A-only range after 0e90a6c has no protected changes at all. These are inherited
   integration changes, not edits by this audit or the S8-A-only commit series. Record
   the broad exception; do not report an empty whole-branch protected diff.
3. The proof uses Mathlib compact uniform continuity directly rather than the trivial
   `compact_uniform` wrapper published as a pa-unif edge. This pays the same mathematical
   obligation but is a dependency-route observation if graph locators are updated.

No production deviation was introduced by this auditor. No new pinned-source erratum is
asserted. The parent signature is verified; the missing broader exports remain explicit
limitations. Default-heartbeat checks produced no design signal.

## Independent checks

All auditor-controlled Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1`
and `nice -n 5`. No build cleanup, update, cache retrieval, package mutation, resource override,
or generated-root regeneration was run. External campaign processes are not controlled by
this audit.

### Targeted build — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8a KAM.Planetary.SecularForm.Analytic
```

```text
[inp-gate] slot 2 acquired 10:39:47 for KAM.Planetary.SecularForm.Analytic
Build completed successfully (9120 jobs).
```

No warning names an S8-A file. The build replays pre-existing unused-variable warnings in
Kepler/Energy (hm,hκ), Poincare/Chart (hm,hκ), Kepler/Mass (hκ,hw,hm) and
Poincare/Holomorphic (hm,hκ); these are upstream of the assigned four-file scope.

### Exact-signature and all-public-theorem axiom probe — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8AAudit.lean
```

The scratch file imports `KAM.Planetary.SecularForm.Analytic`, copies the checked main
signature as `audit_signature`, and proves it with `exact perturbation_analytic D ha`.
It then runs `#print axioms` on each of the 39 public theorems. Complete axiom output:

```text
'KAM.Planetary.SecularForm.inclusionCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.isOpen_realDisc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.secularC_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.polydisc_eq_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.action_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.rho_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.rho_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planetC_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.blockC_mem_nbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_blockC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuousOn_planetC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.action_sq_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planetC_center' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.re_separationC_center' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planetC_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.exists_cell_planetC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuousOn_re_separationC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.separation_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.exists_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planetBlock_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planetC_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planetC_inclusion_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planetC_inclusion_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.separationC_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.cpow_planeSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbationC_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.differentiable_blockC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.differentiableOn_planetC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.differentiableOn_planetC_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.differentiableOn_planetC_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuousOn_planetC_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuousOn_planetC_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.differentiableOn_separationC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuousOn_separationC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.separationC_slit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.differentiableOn_perturbationC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuousOn_perturbationC' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` or extra axiom occurs. This also checks that the main signature can be consumed
without any implicit analytic instance or added hsep/radius premise.

### Kernel replay — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Analytic KAM.Planetary.SecularForm.AnalyticGeometry KAM.Planetary.SecularForm.AnalyticRegularity KAM.Planetary.SecularForm.AnalyticReal
```

```text
replaying KAM.Planetary.SecularForm.AnalyticReal
replaying KAM.Planetary.SecularForm.AnalyticRegularity
replaying KAM.Planetary.SecularForm.AnalyticGeometry
replaying KAM.Planetary.SecularForm.Analytic
```

### Import, source and diff hygiene

A recursive scan of literal KAM imports reaches 74 KAM modules, including 47 frozen definition
modules. Each of those 47 has a `SEALED` manifest entry. No frozen theorem module, provider,
or DRAFT_SORRY anchor occurs in that closure. The new modules have copyright, `module`, public
imports, module docstrings and exposed public noncomputable sections.

```sh
rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace' KAM/Planetary/SecularForm/Analytic*.lean
```

No matches (rg exit 1). All four files are below 1500 lines. No proof/resource override occurs.
`git diff --check inp...HEAD` exits 0, printing only the multiple-merge-base warning described
above. The scoped diffs against inp and inp-s8p compare byte-identically with `cmp` (exit 0).
Protected paths are qualified explicitly above; the broad root diff is not hidden.

### Source lint — exit 1, solely the permitted generated-root exception

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (528 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This satisfies the brief's explicit exception for the stale generated `KAM.lean` line.
No root regeneration was attempted. No scoped or unrelated additional lint defect appeared.

### Handoff and cleanup

The only audit deliverable is this report at the user's exact absolute path. The temporary
`.lake/abi-scratch/S8AAudit.lean` signature/axiom probe was deleted after all Lean checks;
the lint ABI helper removes its own temporary probe. No state-changing git operation was run.
The pre-existing untracked `S8-A-handoff.md` was left intact. Validation logs are available
for this session as `/tmp/maud-s8a-{build,probe,kernel,lint}.log`; all material receipts are
included above so the report does not depend on their retention.

Final disposition: **PASS WITH NOTES for S8-A's checked design signature and paid proof cuts**;
no provider, frozen-anchor seal, complete Part 8 proposition, or later consumer closure is asserted.
