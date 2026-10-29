# GAP-I1a independent package audit 1

**Overall verdict: FAIL for complete literal graph-node closure; PASS for the Dirichlet/N1 repair and proof hygiene, subject to the permitted generated-root lint exception.** No frozen anchor is proved or sealed by this package. The two rejected rows are `bpI:p1:reduced` and `bpI:p1:perturbation-noA5`: their new unsigned exports retain a Diophantine restriction on the frequency where the literal source allows any real frequency. This is the separate B2/D3 issue, not a defect in the Dirichlet proof.

Audited 2026-10-29 in `/root/code/KAM-inp-gi1a`. HEAD: `db305f13e101faf5499dada636f9038bc561cbb4`; comparison ref `inp`: `ab3459def1182c7cf70d8b920eded286c93b2737`. Reviewed the complete `git diff inp...HEAD`: three new modules, 547 insertions, no edited existing production file. The pre-existing untracked `GAP-I1a-handoff.md` was left intact. The user's exact report destination overrides the generic brief's main-worktree destination.

## Controlling scope and finding F1

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, supplied handoff including AUDIT FOCUS and N1 ruling, GAP-PLAN-I sections 2 and GAP-I1a, track-I statement, the Part123 design and its signature appendix/amendment D21, and each of the nine graph records' SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION and cited blueprint statements. Scope of production-code audit: only `DioDirichlet.lean`, `SettingSrc.lean`, `FullRange.lean`; landed definitions and lemmas were read as interface evidence, not re-audited as packages.

**F1 — unresolved arbitrary-frequency restriction (major, two nodes).**

* `KAM/Iso/Linear/FullRange.lean:156`: `reduced_src (hS : SettingSrc n τ M D H ω γ)` uses this same `ω` in all residual, torsion and directional-derivative expressions. `SettingSrc.lean:50` requires `dio : IsDiophantine γ τ ω`, with `gamma_pos` at line 49.
* `FullRange.lean:209`: `perturbation_noA5_src` has the same restriction, in addition to the source norm bound `hω`.
* Blueprint `blueprint-I/parts/p1-iso-linear.tex:484` says “ω ∈ ℝⁿ (any)”; its line 567 says “|ω| ≤ Θ, ω ∈ ℝⁿ”. The graph records at `docs/graph/I/DEPGRAPH.md:2396–2398` and `2719–2721` retain that arbitrary-frequency scope. In particular perturbation's hypotheses explicitly list only the Hamiltonian setting data and the local torus data, not a Diophantine condition for the tested frequency.

Refutation of interface applicability: take the frequency being tested to be zero. It obeys the source's real-frequency and norm-bound conditions. The local analytic/frame hypotheses can hold, for example for the flat primary torus, zero Hamiltonian, and identical perturbed torus (`d = 0`), with positive domain/strip margins and appropriate positive bounds. Yet no `SettingSrc ... 0 γ` exists for `γ > 0`: evaluating `dio` at a coordinate unit integer vector gives `γ ≤ 0`. This is not a counterexample to either proved theorem or to the mathematical source conclusions; it shows the exports cannot be applied throughout the source carrier. Enlarging the σ bounds and proving `τ ≥ n−1` cannot remove this obstruction.

The graph's reduced record itself combines the old setting's Diophantine phrase with “omega ... (any)”; this ambiguity is already disclosed in design departure D3 (`PART123-LEAN-DESIGN.md:246`) and B2 (`:320–321`). The current GAP-PLAN-I section 2.8 explicitly separates B2/D3 from N1 and calls for either a ruling or GAP-I1c; its optional GAP-I1c exports are at lines 386 onward. The supplied handoff provides an explicit ruling for **N1 only**, and AUDIT FOCUS explicitly requires unsigned exports to state the literal node. Earlier acceptance of signed restricted interfaces and sufficiency for existing Diophantine consumers does not establish this new literal claim.

Resolution needed for these two graph rows: prove the arbitrary-frequency exports (a separate auxiliary setting at `ω₀`, if used, must not restrict the target `ω`), or obtain and record an explicit source-interpretation ruling and synchronize the source/graph contract. This report does not silently apply the latter. The package remains useful as a correct N1 repair, but is not complete for the literal nine-node claim.

## Per-node and declaration review

Names in this table are in `KAM.Iso.Linear` unless qualified. Graph locators refer to `docs/graph/I/DEPGRAPH.md`; blueprint locators refer to `blueprint-I/parts/p1-iso-linear.tex`.

| Node / declaration | Lean location | Verdict | Source comparison and reason |
|---|---|---|---|
| N1 auxiliary: `KAM.DioDirichlet.bucket_bounds` | DioDirichlet:30 | PASS | Bucket endpoint `t=m` is handled by clipping to `m−1`; both inequalities hold on the entire stated interval, including `m=1`. |
| N1 auxiliary: `KAM.DioDirichlet.exists_small_combination` | DioDirichlet:44 | PASS | Correct n-dimensional pigeonhole bound; nonzero integer vector, every coordinate bounded by N, and the stated linear-form estimate. Handles zero frequency separately. |
| N1: `KAM.IsDiophantine.n_sub_one_le_tau` | DioDirichlet:139 | PASS | Exactly the required `2 ≤ n`, positive γ, literal frozen Diophantine predicate, same τ. No nonnegative-τ premise added. |
| `bpI:p1:setting`: `SettingSrc` | SettingSrc:34; graph:968; blueprint:30–46 | PASS | Literal Hamiltonian/frequency premises, τ≥0, no σ fields. K/r/primaryness/reality/image/Gram premises stay explicit in consumers as authorized by GAP-I1a. Γ uses existing `cR`, `kappa`; no replacement constants. |
| `SettingSrc.tau_ge` | SettingSrc:56 | PASS | Derived Dirichlet output, not a structure field or assumed dependency result. |
| `SettingSrc.setting` | SettingSrc:60 | PASS | Same τ and frequency, all original fields copied, arbitrary positive σ parameters. No new analytic premise. |
| `bpI:p1:setting#k-bridge`: `SettingSrc.k_bridge` | SettingSrc:81; graph:1001; blueprint:39–46 | PASS WITH NOTES | Same Hamiltonian/domain in Standing, σ=1, DH bound, τ≥0 and n≥1, plus exactly the frozen-agreement interface. Other K objects are the existing definitions, not new substitutes. Torsion-average equality is conditional on continuity, as in `frozen_agreement`; for the source setting's holomorphic primary torus in D with invertible Gram this is supplied by its regularity. It does not assert arbitrary H/K have continuous torsion. |
| `mSize_max_one` | FullRange:43 | PASS | Exact max identity on all real M and σ values; no sign hypotheses. |
| `bpI:p1:extended-basic`: `extended_basic_src` | FullRange:53; graph:1140; blueprint:111–127 | PASS | Complete regularity, periodicity, reality, continuity, block average, row-sum bound and bordered-matrix estimate; σK′, σB′ and CT remain free bounds. |
| `bpI:p1:last-row`: `last_row_src` | FullRange:74; graph:1676; blueprint:228–247 | PASS | Literal Y=ω−ηL identity, row-sum bound, invariant specialization, general average and 2n² bound. Component/signed forms are the same identities using the existing definition of ηL. Fewer torus regularity premises than the source, hence stronger. |
| `bpI:p1:energy-approx` (a)–(e): `energy_approx_src` | FullRange:96; graph:1806; blueprint:275–287 | PASS | Chain rule, ω derivative, ηN identity, all zero averages, correct MΓδ and nMΓδ/δ′ estimates on the stated strips. ηN is literally LᵀΩ₀E in Objects.lean:97; no Gram-inverse premise added to (a)–(e). |
| `bpI:p1:energy-approx` (f): `energy_defect_src` | FullRange:120; same graph record; blueprint:288–294 | PASS | Frame correction identities, average split, pointwise derivative bound and cube-local product bound. Given the source average equation, substitute it into the unconditional split. A/X quantify over bounds on `[0,1]ⁿ`, not all real angles; by continuity on the compact cube they recover the source finite-supremum estimates. This is the D6/D21 pointwise-bound formulation. |
| `bpI:p1:energy-conservation`: `energy_conservation_src` | FullRange:145; graph:2029; blueprint:337–348 | PASS | Whole-strip constancy, arbitrary complex E₀ and pointwise norm equality. The latter gives the supremum equality on the nonempty strip; no Gram assumption. |
| `bpI:p1:reduced`: `reduced_src` | FullRange:156; graph:2389; blueprint:483–503 | **FAIL** | Algebraic clauses and source's explicitly conditional bordered-system/frame-invertibility clauses match. Frequency carrier still restricted by hS.dio: F1. |
| `bpI:p1:geometry-noA5`: `geometry_noA5_src` | FullRange:179; graph:2518; blueprint:535–544 | PASS | All listed defects/frame estimates, exact constants and strip losses; no torsion-average assumption. `AdmissibleNoTwist` contains only source regularity, margins, bounds and error premises. σT is any real, and σK/σB are not forced positive in the interface. Transposed-error bound is an additional proved conclusion. |
| `bpI:p1:perturbation-noA5`: `perturbation_noA5_src` | FullRange:209; graph:2712; blueprint:566–577 | **FAIL** | All five perturbation clauses and free real σ parameters match, but the tested frequency still requires hS.dio: F1. |

Quantifier review: data and original torus/correction premises precede conclusions; numerical bound parameters remain universally quantified, without wider dependence. Splitting energy-approx into two exports and moving free bound quantifiers into conjuncts does not change their logical scope. No wrapper assumes extended-basic, energy conservation, geometry, or another dependency's proved output as a new premise. Reduced's bordered-system and invertible-frame antecedents are expressly present in source clauses (c)/(d), not illicit output premises.

All nine planned nodes have named interfaces, but only seven satisfy the full literal contract (the bridge with the stated representation note). The Dirichlet theorem and all auxiliary declarations are also accounted for. There are no additional gap-package nodes mapped to these three modules by the GAP-I1a node list; GAP-I1b's 29 local-step exports and GAP-I1c are separate scope. No graph status or dependency edge was edited.

## Proof and definition classification

The Dirichlet proof uses `(N+1)^n` grid points and `(N+1)^n−1` buckets in a bounded interval of linear-form values. Distinct grid points give a nonzero difference with coordinate bound N; the bucket estimate gives `|d·ω| N^n ≤ 2N Σ|ωᵢ|`. Setting `s=Σ|dᵢ|` gives `1≤s≤nN`. Replacing τ in intermediate estimates by `max τ 0` is justified by s≥1, and for τ<n−1 this maximum still lies below n−1 when n≥2. The resulting `γ N^(n−1−max τ 0) ≤ C` contradicts positive-power divergence. No false n=1 negative-exponent claim is used; N≥1 and the zero-frequency case are handled. All divisions in the argument have proved positive denominators.

`SettingSrc` is the **only new structure/definition**: a Prop bundle of source premises over the full typed domain. It has no witness selection, fallback, junk value, or hidden conclusion field. No new `def` or `abbrev` occurs. `tau_ge`, `setting`, `k_bridge` and all FullRange outputs are proved theorems. The max-one transformations only weaken DK/Gram bounds; `mSize_max_one` proves the constants unchanged. Thus extending σT to all real values is genuine, not a hidden restriction or a change of normalizer.

These are new unsigned export names, not replacements of declarations in the original Part123 signature file. GAP-PLAN-I supplies their new contract. A whitespace-normalized header comparison against the eight landed parent declarations returned `True` for all eight after exactly replacing `Setting ... σK σB σT` by `SettingSrc ...` and making σ parameters explicit for the two noA5 wrappers. The inherited energy-defect interface is the amended cube-local D21 form. No signed declaration was changed. Agreement with the old parent headers does not excuse F1 under the current unsigned-node rule.

Provider/frozen-type and seal-body probes are **not applicable**: no provider, frozen theorem export or anchor body is introduced. An independent temporary probe did elaborate the prescribed full Dirichlet theorem type. The import closure contains 75 project modules, no provider and no frozen theorem module, so no DRAFT_SORRY theorem is imported. Existing frozen definitions are reused literally, notably IsDiophantine, complexStrip, Gram, normal frame, torsion, invariance error, extended torsion and energy/torus averages.

## Independent checks

All Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1`. No clean/cache/update, heartbeat override, dependency edit or state-changing git command was used. The build gate applies `nice -n 5` internally. The following are this auditor's fresh results, not copied worker receipts.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gi1a KAM.Iso.Linear.DioDirichlet KAM.Iso.Linear.SettingSrc KAM.Iso.Linear.FullRange
[inp-gate] slot 1 acquired 05:18:33 for KAM.Iso.Linear.DioDirichlet KAM.Iso.Linear.SettingSrc KAM.Iso.Linear.FullRange
Build completed successfully (3204 jobs).
exit 0

LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPI1aAudit.lean
exit 0; no errors or warnings
```

The probe imports FullRange, checks the exact Dirichlet target, and prints axioms of every manually declared new public theorem (15). Output, with each name followed by its exact reported axiom list:

```text
KAM.DioDirichlet.bucket_bounds: [propext, Classical.choice, Quot.sound]
KAM.DioDirichlet.exists_small_combination: [propext, Classical.choice, Quot.sound]
KAM.IsDiophantine.n_sub_one_le_tau: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.SettingSrc.tau_ge: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.SettingSrc.setting: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.SettingSrc.k_bridge: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.mSize_max_one: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.extended_basic_src: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.last_row_src: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.energy_approx_src: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.energy_defect_src: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.energy_conservation_src: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.reduced_src: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.geometry_noA5_src: [propext, Classical.choice, Quot.sound]
KAM.Iso.Linear.perturbation_noA5_src: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Linear.DioDirichlet KAM.Iso.Linear.SettingSrc KAM.Iso.Linear.FullRange
replaying KAM.Iso.Linear.FullRange
replaying KAM.Iso.Linear.SettingSrc
replaying KAM.Iso.Linear.DioDirichlet
exit 0
```

The modules have 207, 99 and 241 physical lines respectively; maximum widths are 96, 96 and 100 characters. Each has copyright, `module`, public imports, module docstring and public section. No forbidden proof escape, resource override, EuclideanSpace, harmful root shadow, or reused public helper short name was found. Repository-wide declaration searches locate `bucket_bounds`, `exists_small_combination` and `mSize_max_one` only at their new declarations; all are namespace-qualified. New structure fields have the intended names and namespace; no exposed definition body is missing because no new computational definition was added.

```text
git diff --check inp...HEAD
exit 0; no output

git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output
```

## Source defects, limitations and deliverable

F1 is a source/interface scope discrepancy already identified as B2/D3, not a newly demonstrated false mathematical theorem. Exact source quotations and locations are above. The plan offers an explicit decision or an arbitrary-frequency proof; neither is established by N1 alone. No additional suspected pinned-source erratum was found, and no external PDF re-audit was required or performed for this infrastructure package. No frozen file, source contract, graph record or original signature was repaired by the auditor.

Only this report was written outside temporary worktree-local `.lake/abi-scratch/` files. Scratch artifacts were removed at closeout. Final lint and report-integrity results follow.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1269 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the explicitly permitted generated-root exception; no other lint diagnostics occurred. KAM.lean was not regenerated. Final `git diff --check inp...HEAD` and a Python check of report trailing whitespace passed with no diagnostics. `git status --short` contains only this new report and the pre-existing untracked handoff. No production changes were made, and both scratch files created for this audit were deleted.
