# GAP-P9b independent audit 2

Date: 2026-10-29. **Verdict: PASS WITH NOTES for the required unsigned graph-node package.** Both audit-1 findings are resolved at HEAD. No frozen anchor is claimed or sealed by this package. The optional dictionary remains outside required scope, and the generated-root lint exception is explicitly authorized.

## Scope and authority

Audited HEAD `771afbafe2df671ae4543545c07db5377ee89091`, against local `inp` `5d2c928069e3d3bcea1f688373decd8fda061515`, using the complete `git diff inp...HEAD`. That diff adds the 180-line GoodSetNodes module, the handoff and audit 1 (322 inserted lines total). Also inspected the revision relative to audit-1 HEAD `cf40e885`. Initial working tree was clean. The shared inp reference advanced during the audit (later observed as `d6fa120cc475a689316bdbf716406c2fcc856747`); the full three-dot diff still has the same three-file, 322-line scope. The initial comparison is pinned by the hash above; HEAD did not change.

Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff including AUDIT FOCUS, audit 1, GAP-PLAN-P lines 403–412, the P810 design mapping and selected analytic route, the Track P statement conventions, and the actual dependency interfaces and relevant frozen oscillator/average definitions. The user's exact worktree destination overrides the generic brief's main-worktree destination. Audit scope is only `KAM/Planetary/SecularSpectrum/GoodSetNodes.lean`; dependencies were inspected for meaning and applicability, not repaired.

All six new declarations are UNSIGNED theorems. There is no signed signature equality obligation, provider/frozen type-equality obligation or seal-body probe for this package. Required graph records read: `bpP:p9:good-set` (DEPGRAPH lines 17248 onward), `stepP:p9:gs-c` (17342 onward); also read optional `bpP:p9:dict` (17190 onward). Compared their SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS and SOURCE_CONCLUSION with the cited blueprint text, Part 9 lines 15–16, 155–183. No other required node is assigned to this module by the GAP-P9b plan. Already proved steps and alternative routes are not additional required exports.

## Per-node and per-declaration assessment

Names below are in `KAM.Planetary.SecularSpectrum`; line numbers are in GoodSetNodes.lean.

| Node / clause | Declaration | Verdict | Reason |
|---|---|---|---|
| `stepP:p9:gs-c`, zero-set half | `good_zero_set_small` (:34) | PASS | Starts with D, an open connected B inside axes, and a nonzero point. Proves analyticity/dichotomy internally; exports relative closedness, relative nowhere density, and Lebesgue nullness. |
| Internal dimension consequence | `two_le_of_mem_goodAxes` (:70) | PASS | Derives `2 ≤ n` from good-point data, using D.hn and the zero one-planet spectrum. No dimension premise is added to source exports. |
| `stepP:p9:gs-c`, compact half; good-set (c) | `good_uniform_nonresonance` (:80) | PASS | Any compact K inside goodAxes; α chosen after K and before all a,k. Handles empty K before deriving dimension and constructing the finite-mode minimum. Stronger spatial scope than a fixed connected B. |
| `bpP:p9:good-set` (b), nonzero Ω | `two_sigma_ne_zero` (:94) | PASS | From the literal good-point hypothesis only, each `2 * sigma D a j` is nonzero. Dimension is derived internally. |
| `bpP:p9:good-set` (b), local applicability | `good_diagonalize_data` (:102) | PASS | Exports analytic sorted eigenvalues and strict order at every good point, plus a positive-radius action-image patch containing its center, open and inside actionDomain, with analytic SO frame and exact diagonalization. Exports patchwise nonzero Ω as well. These are the actual landed diagonalize inputs; its remaining dimension requirement follows from :70. |
| `bpP:p9:good-set` (a)–(c) | `good_set_bundle` (:145) | PASS | Polynomial symmetry/characteristic representation, analyticity and label independence; NR4 iff and analytic distinct spectrum at every good point; diagonalization applicability; dichotomy and uniform compact bound. No unsourced premise. |
| `stepP:p9:gs-c`, entire node | zero-set and compact exports together | PASS | Both literal clauses are established from source data. No dependency output is assumed. |
| `bpP:p9:dict` | no new declaration | EXEMPT | Optional under the explicit handoff ruling and plan item 6. No claim that the full dictionary was proved. |

For good-set (a), the characteristic polynomial representation is stronger than the physical-matrix restriction: its polynomial works for all real Hermitian matrices. The bundle's quantified pointwise clause (b) supplies analytic/distinct eigenvalues at every member of the good set in (c); those fields need not be repeated under the disjunction. `AnalyticAt ℝ (sigma D) a` is the assertion that the actual sorted spectrum is analytic on a neighborhood of a, not merely that the symmetric good polynomial is analytic. The `∀ a` pointwise scope precedes the `∀ B` dichotomy, as in the source. Compact constants do not depend on a or k. No coupling parameter enters their scope.

## Audit-1 findings and proof review

**F1 resolved.** Source Part 9 line 15 permits n≥1. The previous extra `2 ≤ n` binder has been removed from all four affected exports. The new helper proves that a good point rules out n=1: the integer mode identically 1 belongs to k4 in dimension one but annihilates sigma_one. For a nonempty K, membership supplies that good point; for empty K, α=1 works. Thus the one-planet case is covered without changing source premises or assuming a dependency's output.

**F2 resolved.** Lines 103 and 152 now explicitly export `AnalyticAt ℝ (sigma D) a` and `StrictMono (sigma D a)`. Injectivity and nonzero frequencies are also present in the bundle. The proof constructs these from NR4 and sorted_analytic/local_analytic rather than assuming them. This discharges the blueprint line 177 requirement for analytic distinct eigenvalues at every good point.

The zero-set proof uses the genuine analytic-zero dichotomy and continuous preimage closedness, then excludes an open part of the relative closure by density of the nonzero locus. Its relative formulation is appropriate on open B. The compact proof uses a continuous positive finite-mode minimum and compact attainment. The local frame is composed with axis; axis_action and the ball's inclusion in axes justify every evaluation. Local analytic spectral branches are identified with the sorted spectrum by sorted_eq_of_frame. Physical perturbation/expansion premises are already discharged inside the landed diagonalize theorem, whose inputs were checked against the returned fields. No conclusion-shaped hypothesis, hidden instance or hard-step field was found.

## Definitions and hygiene

There are no new def, abbrev or structure declarations, so new-definition classification is vacuous. The referenced Data contains physical positivity and positive dimension, not spectral conclusions. `Vec n = Fin n → ℝ`; modes are `Fin n → ℤ`. Existing axes/goodAxes/simpleAxes, sigma, k4/nr4 and action/axis match the physical domain and source objects. No total-function fallback outside the domain is used to prove an on-domain claim. The oscillator normalization remains `(p_j²+q_j²)/2`, with Ω expressed literally as `2σ`.

Direct scan: 180 lines, maximum Unicode width 100; no sorry/admit/axiom/unsafe/opaque/EuclideanSpace/set_option token. Copyright, module command, public imports, module documentation and public section are present. Every new public short name occurs as a declaration exactly once across KAM. All six declarations lie inside KAM.Planetary.SecularSpectrum; no harmful root shadow.

Recursive KAM import inspection: 103 modules including the audited module; no provider. All 47 imported frozen module paths are manifest-matched SEALED definitions. No frozen theorem or DRAFT_SORRY anchor is imported.

## Independent checks

Every Lean/Lake command was serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`, including lint's subordinate ABI check. No production edits, cache fetch, clean, update, resource overrides or state-changing git operations were performed. The only repository addition is this report; the scratch probe is removed after use.

Targeted build:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp9b KAM.Planetary.SecularSpectrum.GoodSetNodes
[inp-gate] slot 1 acquired 02:25:03 for KAM.Planetary.SecularSpectrum.GoodSetNodes
Build completed successfully (9149 jobs).
exit 0
```

Existing dependency warnings were replayed (unused variables/style and deprecated names); no warning in the audited module.

Axiom probe imported the audited module and issued `#print axioms` for every new theorem:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/gp9b-audit2.lean
'KAM.Planetary.SecularSpectrum.good_zero_set_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.two_le_of_mem_goodAxes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_uniform_nonresonance' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.two_sigma_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_diagonalize_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_set_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

Kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.GoodSetNodes
replaying KAM.Planetary.SecularSpectrum.GoodSetNodes
exit 0
```

Source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1201 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only failure is the explicitly permitted generated-root staleness. It is not a finding, and KAM.lean was not regenerated.

A second elaboration of the same scratch path explicitly imported both GoodSetNodes and SecularSpectrum.Diagonalize, repeated all six axiom checks and proved a consumer example: from only D and membership in goodAxes, obtain a positive-radius patch/frame and apply the actual diagonalize theorem to deduce its quadratic oscillator-action identity. Exit 0, no additional output beyond the six axiom lines above. The initial consumer attempt omitted the Diagonalize import and failed with `Unknown identifier diagonalize`; adding that scratch-only import resolved the probe setup error. Production GoodSetNodes exports applicability data and does not itself need to import Diagonalize.

Protected-path and whitespace checks:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check inp...HEAD
(no output; exit 0)
```

## Notes, source defects and limits

No new suspected pinned-source defect or frozen-statement defect was identified. Blueprint line 183 says the zero set is “closed, nowhere dense and null”; closedness and nowhere density are relative to the stated open domain, as the export correctly makes explicit. This is not a source erratum. No implementation deviation remains for the required nodes. The handoff's approximate line count and five-export description predate the round-2 sixth helper; the current source and this report control the assessment.

The optional dictionary is still unproved as a complete node and is exempt, not silently closed. This report certifies the required GAP-P9b slice only; it does not seal a frozen anchor or certify a planetary headline.

Final verification: the report has no trailing-whitespace errors; the initial pinned-base three-dot diff and protected-path checks remain clean. Scratch probe deleted. Final git status contains only this new report.
