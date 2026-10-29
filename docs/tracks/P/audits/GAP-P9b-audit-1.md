# GAP-P9b independent audit 1

Date: 2026-10-29. Verdict: **FAIL for literal graph-node closure**. The five Lean proofs pass elaboration, axiom inspection and kernel replay. The failures below concern source hypotheses and the completeness of the unsigned exports, not kernel soundness.

## Scope and authority

Audited HEAD `cf40e885a0b25a9c5b25ddc076d535eb723da873`, compared using the full `git diff inp...HEAD`; current `inp` is `9208f71fad9c557fdee5db7c9a1b7bd222094650`. The entire three-dot diff adds only `KAM/Planetary/SecularSpectrum/GoodSetNodes.lean` (160 lines). The existing untracked handoff was present before this audit.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package-audit brief, the current handoff and its AUDIT FOCUS, GAP-PLAN-P section GAP-P9b, the relevant P810 design mapping, Track P statement, and the graph/source records cited below. The user's explicit report destination overrides the generic brief's main-worktree destination. No production files were edited. The new declarations are all UNSIGNED; this package claims no frozen anchor and has no provider export to seal. Frozen/provider type-equality and seal-body probes are therefore not applicable. The optional dictionary node is excluded by the explicit handoff ruling.

## Findings

### F1 — unsourced dimension restriction

Part 9's standing data are `n ≥ 1` (blueprint-P/parts/p9-secular-spectrum.tex:15); the good-set proposition at lines 173–179 adds no `n ≥ 2`. The graph agrees: docs/graph/P/DEPGRAPH.md:17255–17257 and :17349–17351. In Lean, `SecularForm.Data.hn` is only `0 < n` (KAM/Planetary/SecularForm/Basic.lean:45).

Nevertheless, `good_uniform_nonresonance` (:70), `two_sigma_ne_zero` (:82), `good_diagonalize_data` (:89) and the entire `good_set_bundle` (:128) require `hn : 2 ≤ n`. In particular the compact-uniform conclusion of `stepP:p9:gs-c` and even part (a) and the dichotomy of `bpP:p9:good-set` cannot be obtained by specializing the named exports to `Data 1`. This is an added premise under the literal-export rule. It is not authorized merely because the dependency `min_mode_continuous_positive` has that guard. Its proof output is correctly constructed internally, but its stronger input requirement has been propagated to the source export.

The one-planet good locus is empty (`Nondegeneracy.sigma_one` gives zero spectrum), so its uniform bound is vacuous; polynomiality, analyticity and the identically-zero dichotomy still have content. This explains how the missing case can be handled without changing the source. A good-point premise in the nonzero case can also be used internally to exclude that dimension. The present file contains no such case split. This is a formal coverage failure, not a counterexample to the proved n≥2 statements.

### F2 — the bundle omits analytic eigenvalues on the good locus

The graph's literal conclusion at docs/graph/P/DEPGRAPH.md:17257 and blueprint-P/parts/p9-secular-spectrum.tex:177 explicitly includes an open dense full-measure good set “on every point of which the eigenvalues are analytic and distinct”.

`good_set_bundle` (:128–150) states analyticity of `good ∘ sigma` and of a local frame `R`, but contains no `AnalyticAt`/`AnalyticOnNhd` assertion for `sigma`, no analytic eigenvalue branches, and no exported strictly ordered analytic spectral decomposition on the local ball. Its nonzero branch (:145–150) exports openness, density, null complement and compact non-resonance only. Distinctness at a good point is exported in part (b), so distinctness itself is not missing there.

The local proof of `good_diagonalize_data` obtains analytic branches `s` and their strict order (:101–110), then discards those fields from its result. The landed theorem `Nondegeneracy.sorted_analytic` already supplies the needed analytic spectrum on `simpleAxes` (GoodAxes/SortedAnalytic.lean:41); this does not put that assertion in the new unsigned bundle's literal conclusion. Exporting the restriction to the good locus would complete this clause. The explicit handoff requires the unsigned export to state the literal node, so mathematical derivability from other imported results is insufficient here.

The action-patch hypotheses of `diagonalize` themselves are correctly supplied: openness, inclusion in `actionDomain`, analytic SO frame and the matrix identity are all exported. No failure is assigned merely for exporting applicability data rather than repeating the entire diagonalization theorem.

## Per-node and per-declaration verdicts

Names below are in `KAM.Planetary.SecularSpectrum`. Line numbers refer to GoodSetNodes.lean.

| Node / clause | Declaration | Verdict | Reason |
|---|---|---|---|
| `stepP:p9:gs-c`, zero set | `good_zero_set_small` (:34) | PASS | Open connected B inside axes and one nonzero point; analyticity and dichotomy constructed internally. Relative closedness, relative nowhere density and zero Lebesgue measure are the intended conclusions. No dimension restriction beyond Data. |
| `stepP:p9:gs-c`, compact uniformity | `good_uniform_nonresonance` (:70) | FAIL | Correct positive minimum, α chosen after K and before a,k; all compact subsets of global goodAxes are allowed, a stronger spatial scope. Added `2 ≤ n` leaves source n=1 uncovered (F1). |
| `bpP:p9:good-set` (b), nonzero frequencies | `two_sigma_ne_zero` (:82) | FAIL as literal source export | Correct for n≥2 and assumes only good-point data besides the added dimension guard (F1). |
| `bpP:p9:good-set` (b), diagonalization data | `good_diagonalize_data` (:89) | FAIL as full source export | Genuine local analytic SO frame and exact sorted-spectrum diagonalization; all landed diagonalize inputs supplied. Added dimension guard (F1); analytic eigenvalue/local strict-order fields are not exported (F2). |
| `bpP:p9:good-set` (a)–(c) | `good_set_bundle` (:128) | FAIL | F1 and F2. Part (a)'s characteristic polynomial assertion is otherwise stronger, applying to every real Hermitian matrix. NR4 equivalence, simplicity at the base point, dichotomy and compact bound are correctly proved for admitted dimensions. |
| `stepP:p9:gs-c`, whole node | first two exports together | FAIL | Zero-set half passes; compact half still has F1. |
| `bpP:p9:dict` | no new export | EXEMPT | Read NODE :17190–17207 and source :155–160. Optional by explicit ruling; no finding for its open status. |

No anchor is seal-ready or sealed by this package: it is an unsigned graph-gap package. Required slice closure fails for exactly `stepP:p9:gs-c` and `bpP:p9:good-set` as above. Nodes already proved/bypassed and the two alternative route nodes are not added to the required scope.

## Definitions, proof review and hypotheses

There are **no new def, abbrev or structure declarations**. The five new public declarations are all theorems. Their local objects (zero/good loci, minimum witness and frame composed with `axis`) are the intended objects, with no fallback or junk value used in a proof. Existing `Data` contains physical positivity and dimension data, not a spectral conclusion. Existing `axes`, `good`, `goodAxes`, `sigma`, `k4`, `nr4`, `action`, `axis` and the frozen oscillator action match the source objects on the stated carriers. The positive increasing-axis carrier is the physical domain intended by the source shorthand.

The zero-set proof builds analyticity from `good_set`, uses the dichotomy to obtain density/nullness, and uses continuity for relative closedness. Its `B ∩ interior (closure Z) = ∅` is a correct formulation of nowhere density relative to open B, rather than an unjustified ambient closedness claim. The compact proof minimizes the finite-mode absolute value on K and handles empty K explicitly. The frame proof uses genuine local spectral decomposition and the inverse axis/action identities. No theorem assumes analyticity, an eigenframe, the dichotomy or a positive minimum as an input; those dependency outputs are proved internally. Quantifier order for B, local radius/frame, and compact α is appropriate. No constant acquires a coupling-parameter dependence.

## Independent verification

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`. No cache fetch, clean, update, rebuild-from-scratch, resource override or production edit was used.

1. Targeted compile gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp9b KAM.Planetary.SecularSpectrum.GoodSetNodes
[inp-gate] slot 1 acquired 02:12:07 for KAM.Planetary.SecularSpectrum.GoodSetNodes
Build completed successfully (9149 jobs).
exit 0
```

Warnings were replayed from existing dependencies (Kepler.Energy, Poincare.Chart, SecularForm.Coefficients, Definiteness, LocalAnalytic.Unique, Nondegeneracy.Weyl and SymmetricRelation.Analytic). No warning was reported in GoodSetNodes.

2. A scratch probe imported the audited module and ran `#print axioms` for every new theorem:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/gp9b-audit.lean
'KAM.Planetary.SecularSpectrum.good_zero_set_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_uniform_nonresonance' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.two_sigma_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_diagonalize_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.good_set_bundle' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

3. Kernel replay, one invocation for the sole new lemma module:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.GoodSetNodes
replaying KAM.Planetary.SecularSpectrum.GoodSetNodes
exit 0
```

4. Source lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1201 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the explicitly allowed stale generated root. It is not a finding; the root was not regenerated.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. `git diff --check inp...HEAD`: empty, exit 0.

6. Direct source scan for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` and `set_option`: no matches (rg exit 1). Module header, module command, public imports, documentation and public noncomputable section are present. File length 160; maximum Unicode line width 100. No file-size or line-width violation.

7. Public short-name declaration scan across KAM found no other declaration with any of the five new names. All are inside `KAM.Planetary.SecularSpectrum`; no harmful root shadow was introduced.

8. Recursive KAM import inspection found 103 KAM modules, no provider, and only SEALED frozen definitions (47 modules), with no frozen theorem import and no DRAFT_SORRY anchor. Thus no forbidden provider/draft dependency enters the new results.

## Source defects, deviations and limits

No new suspected defect in a pinned external mathematical source or frozen declaration was identified. Source wording “closed” for a zero set on an open connected domain is interpreted relatively, as required mathematically; this is not an erratum. F1 and F2 are implementation/contract deviations from the stated graph nodes. The docstring's assertion that `2 ≤ n` is a source hypothesis (:122) is not supported by the cited good-set proposition and standing convention. No production repair was attempted in this report-only audit.

The optional Ω/eigenvalue dictionary remains outside scope by ruling. The generated-root lint exception is authorized and is not a finding. This audit does not certify any physical planetary headline or frozen theorem.
