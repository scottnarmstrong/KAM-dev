# P23-11 independent package audit 1

Overall verdict: **PASS WITH NOTES** for P23-11, at HEAD `067d05299d279b03358836845306555c8d0b7d93`.
The three assigned exports `KAM.Planetary.ob_der`, `osc_bracket`, and `ob_field` PASS their
revision-2 design contracts. No frozen anchor/provider is assigned or sealed by this infrastructure
package, so provider/frozen-type and literal frozen-seal-body probes are **not applicable**.
This does not assert completion of downstream P23 packages or any frozen planetary theorem.

## Scope and authority

Read AGENTS.md, PLAN, DECISIONS, the shared package-audit brief, local handoff/AUDIT FOCUS,
P23-LEAN-DESIGN revision 2 and both design audits, the relevant track-P statement context,
OscillatorSetting and the Weighted Cauchy/algebra/parametric interfaces, and blueprint-P Part 2
L165–180. The exact user-directed report destination overrides the brief's generic main-worktree
output sentence. Only this report is changed; temporary probes/logs are removed from local
`.lake/abi-scratch/` after recording their results.

`git diff inp...HEAD` reports two new files: OscillatorSetting (69 lines, inherited P23-06) and
OscillatorBracket (1103 lines). Git warns about multiple merge bases; it selects
`5847c76fbf9293181c8193218a7caf28ad3495d5`; the other merge base is
`dc53913117b4e52c657fbb011fe01bd6ee17ef4c`. As instructed by AUDIT FOCUS, proof audit scope is
ONLY `KAM/Planetary/Averaging/OscillatorBracket*.lean`, compared also with `inp-p2306`
(`f8bb6eda3b4c7ba1e3e36a19f6d542b162f1f7eb`). That scoped diff is one new 1103-line module.
The unrestricted diff from inp-p2306 contains unrelated integration work and is not this package's scope.
The pre-existing untracked handoff is preserved.

## Statement and proof findings

All three public contracts were independently copied from the embedded design statements into
fresh theorem commands and proved by applying the actual exports to the listed explicit binders.
Each copied statement also equals `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` after
whitespace normalization. This checks binder order, carriers, hypotheses and all conclusion clauses
against independent design text, rather than reconstructing the type from the implementation.

G1 is paid without a new premise: `ob_der` L575–610 takes only positive target widths and strict
outer containment, and evaluates every derivative at `S−σ`. Its angular denominator is
`exp 1 * (S₀−S+σ)`, positive even if S₀≤S. `wsum_dtheta_le` L96–109 invokes the existing
fixed-parameter Cauchy sum. `wsum_dI_le` L113–184 proves the necessary anisotropic estimate on
an actual coordinate disc; it does not falsely identify oscParams with an isotropic polyNbhd.
Finite coefficient sums are dualized before Cauchy, then nonnegative finite-sum bounds establish
summability and the full weighted estimate. Each disc-containment condition is discharged by the
coordinate line lemmas in the final contracts; it is not an assumed hard step in an export.

Transport is genuine: the inherited unpack-after-pack identity and new pack-after-unpack identity
are inverse coordinate permutations for phase order ((θ,q),(I,p)). The continuous linear maps
have exactly those functions as bodies. Derivative identities use the chain rule at open-domain
points. Coefficient congruence uses equality on every real angular slice, which lies inside the
positive target strip; it does not rely on off-domain fderiv defaults.

`bracket_flat_eq` L826–840 gives the correct θ/I and q/p signs. In `bracket_bound` L862–1051,
the angular sums are bounded at the fixed x before the uniform parameter quantifier is closed.
There is no sum of global angular norms. The two oscillator coordinate sums contribute m each;
`coeff_mul` and the finite-sum triangle bound justify products and the signed sum, with explicit
summability. Positive minimum denominators justify the final W comparison. The final theorem
also proves holomorphy and periodicity of the bracket. `ob_field` L647–704 derives each coordinate
bound from ob_der and the weighted-to-sup bridge, then bounds the four gauge components.
Nonnegativity of E/A/B is inferred from a point when needed; empty domains remain harmless.
No conclusion-shaped assumption, hidden instance, new constant dependence or weakened target was found.

Notes on coverage: the blueprint additionally displays the elementary scalar comparison
`W≤2(1+m)R` (Part 2 L174–175). It is not separately exported by this package, and is not in any
of the three assigned design signatures. The exact W estimate is proved; this report does not
claim a separate Lean declaration for that scalar corollary. Dimension hypotheses hn/hm in
osc_bracket are retained exactly although unused by its stronger underlying proof.

## Declaration-by-declaration review

All names below are in `KAM.Planetary`; parentheses give OscillatorBracket.lean line numbers.
Auxiliary declarations implement local components of the assigned nodes and are not advertised
as replacements for a full blueprint theorem. Every new declaration is listed.

| Node | Lean declaration | Verdict | Reason or note |
|---|---|---|---|
| auxiliary: ob-der / ob-prod | `polyNbhd_singleton` (47) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `FClass` (53) | PASS | Total intended auxiliary object; see definition classification. |
| auxiliary: ob-der / ob-prod | `FClass.inClass` (57) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `FClass.mono_width` (66) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `FClass.mono_set` (72) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `coeff_differentiableAt_of` (76) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `coeff_dI_eq_of` (86) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `wsum_dtheta_le` (96) | PASS | Weighted.cauchy_theta at fixed parameter; angular sum stays inside uniform bound. |
| auxiliary: ob-der / ob-prod | `wsum_dI_le` (113) | PASS | Actual one-coordinate complex disc, finite-mode dualization, Cauchy and summability. |
| auxiliary: ob-der / ob-prod | `fderiv_shift_eq` (187) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `FClass.fderiv_apply` (196) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `norm_le_of_wsum` (211) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `wsum_dI_le_on` (225) | PASS | Actual one-coordinate complex disc, finite-mode dualization, Cauchy and summability. |
| auxiliary: ob-der / ob-prod | `nonneg_of_wsum` (239) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscPack_oscUnpack` (249) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscUnpackL` (260) | PASS | Total intended auxiliary object; see definition classification. |
| auxiliary: ob-der / ob-prod | `oscUnpackL_apply` (272) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscPack_theta` (284) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscPack_I` (288) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscPack_p` (293) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscPack_q` (298) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscUnpack_theta` (309) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscPackL` (315) | PASS | Total intended auxiliary object; see definition classification. |
| auxiliary: ob-der / ob-prod | `isOpen_actionNbhd` (331) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `isOpen_oscParams` (335) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscParams_mono` (351) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `isOpen_oscDom` (358) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscUnpack_mem_oscDom` (363) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscClass.flat` (368) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `fderiv_oscFunction` (389) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `coeff_congr_real` (400) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscBound_of_flat` (408) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `norm_smul_single` (427) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `mem_actionNbhd_add` (431) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `line_I` (441) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `line_p` (462) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `line_q` (497) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `ob_der_dir` (539) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `ob_der_theta` (557) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| stepP:p2:ob-der | `ob_der` (575) | PASS | Exact revised signature; four losses; target S−σ; no S<S₀ premise. |
| auxiliary: ob-der / ob-prod | `oscDom_mono` (620) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscClass.mono` (624) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscClass.fderiv_apply` (628) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `oscBound.norm_le` (641) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| stepP:p2:ob-field | `ob_field` (647) | PASS | Exact design signature; all four gauge components, same loss minimum. |
| auxiliary: ob-der / ob-prod | `osc_deriv_eqs` (716) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `comp_aux` (741) | PASS | Positive denominators and nonnegative multipliers; Mn≤a*b gives correct comparison. |
| auxiliary: ob-der / ob-prod | `wsum_sum_le'` (749) | PASS | Linear Fourier coefficients and summable finite triangle bound; no unsupported interchange. |
| auxiliary: ob-der / ob-prod | `lineI'` (786) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `lineP'` (794) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `lineQ'` (802) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `BIdx` (811) | PASS | Total intended auxiliary object; see definition classification. |
| auxiliary: ob-der / ob-prod | `brCoeff` (813) | PASS | Total intended auxiliary object; see definition classification. |
| auxiliary: ob-der / ob-prod | `brFun` (816) | PASS | Total intended auxiliary object; see definition classification. |
| auxiliary: ob-der / ob-prod | `bracket_flat_eq` (826) | PASS | Coordinate, domain, regularity or coefficient transport; premises are local typing/analytic data. |
| auxiliary: ob-der / ob-prod | `prod_term` (842) | PASS | Weighted.coeff_mul applied to the same singleton-neighborhood parameter and width. |
| stepP:p2:ob-prod | `bracket_bound` (862) | PASS | Fixed-parameter angular sums, coordinate products, exact W arithmetic. |
| bpP:p2:osc-bracket | `osc_bracket` (1069) | PASS | Exact design signature; class and W/min-product bound, correct m factor. |

## Definition classification

- `FClass` (53): genuine holomorphy and angular period-one predicate on strip × arbitrary parameter set.
- `oscUnpackL` (260), `oscPackL` (315): continuous complex-linear coordinate permutations on their entire
  finite-dimensional carriers, including zero-dimensional cases; no domain-based default values.
- `BIdx` (811): disjoint union indexing the four canonical product families, including empty Fin blocks.
- `brCoeff` (813): total signs +1, −1, +1, −1, matching the displayed canonical bracket.
- `brFun` (816): total coordinate-derivative products in the correct flat I,p,q order. Lean fderiv is
  total; all analytic/bracket identities used in the proof are restricted to differentiable points.

These are all six new def/abbrev declarations. No new structure or instance is introduced.
All are in an exposed public noncomputable section. No junk/fallback is exploited.

## Independent validation

All Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1`; builds used the prescribed
compile gate (its script runs `nice -n 5 lake build`). No clean, cache fetch, package update or
source/build-root regeneration was run.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2311 KAM.Planetary.Averaging.OscillatorBracket
[inp-gate] slot 1 acquired 08:18:54 for KAM.Planetary.Averaging.OscillatorBracket
Build completed successfully (9091 jobs).
exit 0
```

This is the gate's job-graph count, not a claim of rebuilding the library from scratch.

2. Independent signature and axiom probe:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2311Audit.lean
exit 0; three copied-design theorem commands elaborate; no errors or warnings.
```

The copied bodies apply `ob_der hu hA hpos houter`,
`osc_bracket hn hm hu hw hA hB hρ hρp hρq hσ houter`, and
`ob_field hφ hE hρ hρp hρq hσ`, respectively. Exact #print axioms output for all
52 new public theorems follows:

```text
'KAM.Planetary.polyNbhd_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FClass.inClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FClass.mono_width' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FClass.mono_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coeff_differentiableAt_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coeff_dI_eq_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wsum_dtheta_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wsum_dI_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_shift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FClass.fderiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_le_of_wsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wsum_dI_le_on' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.nonneg_of_wsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscPack_oscUnpack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscUnpackL_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscPack_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscPack_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscPack_p' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscPack_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscUnpack_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_actionNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_oscParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscParams_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_oscDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscUnpack_mem_oscDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscClass.flat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_oscFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coeff_congr_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscBound_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_smul_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_actionNbhd_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.line_I' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.line_p' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.line_q' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ob_der_dir' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ob_der_theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ob_der' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscDom_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscClass.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscClass.fderiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscBound.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ob_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_deriv_eqs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.comp_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wsum_sum_le'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lineI'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lineP'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lineQ'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.bracket_flat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.prod_term' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.bracket_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (the one scoped module contains all new lemma declarations; there is no provider module):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorBracket
replaying KAM.Planetary.Averaging.OscillatorBracket
exit 0
```


4. Full repository source lint (including frozen guard and ABI tail):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (463 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the explicitly permitted stale generated KAM.lean check. Module, frozen-anchor,
and ABI checks pass. No generated file was edited or regenerated.


5. Source hygiene: 1103 total lines (below 1500); zero lines over 100 Unicode characters;
no sorry/admit/axiom/unsafe/opaque/EuclideanSpace or resource override tokens. The only local
option is `set_option linter.unusedVariables false in` for the retained hn/hm binders. Copyright,
module declaration, public imports, module docstring and exposed public section are present.
A recursive project-import scan visited 45 project modules: no Provider imports, no frozen theorem
imports (hence no imported DRAFT_SORRY theorem); the 12 frozen dependencies are definition modules.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(empty stdout; only the multiple-merge-base warning on stderr)
git diff --check inp...HEAD
(empty stdout; exit 0; same merge-base warning)
```

## Blueprint/source defects, deviations and uncertainties

Known G1, `blueprint-P/parts/p2-averaging.tex:177`, says
“sum_i ... at S ... /(e(S_0-S))” under only `S−σ<S₀`.
That intermediate width may exceed the available strip; its denominator can be nonpositive.
Design revision 2, G1 row at `P23-LEAN-DESIGN.md:229`, explicitly corrects the evaluation width
to S−σ and denominator to e(S₀−S+σ). The code implements exactly that recorded repair, and its
bracket conclusion still agrees with the blueprint's printed W. This is an inherited blueprint
defect/declared repair, not a newly alleged defect in a pinned primary source. No new pinned-source
erratum or undeclared mathematical deviation was found. No fresh PDF verification is claimed.
The handoff's 1094-line figure is stale; the audited file has 1103 lines, still within the cap.
Only the assigned infrastructure contracts have passed; root closure, downstream applicability
beyond these interfaces, and the other P23 packages are not certified by this audit.
