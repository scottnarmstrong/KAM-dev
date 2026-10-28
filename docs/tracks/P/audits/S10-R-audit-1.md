# Independent S10-R package audit 1

Overall verdict: **PASS WITH NOTES**. The S10-R slice is **COMPLETE**: all five assigned declarations match the binding signatures, and all ten additional public helpers prove the stated supporting facts. No proof or statement defect found. Notes concern the permitted stale generated root, an explicit broader import than the package row lists, and an existing short-name homonym. This is an infrastructure audit; no frozen anchor is sealed by S10-R.

Audited `/root/code/KAM-inp-s10r`, branch `inp-s10r`, HEAD `c1db3418d42896eca8fcc5e95644725aa77c0a48`, against `inp` at `ccd0fdc16c5e59bc83b9bda4321d2d85eadb8825`, using `git diff inp...HEAD`. The diff has Frequency.lean plus six inherited S10-F files. As explicitly instructed, only `KAM/Planetary/Nondegeneracy/Frequency.lean` (230 lines) is independently audited here; inherited S10-F is consumed, not certified by this report. The pre-existing untracked S10-R handoff was left untouched. Only this report and temporary worktree-local audit scratch were written.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, handoff and offloaded S10-R brief, track-P statement, blueprint Part 10, P810 design and both design audits, relevant frozen definitions and the P-G anchor. The missing worktree-local draft signature was read at the binding `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`; the design audits are in `docs/tracks/P/design/`, rather than the handoff's `audits/` spelling. Signature SHA-256: `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design audit 2.

## Declaration inventory

Names are relative to `KAM.Planetary.Nondegeneracy`; line numbers refer to Frequency.lean.

| Node / role | Declaration | Verdict | Evidence |
|---|---|---|---|
| conv#data; component calculus | `analyticAt_action` (38) | PASS | Positive square-root argument from standing masses and positive axes; analytic regularity, not merely smoothness. |
| conv#data; component calculus | `analyticAt_axis` (46) | PASS | Polynomial divided by a fixed strictly positive mass/gravity denominator; valid at every action vector. |
| conv#data; inverse | `axis_action` (51) | PASS | Literal square-root identity on axes with nonzero physical constants. |
| conv#data; inverse | `action_axis` (60) | PASS | Positive-action guard is necessary for sqrt of a square; no inverse asserted on negative actions. |
| conv#data; openness | `actionDomain_eq` (70) | PASS | Exact image characterization by positive actions and axis membership. |
| bpP:p10:conv#data | `action_diffeomorphism` (80) | PASS | Exact signature lines 739–744; all eight clauses, including openness and both inverse identities. |
| bpP:p10:sec-rnd#data | `frequency` (102) | PASS | Exact signed concatenation of Kepler frequencies and twice sorted secular eigenvalues at axis(I). |
| bpP:p10:sec-rnd#data | `frequencyAxes` (104) | PASS | Exact signed pullback along action; definition body checked by rfl. |
| sorted-analytic / rnd | `analyticAt_frequency` (106) | PASS | Positive-action inverse cubes; sorted_analytic composed with analytic axis, using axis_action. |
| sorted-analytic / rnd | `analyticAt_frequencyAxes` (122) | PASS | Composition with analytic action on axes. |
| stepP:p10:rnd-a | `exists_relation_ne` (127) | PASS | Stronger support lemma: B need only be open, nonempty and inside axes; identity factor of Fc and zero-null exclude identical vanishing. |
| finite-component calculus | `sum_append` (143) | PASS | Exact Fin sum decomposition; valid for arbitrary n, x, y, c. |
| stepP:p10:rnd-a | `exists_freq_ne` (149) | PASS | Coefficients (c_fast,2*c_slow) remain nonzero; factor 2 handled exactly. |
| bpP:p10:rnd; rnd-a,b | `rnd` (171) | PASS | Exact signature lines 486–492, all six conjuncts retained; joint and separate nondegeneracy, both action and axes analyticity. |
| bpP:p10:scaling; rnd-c | `scaling` (211) | PASS | Exact signature lines 494–496; inverse-permutation coefficient transform c(p⁻¹j)s(p⁻¹j), positivity prevents zero, finite sum reindexing. |

No new public theorem assumes its own result or a substantive unpaid proof step. Every helper's premises are standing physical/typing data, positivity/domain guards or source nondegeneracy in the explicitly conditional scaling theorem. No extra premise, weakened conclusion, changed carrier, or enlarged constant dependence was found. There are no new quantitative constants.

## Definitions and mathematical review

Exactly two new definitions; no abbrev or structure. `frequency` is a literal total map `Vec n → Vec (n+n)`, with the signed body unchanged on its entire carrier. `frequencyAxes` is exactly composition with `action`. Their dependent total operations (division, real sqrt, sorted spectrum) are the existing intended objects; every analytic/inverse use is guarded by positivity/simple spectrum. No theorem exploits values at singular or negative inputs. Both definitions are exposed by the module's `@[expose] public noncomputable section`.

Action-domain openness is proved from `actionDomain_eq`: the finite intersection of strict positive-coordinate sets intersected with the continuous axis map's preimage of open axes. The analytic inverse on the image follows from the global polynomial formula for axis and positivity of action-image coordinates. Convexity and connectedness of axes come from the existing proved GoodAxes lemmas; these hold even at n=0, so the signature's stronger arbitrary-dimension convention lemma is consistent.

The relation argument at lines 127–141 consumes S10-F's actual `f_nonzero`, `fc_analytic`, and literal product `fc_def`. If a relation vanished throughout B, its identity-permutation factor would make Fc vanish there. S10-Z's `analytic_zero_null` makes that zero locus null in the connected open axes domain; nonempty open B has positive Lebesgue measure, contradiction. This is the designed analytic-zero route, with an equivalent measure contradiction instead of a second direct identity-theorem invocation. Sorted analyticity is consumed through `Nondegeneracy.sorted_analytic`, whose implementation uses S9-S's `local_analytic` and identifies its increasing analytic eigenvalue enumeration with the existing sorted spectrum.

The `hBS : B ⊆ simpleAxes D` premise is literally present in the signature (line 487), blueprint p10 lines 173–180, and Frequency.lean:172. Its discriminant restriction is used only in the analytic conjuncts; the nondegeneracy argument uses its axes-membership part. It is not an added hypothesis and is not vacuous: S10-H `good_point`/`good_set` supply good axes and open balls, and good axes have nonzero discriminant by the literal product defining `good`. `IsConnected B` includes nonemptiness; the proof explicitly uses `hBc.nonempty`. Connectedness beyond nonemptiness is unnecessary for the relation helper, which is a valid strengthening. No analyticity through spectrum collisions is asserted for sorted eigenvalues; only the symmetric product is analytic there.

The separate fast/secular conclusions follow by extending coefficients by zeros. This also proves the fast-axes assertion in blueprint rnd(b) by pulling back the action-image clause. Openness and connectedness of action-image patches follow from the analytic inverse/continuous action change of variables already proved, rather than being hidden new premises. The scaling theorem preserves nondegeneracy under all positive component rescalings and permutations. Quantitative index/amount scaling belongs to `scaling_amount` in S10-S, not this slice; this report does not claim it here.

## Scope and import notes

1. The design module-table row S10-R (line 448) lists S10-F, S9-S and S10-Z. The implementation additionally directly imports `GoodAxes` (S10-H, earlier wave 7) to obtain `convex_axes`, `isConnected_axes` and `sorted_analytic`. This is a truthful, acyclic earlier-wave dependency, already disclosed in the handoff; the design import row should be updated to list S10-H explicitly. It does not introduce a logical premise or invalidate the exact signed API.
2. The whole-KAM declaration-name scan found no homonyms for 14 names. The prescribed `frequency` has an existing short-name homonym `KAM.Apost.frequency` at KAM/Apost/Frame.lean:423. Its fully qualified name differs from `KAM.Planetary.Nondegeneracy.frequency`; there is no redefinition or duplicated implementation. Thus the handoff's “grepped unique” claim is accurate for its listed helpers, while a literal requirement of uniqueness of every short name throughout KAM conflicts with the signed frequency name. Report this naming ambiguity; do not silently rename the required export.
3. Recursive inspection of all 98 project modules in Frequency's import closure found only frozen **definitions**, no frozen theorem modules and no providers. Thus no DRAFT_SORRY theorem is imported. P-G remains manifest `DRAFT_SORRY`; provider/frozen type equality and seal-body probes are inapplicable to this infrastructure package. Three fresh-name copies of the signed theorem statements were instead elaborated with the exact production exports applied to their explicit binders, plus `type_of%` checks against those copies. Both definition bodies were checked by `rfl`.

## Independent validation

All Lean-related invocations were sequential with `LEAN_NUM_THREADS=1` and niceness 5; the build used the mandatory gate. No cache fetch, clean, update, resource override, generated-file edit or state-changing git command was used.

### Targeted gated build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10r KAM.Planetary.Nondegeneracy.Frequency
```

Exit 0. Gate output: `[inp-gate] slot 2 acquired 15:59:05 for KAM.Planetary.Nondegeneracy.Frequency`; final output: `Build completed successfully (9144 jobs).` Lake replayed upstream unused-variable, deprecated-name and style warnings in Kepler/Energy, Poincare/Chart, Kepler/Mass, SecularForm/Coefficients, SecularSpectrum/Definiteness, LocalAnalytic/Unique, Nondegeneracy/Weyl and SymmetricRelation/Analytic. None was in Frequency.lean. The job count is the targeted dependency traversal, not a clean/full-library rebuild.

### Signature and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10RAudit.lean
```

Exit 0, no diagnostics from any signature or rfl example. The probe copied the three theorem headers from the pinned signature file, supplied the exact production export with explicit binders in order, and checked `example : type_of% @production := @freshCopy`. Independent normalized-header comparison also returned MATCH for all five assigned declarations.

For each of the following 15 `#print axioms KAM.Planetary.Nondegeneracy.<name>` commands, the exact axiom list was `[propext, Classical.choice, Quot.sound]`:

```text
analyticAt_action
analyticAt_axis
axis_action
action_axis
actionDomain_eq
action_diffeomorphism
frequency
frequencyAxes
analyticAt_frequency
analyticAt_frequencyAxes
exists_relation_ne
sum_append
exists_freq_ne
rnd
scaling
```

The output format was `'KAM.Planetary.Nondegeneracy.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`. No sorryAx or nonstandard axiom.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.Frequency
```

Exit 0. Complete output: `replaying KAM.Planetary.Nondegeneracy.Frequency`. This one invocation covers the only module in the independent audit scope, including all its public helpers. No separate provider exists in this package.

### Source lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the expressly permitted stale generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (793 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated root was not regenerated or edited. The source/module, frozen-anchor and elaborated ABI checks passed.

### Static checks and final workspace

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. `git diff inp...HEAD --check`: empty, exit 0. Static forbidden-token/resource-option scan of Frequency.lean: `[]`. File size 230 lines, compliant module header/copyright/imports/docstring/public section, Pi ambient spaces, no EuclideanSpace. All helpers have distinct full names. Temporary audit probe/logs were removed after recording results. Final report whitespace check: passed (no trailing whitespace; final newline present). `git diff --check` also passed; final status contains only this new report and the pre-existing untracked handoff.

## Errata, deviations and limits

No new suspected pinned-paper defect or mathematical blueprint defect found in this scoped module. The inherited blueprint p10:158 quotes Fej04r p.58 “par un raisonnement analogue” and explicitly records an unwritten induction; S10-R consumes S10-F's formal theorem rather than treating the paper sketch as a premise. The inherited universal-cover objection is bypassed by the symmetric-product route. Neither pinned-PDF claim was independently re-audited here.

The import-row omission and short-name ambiguity above are documentation/workflow notes, not repairs to the audited code. No mathematical deviation from the signed statements. The P-G frozen anchor's historical comments and the track statement's draft wording do not constitute closure; manifest status remains authoritative. This report certifies the S10-R infrastructure slice only, with inherited S10-F source/proof audit status and downstream P11A consumers outside scope.
