# P11A-C7 independent package audit 1

Verdict: **PASS WITH NOTES for the scoped C7 implementation**. All four requested signature surfaces match, and the nonlinear continuation, actual variational derivative and two-sided Gronwall arguments are sound. No frozen anchor is implemented or sealed by this package. This verdict does not close the entire blueprint lemma's coefficient-constant clause or the later real/complex flow identification.

## Scope and authority

Audited HEAD `24ba56d8b7ac7bd2af3e4a5fb7c4c742f6d3e912` against branch `inp`, which resolved to `2bc21e5bb024a3cd6d69c6c8fbc587eb0dc224d5`, using `git diff inp...HEAD`. As instructed by the handoff, substantive implementation review covers only:

- `KAM/Planetary/MaximalStep/GlobalRealFlow.lean` (153 lines).
- `KAM/Planetary/MaximalStep/RealFlow.lean` (100 lines).

The five other files in the branch diff belong to the C6/base delta and are outside this audit. The pre-existing untracked handoff is untouched. Only this report persists; temporary probes are confined to this worktree's `.lake/abi-scratch/` and removed after verification. The user's exact worktree report destination overrides the generic brief's main-worktree output instruction.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package brief, handoff, track-P statement, design row C7/proof plan/Appendix A, and the relevant entries and findings of design audits 1–3. The signature and design-audit files absent from this checkout were read at `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` and `/root/code/KAM-inp/docs/tracks/P/design/DESIGN-P11A-design-audit-{1,2,3}.md`. Direct imports and the 16-module project import closure contain no frozen module or provider; provider/frozen type and seal-body probes are therefore inapplicable. There is no manifest anchor whose PASS could mean seal-ready here.

Snapshot hashes (SHA-256):

| Input | Hash |
|---|---|
| GlobalRealFlow.lean | `dcaedc1fad1b476f5c227226bf654cf2a5840fdf20abb6ad8ec888126b747909` |
| RealFlow.lean | `948241dfd5523ed7ec7b0a8dac66e304b348b34c510e50f4c60fc0f8a9087182` |
| Current supplied P11ASignatures.lean | `36f4f5b6da43859e9008cb3e1e0a611d926146805a63b4420de6e1fb540a3d1b` |
| Worktree P11A-LEAN-DESIGN.md | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| p11a2-cutoff-step.tex | `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec` |

The current external signature hash differs from the historical R3 report's whole-file hash. The three C7 theorem headers were independently compared against both the current signature and the worktree's pinned Appendix A: all equal byte-for-byte before the proof assignment. The complete `open Classical in def p11RealFlow ...` command also equals the supplied definition byte-for-byte. No historical whole-file identity is inferred.

## Declaration and node ledger

All names below are in namespace `KAM.Planetary`; locators refer to the two scoped files.

| Node / role | Declaration (file:line) | Verdict | Evidence / note |
|---|---|---|---|
| rl-global displacement helper | `p11_norm_sub_le_of_sol` (GlobalRealFlow:32) | PASS | Mean-value inequality on `uIcc a b`; general interval displacement, stronger than the unit-time consequence. |
| rl-global forward continuation | private `p11_maximal_top` (GlobalRealFlow:40) | PASS | A hypothetical finite endpoint T traps the forward trajectory in the compact max-norm ball of radius M T; continuation contradicts finiteness. |
| rl-global backward continuation | private `p11_maximal_global` (GlobalRealFlow:67) | PASS | Applies the forward argument to the negated field and maximal solution. |
| rl-global uniqueness | private `p11_eq_global_flow` (GlobalRealFlow:74) | PASS | Generic uniqueness on the full real interval with equal initial values. |
| rl-global / SG3 | `p11_bounded_global_flow` (GlobalRealFlow:82) | PASS | Exact signature L403–406; proves existence, not an assumed solution field. |
| real-flow construction | `p11RealFlow` (GlobalRealFlow:94) | PASS with guarded semantics | Exact literal signature L407–410, including the specified fallback. See definition classification below. |
| choice specification | `p11RealFlow_spec` (GlobalRealFlow:99) | PASS | Uses proved global existence to select the solution branch, then proves initial value and ODE for all real times. |
| choice independence | `p11RealFlow_eq` (GlobalRealFlow:111) | PASS | Every global solution with the same initial value equals the selected flow under the declared C1/boundedness assumptions. |
| rl-deriv / SG4 | `p11_global_variational` (GlobalRealFlow:118) | PASS | Exact signature L412–418; obtains differentiability and the ODE for the actual `fderiv` from `FlowChain.reg_all`. |
| rl-deriv Gronwall helper | private `p11_gronwall_lin` (RealFlow:27) | PASS | Applies Gronwall to Y−id with initial norm zero and inhomogeneous term L; handles L=0 separately. |
| bpP:p11a:real-lipschitz, dynamic clauses | `real_lipschitz` (RealFlow:59) | PASS | Exact signature L420–428. Proves derivative bound, displacement and integer equivariance for every t in [-1,1]. |
| stepP:p11a:rl-const | `p11_trig_derivative_bound` (design:2250; absent from KAM) | NOT DELIVERED by this scope | Fourier-to-operator bound is a separate designed signature, not proved in either scoped file. Do not mark this step or the full source lemma closed from C7 alone. |
| C6 consumption / later real-complex identification | no C6 import or application | NOTE | C7 uses general real ODE infrastructure independently. Identification with the complex affine flow is a later consumer obligation. |

## Hypothesis and signature fidelity

The source is blueprint-P/parts/p11a2-cutoff-step.tex:229–241, with explicit bridge contracts in design:1345–1371 and signatures:403–428. `P11Vec n` unfolds literally to `Fin n → ℝ` (WeakMeasure/Basic:24); the inherited Pi norm is the max norm and the continuous-linear-map norm is its induced operator norm. No norm instance is replaced. Fields are real from the outset, so no unproved reality transfer is used.

The generic theorem applies to every bounded C2 periodic real field, a generalization of the blueprint's real trigonometric-polynomial setting. M and L are arbitrary nonnegative uniform upper bounds, not existential constants with widened dependence. The source polynomial supplies regularity and boundedness, while its explicit coefficient estimate remains a separate bridge. All explicit/implicit binders are enumerated below. SOURCE includes the independently stated helper's actual solution premises; those helpers do not replace the unconditional existence or variational result.

| Declaration | Binder | Bin | Source / reason |
|---|---|---|---|
| p11_bounded_global_flow | n | TYPING | dimension |
| p11_bounded_global_flow | v | TYPING | real vector field |
| p11_bounded_global_flow | hv | SOURCE | C1 regularity, signature:404 / SG3 |
| p11_bounded_global_flow | M | TYPING | bound parameter |
| p11_bounded_global_flow | hM | SOURCE | nonnegative bound, signature:404 |
| p11_bounded_global_flow | hb | SOURCE | uniform boundedness, signature:404 |
| p11_bounded_global_flow | x | TYPING | initial point |
| p11_global_variational | n | TYPING | dimension |
| p11_global_variational | v | TYPING | real vector field |
| p11_global_variational | hv | SOURCE | C2 regularity, signature:413 |
| p11_global_variational | M | TYPING | field bound parameter |
| p11_global_variational | L | TYPING | derivative bound parameter |
| p11_global_variational | hM | SOURCE | nonnegative field bound, signature:413 |
| p11_global_variational | hL | SOURCE | nonnegative derivative bound, signature:413 |
| p11_global_variational | hb | SOURCE | field boundedness, signature:414 |
| p11_global_variational | hD | SOURCE | derivative boundedness, signature:414 |
| real_lipschitz | n | TYPING | dimension |
| real_lipschitz | v | TYPING | real vector field |
| real_lipschitz | hv | SOURCE | C2 regularity, signature:421 |
| real_lipschitz | M | TYPING | field bound parameter |
| real_lipschitz | L | TYPING | derivative bound parameter |
| real_lipschitz | hM | SOURCE | nonnegative field bound, signature:421 |
| real_lipschitz | hL | SOURCE | nonnegative derivative bound, signature:421 |
| real_lipschitz | hb | SOURCE | field boundedness, signature:422 |
| real_lipschitz | hD | SOURCE | derivative boundedness, signature:422 |
| real_lipschitz | hp | SOURCE | integer periodicity, signature:423 |
| p11_norm_sub_le_of_sol | n, v, M, u, a, b (each) | TYPING | dimension, field, bound, trajectory and endpoints |
| p11_norm_sub_le_of_sol | hb | SOURCE | uniform speed bound, blueprint:237 |
| p11_norm_sub_le_of_sol | hu | SOURCE | ODE on the interval under consideration, blueprint:237 |
| p11RealFlow_spec | n, v, M, x (each) | TYPING | same real-flow input data |
| p11RealFlow_spec | hv | SOURCE | C1 bridge regularity, signature:404 |
| p11RealFlow_spec | hM | SOURCE | nonnegative bound, signature:404 |
| p11RealFlow_spec | hb | SOURCE | bounded field, signature:404 |
| p11RealFlow_eq | n, v, M, x, u, t (each) | TYPING | same data plus competing trajectory and evaluation time |
| p11RealFlow_eq | hv | SOURCE | uniqueness regularity, blueprint:237 / SG3 |
| p11RealFlow_eq | hM | SOURCE | nonnegative bound, signature:404 |
| p11RealFlow_eq | hb | SOURCE | bounded field, signature:404 |
| p11RealFlow_eq | hu0 | SOURCE | competitor through the same point, blueprint:237 |
| p11RealFlow_eq | hu | SOURCE | competitor solves the ODE, blueprint:237 |
| p11RealFlow | n, v, t, x (each) | TYPING | literal total definition, signature:408 |

Counts for the six public theorems: SOURCE 24, TYPING 28, STANDING 0, RULED 0, EXCESS 0. The definition has four further TYPING binders. The all-time t/x quantifiers, interval membership and integer k in the conclusions retain their original scope. No new typeclass, assumption structure or conclusion-shaped hypothesis is introduced. The variational proof needs only C1 regularity and field boundedness; keeping the prescribed stronger C2/hL/hD interface is harmless and matches the signature exactly.

## Definition classification

Only one new definition exists: `p11RealFlow`. No new abbrev or structure occurs. It is a **literal, deliberately totalized selector** in the supplied design, rather than an unconditional definition of a unique flow for every arbitrary function v.

- BODY_MATCH: OK. Exact signature body: choose a global solution if one exists; otherwise return x.
- PUBLIC_CARRIER: OK relative to that literal totalized contract. Arbitrary v is admitted, with no claim that all such v generate flows.
- WELL_DEFINEDNESS: OK on the C1 bounded-field locus, by the proved `p11_bounded_global_flow`; the literal expression itself is total everywhere.
- CHARACTERIZATION: OK on that locus, by `p11RealFlow_spec` (initial value and actual ODE at every time).
- CHOICE_INDEPENDENCE: OK on that locus, by `p11RealFlow_eq` and function extensionality. No uniqueness is claimed for arbitrary irregular v.
- DEFINITION_VERDICT: PASS for the requested exact literal definition and its guarded consumers.

The fallback cannot establish any audited theorem: `p11RealFlow_spec` first proves existence and rewrites to the chosen solution, and both variational and Lipschitz proofs consume this specification. This preserves design audit 1's N3 guard and audits 2–3's retained requirement. The supplied exact definition is not silently replaced by a stronger globally characterized object.

## Proof reconstruction and limitations

For a finite forward endpoint T>0, `p11_maximal_top` bounds every point at 0≤t<T by M t≤M T using the actual maximal solution on the whole closed interval from 0 to t. The closed ball is compact in the finite-dimensional Pi space and contained in univ. `gen_continuation_compact` forces the endpoint to be infinite. Negation supplies the backward endpoint. Thus SG3 is genuinely discharged at this generic level.

For SG4, the selected flow is proved to be a family of maximal solutions on (-∞,+∞), using uniqueness for every competing interval. `FlowChain.reg_all` receives this proved family, an open full domain and C1 field regularity. Its `RegOn` conclusion supplies a HasFDerivAt for the actual initial-data map and HasDerivAt for its actual fderiv, not an unrelated linear-ODE solution. At time zero the map equals id pointwise, giving the identity derivative.

Gronwall controls W=Y−id using ‖A Y‖≤L‖Y‖≤L(‖W‖+1); the identity norm bound is ≤1, also valid for n=0. The L=0 branch avoids division by zero. For negative times the proof differentiates Y(-s) and uses coefficient -A(-s); its norm bound stays L. Equivariance comes from translating a genuine solution by an integer vector and applying global uniqueness. No complex continuation or strip argument enters these real estimates.

Two integration notes remain:

1. Design:718 lists “C6; nonlinear continuation and variational bridges, Gronwall”. Actual C7 imports neither C6 module and calls no C6 declaration. This is a safe independent route for the exact real-field signatures, but it does not certify the requested “C6 consumed as designed” subcheck. In particular, blueprint:287's “the real flow ... is the restriction of Θ_b (uniqueness)” is not proved here. Retain that obligation at the real canonical-step consumer.
2. RealFlow:15–16 associates this module with rl-const, while blueprint:241 explicitly proves “the i-th row sum ... ≤ ... 2π ...”. C7 only accepts hD. The separately specified `p11_trig_derivative_bound` is absent from KAM in this snapshot. This is an attribution/completeness note, not a false C7 theorem or an added premise relative to its exact contract. Do not use this audit to close the coefficient-constant source step.

No new suspected mathematical erratum in the pinned source was found. SG3 and SG4 are previously recorded proof gaps, now supplied at the generic real-field level. No frozen statement defect, unreported mathematical deviation or counterexample was found. Lack of a docstring on p11RealFlow follows the literal signature and is cosmetic.

## Mechanical verification

All audit-owned Lean/Lake calls are serial, use `LEAN_NUM_THREADS=1` and `nice -n 5` (the compile wrapper supplies nice for its build). No clean, update, cache fetch, full-library build or state-changing git was run.

### Targeted build

```
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac7 KAM.Planetary.MaximalStep.RealFlow
```

Exit 0. Output includes:

```
[inp-gate] slot 2 acquired 14:05:51 for KAM.Planetary.MaximalStep.RealFlow
Build completed successfully (9062 jobs).
```

Lake replayed pre-existing warnings in PicardFamilies (unused section variables at 60, 82, 203, 208; haveI style at 268) and LocalDependence (unused section variables at 45, 186; variable p at 99). No warning from either scoped module. This was an incremental targeted build against the shared snapshot, not 9062 fresh recompilations.

### Exact-type/body and axiom probe

```
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC7Audit.lean
```

Exit 0. The probe copied the three exact signature theorem headers under fresh names and supplied `by exact p11_bounded_global_flow hv hM hb x`, `by exact p11_global_variational hv hM hL hb hD`, and `by exact real_lipschitz hv hM hL hb hD hp`, respectively. It copied the literal definition under a fresh name and checked `example : @audit_p11RealFlow = @p11RealFlow := rfl`. No sorry-bearing signature module was imported. The headers and definition were also text-compared independently; all four comparisons returned True.

Exact `#print axioms` output:

```
'KAM.Planetary.p11_norm_sub_le_of_sol' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_bounded_global_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RealFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RealFlow_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RealFlow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_global_variational' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.GlobalRealFlow KAM.Planetary.MaximalStep.RealFlow
```

Exit 0. Complete output:

```
replaying KAM.Planetary.MaximalStep.RealFlow
replaying KAM.Planetary.MaximalStep.GlobalRealFlow
```

### Lint and source hygiene

```
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, with complete output:

```
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (704 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is exactly the generated-root exception permitted by the audit brief. KAM.lean was not regenerated or edited. No other lint failure occurred. The ABI phase ran only after the build, exact-type probe and kernel replay completed.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has empty output. `git diff --check` exits 0. Searches find none of sorry/admit/axiom/unsafe/opaque/EuclideanSpace or resource overrides in the scoped files. Both files have the required copyright, module command, public imports, module docstring and exposed public noncomputable section; lengths are below 1500. Each of the seven new public names has exactly one declaration site across KAM. Project import-closure scan: 16 modules, zero Frozen modules, zero Provider modules. No draft anchor is consumed transitively.

Final scope: six public theorems and the exact totalized flow definition are accepted. No frozen theorem, full coefficient-constant step or downstream complex-flow attachment is promoted by this receipt.

Closeout: disposable probe deleted; final `git diff --check` and whitespace check of this untracked report passed. Final git status contains only this new report and the pre-existing untracked handoff. No source or other tracked file was changed by the auditor.
