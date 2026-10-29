# SO-HAMX independent audit 1

Verdict: **PASS WITH NOTES** for the assigned SO-HAMX helper package. All three signed declarations match exactly, all four public theorems have acceptable axioms, and independent elaboration and kernel replay pass. The notes are the permitted stale generated-root lint exception, an inherited dependency warning, and the explicitly retained original-frame scope. There is no frozen theorem anchor or provider to seal in this package.

## Scope and authority

- Report destination: `/root/code/KAM-inp-sohamx/docs/tracks/SO/audits/SO-HAMX-audit-1.md`, following the user's explicit worktree destination over the generic brief's main-worktree destination.
- Audited HEAD: `dcdd492d8e41df5ea69db48b74f498f17b765861`.
- Observed `inp`: `6cad95806f4dbeafc1933f733daf875fdb3b097a`; merge base: `0d5b57af7d12326977f66e187b08fe0c03106d0e`.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/SO/audits/SO-HAMX-handoff.md` including AUDIT FOCUS.
- Controlling signatures: `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:1368–1384`, namespace `KAM.SpinOrbit`, section I. Inspected SHA-256: `95a45623f1cd75be9e406f32f2da407035b6663a7a8e98658541fbe4ff38a887`.
- Design: `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md:334–336`, dependency row at 419, package row at 452, and declaration block at 1957–1969. Inspected SHA-256: `19a463bd3e5d1307a7a3da8db2ea053f3bbed9ee8574a3fefc239b1703288f17`.
- Read `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`, including O5. The handoff explicitly requires these original-frame declarations despite the later rotated-frame client. No track-SO statement file exists in this checkout; the named SO signatures/design govern this helper slice. Unrelated I/N/P anchors and blueprint nodes are outside the explicit audit focus.
- Read the expression evaluator, phase basis, landed Hamiltonian and model interfaces, and relevant frozen complex-field/strip conventions. The full `git diff inp...HEAD` is exactly the addition of `KAM/SpinOrbit/HamExpr.lean` (79 lines); no inherited implementation diff needs separate attribution.
- Audited module SHA-256: `99536c0913f7d6f3b357231e908c14c60ef656ba26eb311ce19e2570b99b56bd`.

## Declaration results

All locations below are in `KAM/SpinOrbit/HamExpr.lean`; all names have prefix `KAM.SpinOrbit.`.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Signed expression, design §6 / Appendix I | `soHamExpr`, line 28 | PASS | Full declaration body is text-identical to the signature; independent copied definition is definitionally equal by `rfl`. |
| Public fold helper | `soHamExpr_eval_foldr`, line 35 | PASS | Exact evaluation for every finite list, including empty lists, repetitions, and arbitrary natural indices; list induction proves the assertion without extra analytic premises. |
| Public sum helper | `soHamExpr_list_sum_range`, line 50 | PASS | Valid for every additive commutative monoid and every natural range, including zero; ordinary typing structure, no conclusion-shaped premise. General supporting fact, not a substitute for a signed result. |
| Signed evaluation bridge | `soHamExpr_eval`, line 56 | PASS | Header text-identical, fully qualified elaborated theorem checks at the copied signed type; equality on the entire complex phase space, with no restriction or added premise. |
| Signed clock derivative | `soHamExpr_clock`, line 71 | PASS | Header text-identical, fully qualified elaborated theorem checks at the copied signed type; derivative is 1 at every complex point in the correct action direction. |

The assigned slice is complete: exactly one signed expression definition and both signed theorems are implemented. The two additional theorems are supporting helpers. There are no frozen-anchor/provider type comparisons or seal bodies applicable to this package; signature/body probes supply the relevant interface checks.

## Definition classification and proof scrutiny

`soHamExpr` is the only new definition; there are no abbreviations, structures, instances, bundled hypotheses, or fallback branches. It is the intended finite Hamiltonian expression on its whole carrier: action 1 is `J`, action 0 is `p`, the rational kinetic coefficient is `1/2`, and range indices `0,…,6` produce precisely modes `1,…,7` with coefficients `-soEpsQ * soAQ (m+1)` and keys `[2, -(m+1)]`. Each key has exactly two entries; `certKeyFun`'s default value is never used for `Fin 2`. The expression contains no division constructor. Definitions are exposed by `@[expose] public noncomputable section`.

At lines 35–48 the fold lemma proves the phase `2π(2q-(m+1)φ)` directly from `modePhase`, `certKeyFun` and the two-coordinate finite sum. The range-sum conversion (50–54) preserves every summand. At lines 57–66 the kernel-checked `decide` equality identifies `Icc 1 7` with the image of `range 7` under addition by one; the image map's injectivity is proved. Rational-to-real-to-complex casts are reconciled using the landed `soA_eq_ratCast` and `soEps_eq_ratCast`. Ring normalization then proves the exact potential, including its negative sign and period-one factor. There is no numerical approximation or truncation of an infinite series.

At lines 73–75 pointwise evaluation equality gives equality of functions. The landed unconditional `fderiv_soHC_apply` evaluates the differential on `phaseBasis (.inr 1) = (0, Pi.single 1 1)`. This leaves the `J` coefficient 1 and kills all other terms. This is the complex Frechet derivative, not a formal expression derivative or an unsupported claim about a possibly nondifferentiable function.

No theorem assumes its conclusion, an unproved identity, a native computation result, or a hard analytic step. No carrier, constant dependence, premise, or conclusion differs from the signed declarations.

## Independent checks and output

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build used the required gate. Lint was run only after the explicit Lean/kernel jobs completed because its ABI stage can invoke Lean. No clean, update, cache fetch, generated-root regeneration, or state-changing git command was used.

### Targeted build

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sohamx KAM.SpinOrbit.HamExpr
[inp-gate] slot 1 acquired 14:26:24 for KAM.SpinOrbit.HamExpr
⚠ [2896/2911] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:85:5: Variable name `hS` is not explicitly referenced.
Build completed successfully (2911 jobs).
exit 0
```

The remaining warning text suggests renaming/removing the unused binding or disabling its linter. No such change or linter override was made. There were no warnings in the audited module.

### Signature/body and axiom probe

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOHamxAudit.lean
exit 0
```

The probe imported `KAM.SpinOrbit.HamExpr`, copied the exact signed expression body under `SOHamxAudit.signedSoHamExpr`, and proved equality with `KAM.SpinOrbit.soHamExpr` by `rfl`. It checked the copied signed types with `@KAM.SpinOrbit.soHamExpr_eval` and `@KAM.SpinOrbit.soHamExpr_clock`, printed their declarations, and ran:

```lean
#print axioms KAM.SpinOrbit.soHamExpr_eval_foldr
#print axioms KAM.SpinOrbit.soHamExpr_list_sum_range
#print axioms KAM.SpinOrbit.soHamExpr_eval
#print axioms KAM.SpinOrbit.soHamExpr_clock
```

Exact axiom output:

```text
'KAM.SpinOrbit.soHamExpr_eval_foldr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soHamExpr_list_sum_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soHamExpr_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soHamExpr_clock' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An independent Python text comparison returned `True` for the entire signed definition and each signed theorem header, including binders. The surrounding signed namespace is exactly `KAM.SpinOrbit`.

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.HamExpr
replaying KAM.SpinOrbit.HamExpr
exit 0
```

This single invocation replays the only new module, including all four theorem proofs; there are no separate provider or helper modules in scope.

### Lint and static hygiene

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1298 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is exactly the generated-root exception allowed by the audit brief. `KAM.lean` was left untouched. No substantive source lint failure occurred.

Static checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0.
- 79 file lines, maximum 96 Unicode characters per line; both the 1500-line and 100-character limits pass.
- Copyright, `module`, public imports, module docstring and exposed public section are present.
- `rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace|native_decide' KAM/SpinOrbit/HamExpr.lean`: no matches, exit 1 as expected for an empty search.
- `rg -n '\b(soHamExpr|soHamExpr_eval|soHamExpr_clock|soHamExpr_eval_foldr|soHamExpr_list_sum_range)\b' KAM .lake/packages/mathlib/Mathlib`: matches only the audited module. Thus none of the five public short names is reused in the checked KAM/Mathlib sources. Every declaration stays inside `KAM.SpinOrbit`; no root declaration or harmful root shadow is introduced.
- Recursive KAM import inspection: 41 modules including the audited module; no provider import, no frozen theorem import. All 17 reachable frozen modules are definitions with manifest state `SEALED`. No `DRAFT_SORRY` anchor is imported.

## Defects, limits, and handoff

No suspected pinned-source or blueprint defect was found in this slice, and no implementation deviation was introduced. The original-frame wording is intentional under the handoff: the plan's O5 adopts a rotated frame for the future lunar client, while the currently signed declarations describe the original frame. The audited equality and clock theorem remain valid; they do not establish the rotated Hamiltonian or its certificate applicability. That migration belongs to the later client/design work.

This audit establishes the complete signed Hamiltonian-expression slice. It does not close certificate soundness, validate lunar certificate data, establish a barrier/confinement theorem, or seal any I/N/P frozen anchor.

Repository edits by this audit: this report only. The pre-existing untracked `SO-HAMX-handoff.md` was preserved. Audit probe/log files in `.lake/abi-scratch/` are removed before completion; no implementation or protected file was edited.
