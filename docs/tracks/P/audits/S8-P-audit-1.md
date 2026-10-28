# S8-P independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped package. All four designated design exports and the CSlow adapter pass statement and proof review. There is no frozen theorem anchor or provider export in S8-P, so frozen-type/seal-body tests are not applicable and no anchor is declared seal-ready by this report.

Audited worktree `/root/code/KAM-inp-s8p`, HEAD `8ed5fd213eb126a1b74cfadb8bcb2a6764b4a5fd`; comparison ref `inp` was `5991245cabc06e69ec900cb6006b45f72cc85eb0`. Scope is **only** `KAM/Planetary/SecularForm/ParameterIntegral.lean`, per the handoff's AUDIT FOCUS. Report destination follows the user's explicit absolute path, overriding the generic brief's main-worktree destination.

Read AGENTS.md, PLAN.md, DECISIONS.md, the assigned package brief, handoff, P810 design (S8-P row, proof boundary and signatures), both P810 design audits, the current original signatures at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, the relevant P8 blueprint statements, track P statement conventions, SecularForm.Basic and the literal frozen secularAverage definition. No production source was edited.

## Declaration inventory and fidelity

All names below have prefix `KAM.Planetary.SecularForm`; line numbers refer to ParameterIntegral.lean.

| Node / role | Lean declaration | Verdict | Reason |
|---|---|---|---|
| Compact angle-cell infrastructure | `isCompact_cell`, L29 | PASS | Finite product of closed bounded intervals; includes n=0. |
| Cell measurability | `measurableSet_cell`, L32 | PASS | Literal product cell is measurable. |
| Real dominated differentiation helper | `hasFDerivAt_cell_integral`, L36 | PASS | Open real parameter domain; joint continuity of integrand and derivative, pointwise differentiability; Banach target. These are explicit calculus premises, not assumed integral conclusions. |
| Complex derivative measurability helper | `aestronglyMeasurable_fderiv_cell`, L74 | PASS | Obtains directional derivatives as measurable difference-quotient limits and reconstructs the actual continuous linear map from the finite basis. |
| Uniform Cauchy estimate helper | `norm_fderiv_le_cell`, L139 | PASS | Actual complex Fréchet derivative bounded by M/r on ball(x,r), from holomorphy and a bound on closedBall(x,2r). Source positivity and domain guards are explicit. |
| `bpP:p8:e-param` | `e_param`, L184 | PASS | Exact design telescope: open U, joint continuity on cell × U, holomorphy in the parameter for each angle. No added premise. |
| `bpP:p8:e-diff` | `e_diff`, L219 | PASS | Exact revised finite-order telescope, natural k, continuity only through k, ContDiffOn at k. Literal equality of iterated derivatives of the integral and integral of derivatives. |
| Carrier adapter definition | `cslowEquiv`, L267 | PASS | Genuine continuous complex-linear equivalence of the three Pi factors with the corresponding concatenated Pi space. |
| S8-P carrier obligation | `e_param_cslow`, L279 | PASS | Same integral theorem on the actual CSlow carrier, with independent angle dimension m. Transport through the equivalence preserves the integral and open domain. |
| Published external G1 / `bpP:p12:f-unif` | `compact_uniform`, L295 | PASS | Exact generic compact-uniform-continuity signature; direct Mathlib application. Consumer still supplies its compact set and continuity. |
| Published external G2 / `K:bp:p1:ext-integral` | `periodic_derivative_integral`, L301 | PASS | Exact signature, C1 map into Fin 2 → ℝ and period 2π; FTC gives q(2π)-q(0)=0. |

The four designated signatures are identical to the original design signatures after whitespace normalization. An independent Lean probe copied each design statement to a fresh theorem and proved it by the implementation using all explicit arguments in order. It also checked `example : type_of% @audit_NAME := @NAME` for all four. All elaborated at default resource settings.

The finite-order `e_diff` resolves the old design-audit F1: no analytic/all-orders premise remains. For each j≤k, apply this theorem at order j and restrict the hypotheses by regularity monotonicity. Evaluating the derivative tensors yields the partial-derivative identities; multiplication by the fixed `(2π)^(-n)` yields normalized averages. The theorem proves the raw integral equality deliberately specified by the design. It does not export translation invariance (`average_translate` belongs to another package) or claim the entire multi-part external blueprint paragraph closed.

## Proof review and definitions

`hasFDerivAt_cell_integral` chooses a closed parameter ball inside U and bounds the jointly continuous derivative on its product with the compact angle cell. Finite restricted volume makes the constant bound integrable. Joint continuity supplies integrability at the base point and measurability, and openness upgrades within-domain differentiability to derivatives on the whole local ball. All hypotheses of Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le` are discharged explicitly.

For `e_param`, the uniform bound on the integrand comes from the compact cell × closedBall(x,2r). Each complex direction v is reduced to a one-variable disc of radius r/‖v‖; the triangle inequality keeps that disc inside the bounded parameter ball. Cauchy's derivative estimate gives M/r in operator norm, including a separate v=0 case. The measurable derivative is established independently by nonzero real increments tending to zero inside U, then a finite basis expansion. Thus derivative measurability and domination are proved, not hidden in a holomorphy premise.

For `e_diff`, the zero-order case uses the genuine order-zero multilinear equivalence. Induction differentiates the integral of the j-th derivative, using only j+1≤k and joint continuity through k. Equality on a neighborhood in open U transfers the derivative of the integral, and the curry-left isometry commutes with integration. This avoids arbitrary outside-U values of fderiv and iterated derivatives; all derivative identifications are at interior points. There is no dependence on Bochner integral fallback values for nonintegrable functions: compactness and continuity supply the integrability used in differentiation.

**Definition classification:** the sole new definition is `cslowEquiv` (L267–276), exposed by `@[expose] public noncomputable section`. It is the inverse of the explicit finite-index splitting linear equivalence, upgraded by finite-dimensional continuity. Its body represents the intended object on its entire carrier, including dimension zero. It has no junk branch, fallback, choice of a different secular object, new bundled assumption, abbrev, structure or instance. Local `let` objects in the proofs are auxiliary constructions only. Ambient coordinates remain Fin-indexed functions and their products, with their ordinary Pi/product norms; no EuclideanSpace or substituted physical metric appears.

## Independent checks

All Lean/Lake invocations controlled by this auditor were sequential and used `LEAN_NUM_THREADS=1` and `nice -n 5`. The prescribed build gate itself applies nice to lake build. No resource overrides, library-wide rebuild, cache mutation or generated-root regeneration was requested.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8p KAM.Planetary.SecularForm.ParameterIntegral
```

Exit **0**. Output begins `[inp-gate] slot 2 acquired 09:43:04 for KAM.Planetary.SecularForm.ParameterIntegral` and ends `Build completed successfully (9110 jobs).` Replayed unused-variable warnings occur in existing KAM.Kepler.Energy, KAM.Planetary.Poincare.Chart and KAM.Kepler.Mass; none comes from the audited module.

### Signature probes and all public declaration axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8PAudit.lean
```

Exit **0**, all eight signature/application checks accepted. The probe issued `#print axioms` for every new theorem and additionally the definition; the exact output was:

```text
'KAM.Planetary.SecularForm.isCompact_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.measurableSet_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.hasFDerivAt_cell_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.aestronglyMeasurable_fderiv_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.norm_fderiv_le_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.e_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.e_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.cslowEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.e_param_cslow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.compact_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.periodic_derivative_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.ParameterIntegral
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.SecularForm.ParameterIntegral
```

This single replay invocation covers the entire audited module, including all helpers and the definition.

### Source lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted stale generated-root failure. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (521 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden-token, size, 100-character-line, errata-rendering or other lint failure was reported. The generated root was preserved.

### Static/import and comparison checks

- 311 lines; zero lines exceeding 100 Unicode characters; copyright/license/authors header, `module`, two `public import`s, module docstring and exposed public section present.
- No sorry/admit/axiom/unsafe/opaque declaration or token, resource override or EuclideanSpace occurrence in the audited module.
- Direct imports are Mathlib and SecularForm.Basic. A recursive scan of the 64 KAM modules in its project import closure found **no provider and no frozen theorem module**; the 47 frozen modules in that closure are definitions. No DRAFT_SORRY theorem can enter through this project import chain. The axiom checks independently found no sorryAx.
- `git diff inp...HEAD -- KAM/Frozen manifest README.md`: empty (exit 0), aside from Git's multiple-merge-base warning.
- `git diff --check add04da..HEAD`: empty (exit 0). All three S8-P commits, `9922efa`, `bd2b1a8`, `8ed5fd2`, touch only the audited module.

## Notes, discrepancies and limits

1. The required literal `git diff inp...HEAD` warns `multiple merge bases, using 6f2cb1ec6284a98aaffeed74340762f20f4afc04`. The other merge base is `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`. The selected comparison shows 22 changed files, including unrelated inherited packages and **12 added imports in KAM.lean**. Consequently the brief's entire-branch protected-path check is **not empty** for KAM.lean. This is recorded, not silently treated as passing. None of the three S8-P implementation commits modifies KAM.lean; their combined diff after `add04da` consists solely of this 311-line module. The explicit focus excludes auditing the inherited packages, and no generated file was edited by this auditor.
2. The whole comparison's `git diff --check inp...HEAD` also reports an inherited trailing space in `docs/tracks/P/audits/P23-12-handoff.md:28` (the line ending “source Case B).”). The scoped S8-P commit range passes whitespace checking. This is not an S8-P proof or source defect.
3. The expected stale generated root is reported under lint rather than repaired. This report approves the scoped infrastructure; it does not close a frozen planetary anchor, later secular analyticity/momentum consumers, torsion, or the full blueprint external-fact paragraph.

**Suspected source/blueprint defects:** none found in the scoped statements or proofs. No new mathematical deviation or extra owner ruling is needed. The discrepancy notes above concern inherited comparison contents and the permitted generated-root state, not a suspected defect in a pinned source.

Scratch probe `.lake/abi-scratch/S8PAudit.lean` and the temporary kernel log were deleted after their successful checks. Final `git diff --exit-code` is empty; status contains only this new report and the pre-existing untracked S8-P handoff. The report has no trailing whitespace or pending-check placeholders. No state-changing git command was used.
