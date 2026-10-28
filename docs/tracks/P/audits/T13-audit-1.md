# T13 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the T13 helper package. All required checks completed; lint has only the expressly permitted generated-root exception. No frozen anchor is assigned to T13; “seal-ready” is therefore not applicable. This audit does not close P-G, P-PLANAR, P-FIXED, T6's separate graph slice, or downstream Birkhoff/asymptotic packages.

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-t13`. HEAD: `a73d2767362222d4a6d0610ce6bf6be553301a4e`; comparison `inp`: `72139c7754e00f38e88c675b5327866250e6678e`. Authority: user instructions and AUDIT FOCUS, AGENTS.md, PLAN, DECISIONS, the package audit brief, T13 handoff, P11C design/node table and design audit, current standalone signatures, track-P statement, and blueprint Part 11b. The user's exact worktree report path overrides the brief's generic main-worktree destination.

Only `KAM/Planetary/PlanarTorsion/Beta.lean` is audited. The full three-dot comparison contains eight new Lean files (1,397 lines): Beta plus seven inherited T6 Quartic files. No other Beta module exists. T6 is dependency context, not a second audited package. The untracked T13 handoff was already present. Only this report is a lasting edit; scratch probes are removed after use; no git state-changing command was run.

## Findings and scope notes

No material T13 defect was found. The notes are:

1. The generated root is stale, the explicit lint exception allowed by this brief. It is left unchanged.
2. `beta_formula` retains the SIGNED unit-circle hypothesis exactly, although its proof is polynomial and does not use it. The unused-variable warning at Beta:252:48 is benign. There is no added premise or weakened conclusion.
3. Beta imports Frame (T14) for already proved spectral analyticity and the concrete rotation, in addition to the design row's T6/T7/T12 prerequisites. This is an actual extra acyclic implementation dependency, not an assumed frame theorem. Frame does not import Beta. The design audit's earlier DAG note is consistent with treating the dispatch DAG as implementation guidance rather than a proof certificate.
4. T13 does **not** need T6's append-only `qe-c12` repair. At Beta:85 it consumes only `(quartic_explicit p hp).1`, the analyticity of the six coefficient functions. The averaged identity is proved for arbitrary `c : Fin 6 → ℝ`. The physical fourth-jet attachment and radial diagonal comparisons are separate T6 obligations. The original T6 audit's F1 records missing comparison with Part 8, not a counterexample to the coefficient values; its later `Quartic/Diagonal.lean` repair is outside this checkout and outside this audit. No T6 graph-completion claim is inferred here.

## Node and declaration review

Names below belong to `KAM.Planetary`; line numbers refer to Beta. The node table in P11C design:126–129 assigns exactly four graph records to T13. All four are established, including both proof fragments. There is no unsigned export impersonating a graph node with a narrower conclusion.

| Node / role | Declaration and location | Verdict | Evidence |
|---|---|---|---|
| `bpP:p11b:beta-def` | `beta_def` :34 | PASS | Exact signed polynomial body, factors 8 diagonal / 4 off diagonal. |
| `bpP:p11b:beta-def` | `p11c_beta` :42 | PASS | Exact signed physical coefficient/projector adapter. |
| `bpP:p11b:beta-def` | `beta_properties` :79 | PASS | Exact signed entrywise `AnalyticOnNhd` on the whole axis cone and symmetry at every axis vector. |
| `bpP:p11b:beta-formula` | `beta_formula` :252 | PASS | Exact signed type including all binder order, unit-circle premise, matrices, real torus average, factor 1/2 and frozen oscillator actions. |
| `stepP:p11b:bf-gram` | `p11cBetaGram` :174; `p11c_quartic_rotateSlow_gram` :181; `p11cBetaGram_quad` :191 | PASS | Literal A1/A2/cross-dot Gram polynomial and degree ≤2 in G established by ring identities; no normalization premise needed. |
| `stepP:p11b:bf-avg` | `p11cGramRot_integral` :214; `p11cGramRot_sq_integral` :229; final proof :258–283 | PASS | Raw integrals 0 and `2π² r0 r1`, divided by `(2π)²`; yields normalized means 0 and `r0 r1/2`, then exact coefficient collection. |
| Symmetry helper | `beta_def_isSymm` :47 | PASS | Stronger all-matrix statement; no projector assumptions. |
| Spectral regularity helper | `p11c_projector_analyticAt` :53 | PASS | Source validity and cone membership only; second eigenvalue via trace, denominator nonzero via strict spectral gap. |
| Product integration helper | `p11c_boxIntegral_prod` :94 | PASS | Actual Pi Lebesgue box factorization; unrestricted version justified by Mathlib's total Bochner-integral product theorem. |
| Integrability helper | `p11c_boxIntegrableOn` :107 | PASS | Continuity implies integrability on compact box; supplies all additive-integral side conditions in averaging proof. |
| Average adapter | `p11c_average_eq_boxIntegral` :160 | PASS | Unfolds the existing zero character, real/complex integral and exact `(2π)⁻²` normalization. |
| Gram variable definition | `p11cGramRot` :200 | PASS | Actual rotated real dot product, all phases and angles. |
| Rotation helper | `p11c_rotation_sq` :204 | PASS | Each squared radius invariant for all angles/phases; trigonometric identity. |
| Continuity helper | `p11cGramRot_continuous` :209 | PASS | Literal trigonometric-polynomial continuity. |

The five private one-variable lemmas `int_a`, `int_b`, `int_aa`, `int_bb`, `int_ab` (:111,117,123,135,147) prove zero first moments, the two `π(x²+y²)` second moments, and zero mixed moment. These are actual integrals, not bundled averaging assumptions.

## Definition classification and consumer fidelity

There are four new definitions and no new structure, abbreviation, instance or hidden proof-premise field:

- `beta_def`: total polynomial in six coefficients and three projector entries. On arbitrary matrices it intentionally gives the same symmetric polynomial matrix; no singular fallback or fabricated projector is involved.
- `p11c_beta`: exact composition with the established physical six coefficients and spectral projector. Outside the axis cone it inherits their existing total extensions; no regularity or physical averaging theorem relies on those extensions. Symmetry is algebraic everywhere.
- `p11cBetaGram`: total explicit polynomial in A1, A2 and B, exactly the rotated quartic for every real γ,s and phase.
- `p11cGramRot`: total actual cross-dot variable after the existing torus rotation. No default, choice or branch.

SIGNED declarations checked against `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`: `beta_def` (:526), `p11c_beta` (:533), `beta_formula` (:539), `beta_properties` (:737). The first two pass Lean `rfl` body-equality probes against fresh copies of the signed definitions; both theorem types pass `type_of%` probes and fresh copied declarations with bodies applying exactly `beta_formula c g s h z` and `beta_properties p hp`. A separate textual comparison also returns `True` for both theorem headers and both complete definition bodies modulo whitespace. No frozen seal-body probe applies to this helper-only package. `p11c_rotateSlow` is already owned by Frame:34 and is not redefined.

The signed generic SO(2) formula is sufficient for the blueprint's physical diagonalizing frame: upstream `p11c_projector_eq_frame` (SpectralAdapter:442) identifies the physical projector with the first-column outer product for a sorted diagonalizing SO frame; Frame supplies such a frame. Writing its columns as `(g,s),(-s,g)` recovers precisely the signed matrices. No stronger spectral hypothesis or special frame choice is required by the polynomial formula. The definition depends only on the projector, hence is frame-sign independent, has no coupling-parameter input, and uses the same six coefficients for both physical models through T6's two fourth-jet equalities. These are definitional/upstream attachments, not missing local analytic assumptions.

Consumers retain the required surface: T16 gets the exact averaged action polynomial; T17 gets continuity from entrywise analyticity; T18 gets literal coefficient/projector formulas and 8/4 normalization; T20/Part 12 get symmetry and axis-cone analyticity. Their own physical Birkhoff, determinant and asymptotic proofs remain separate tasks. No conclusion-shaped hypothesis occurs in any new public result.

## Independent validation

All Lean/Lake invocations initiated by this audit are serialized and use `LEAN_NUM_THREADS=1` with `nice -n 5` (the compile-gate script supplies nice for its build). No library clean, cache fetch, update, root regeneration, frozen/manifest edit or production repair was performed.

1. Targeted gate command:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t13 KAM.Planetary.PlanarTorsion.Beta
   ```

   Exit 0. Output: `[inp-gate] slot 1 acquired 22:44:42 for KAM.Planetary.PlanarTorsion.Beta`; `Build completed successfully (9249 jobs).` Beta warning: unused `h` at :252:48. The build also replays dependency unused-variable/deprecation warnings; no T13 elaboration or heartbeat failure.

2. Exact-type/body and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T13Audit.lean
   ```

   Exit 0; no signature/body probe errors. Each of all 13 new public theorems prints exactly `[propext, Classical.choice, Quot.sound]`: `beta_def_isSymm`, `p11c_projector_analyticAt`, `beta_properties`, `p11c_boxIntegral_prod`, `p11c_boxIntegrableOn`, `p11c_average_eq_boxIntegral`, `p11c_quartic_rotateSlow_gram`, `p11cBetaGram_quad`, `p11c_rotation_sq`, `p11cGramRot_continuous`, `p11cGramRot_integral`, `p11cGramRot_sq_integral`, `beta_formula`. No `sorryAx` or other axiom.

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Beta
   ```

   Exit 0. Exact output: `replaying KAM.Planetary.PlanarTorsion.Beta`. This single invocation covers the sole in-scope lemma module; there is no provider module in T13.

4. Full source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 **only for the allowed stale generated root**. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1057 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint finding. The root was not regenerated.

5. Source and repository checks: Beta is 287 lines, maximum Unicode line width 98; required copyright/module/public imports/docstring/exposed public section present. Forbidden-token/resource-override scan has no matches. All 17 new public declaration short names were searched against every other KAM Lean source: no reuse; all are inside `KAM.Planetary`, and private `int_*` names do not create root shadows. Recursive local imports cover 203 modules and 58 frozen definition files, with **zero provider imports and zero frozen theorem imports**; therefore no `DRAFT_SORRY` dependency or imported theorem-state exception arises.

   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. `git diff --check inp...HEAD`: exit 0, no output. Final `git diff --check` exits 0. All three audit-created scratch files (`T13Audit.lean`, `T13-kernel.log`, `T13-lint.log`) were deleted. Final `git status --short` lists only the new report and the pre-existing untracked T13 handoff. No tracked file changed.

Input SHA-256:

- Beta: `d9ffb40182a969d846d7842b0ae998816b92ddb3c7d8faba110a491774a89515`.
- P11C design: `8693b4c33b78a6d52c251999b15e08fc68d588b9250e2e4bbe3e64b4510a6437`.
- Current standalone signatures: `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`.

## Suspected defects, deviations and uncertainties

No new suspected pinned-source defect or mathematical blueprint contradiction was found. The proof does not use a pinned paper theorem directly; blueprint Part 11b:184–203 and the approved design/signature surface are the mathematical comparison authority. No new external source verification is claimed. The source's unit-circle assumption is redundant in this polynomial identity, not false. The broader T6 `qe-c12` completeness finding remains outside T13's ownership; it was not silently repaired or treated as proved by compilation. The sole implementation dependency addition is Frame described above. No signature deviation or source edit was introduced.
