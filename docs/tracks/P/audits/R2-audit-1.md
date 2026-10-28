# R2 independent package audit 1

Overall verdict: **FAIL for R2 slice completeness (F1)**. The twelve declarations in the audited module pass the source/type/proof inspection; the failure is the explicitly promised compact-set common-neighbourhood obligation. No frozen anchor or provider is delivered by R2, so no anchor is seal-ready on this audit's authority. The signed `real_analytic_hamiltonian_local_flow` belongs to R3 and remains outside this package's completion claim.

## Scope and evidence

Audit date: 2026-10-28. Audited `KAM/Planetary/PlanarTorsion/RealFlow/Analytic.lean` only, at HEAD `98374b013a7f331da05052b916826e23c2a7a56c`. Read AGENTS.md, PLAN.md, DECISIONS.md, the package-audit brief, R2-handoff.md, P11C design and its independent design audit, the supplied signatures, the relevant Track P statement conventions, blueprint Part 11b, frozen Phase/HamiltonianVectorField, and the ODE solution predicate. Dependency files were inspected for applicability/import provenance, not given independent package verdicts.

The requested full `git diff inp...HEAD` was inspected: five new files, 845 insertions. Besides the four R2 modules, this includes the merged R1 `RealFlow/Local.lean` (89 lines); the handoff's “Local.lean untouched” means untouched by R2's own commits, not absent from the three-dot comparison. `inp` was `00afab9de5797d50e1a1b8123a8101c6fd5f8bbb`. Git warns of multiple merge bases and selects `ec23b835c48802c9afb977ff01f72600b82cca7f`; the other base is `e1a6d79dbc71cb183d0c04add2a0bbc8f2ac0b59`. These facts are recorded rather than silently substituting a different comparison.

SHA-256:

- Analytic.lean: `4b12359786595ba0e43887b162fb70e8dc3bea4baf23eb593f83c8ea14a9be4a`.
- P11C-LEAN-DESIGN.md: `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36`.
- `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`: `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079`.

The user's exact output path overrides the generic brief's main-worktree destination. Only this report is a lasting repository edit; disposable probes are confined to this worktree's `.lake/abi-scratch/`. No production, frozen, manifest, generated-root, or README edit was made.

## F1 — R2's compact common-neighbourhood deliverable is missing

**Severity: material package-completeness finding, not a false local theorem.**

The design's U5 row at line 47 assigns RealFlow.Analytic “local complex extensions, compact common parameter domains, uniform Picard bounds and derivative convergence.” Its R2 row at line 208 says “real analytic parametric Picard convergence on common neighbourhoods.” The proof instruction at line 253 is explicit: “extend each real analytic coefficient locally to a complex neighbourhood, use compactness to obtain a common neighbourhood, and prove analytic Picard convergence there.”

In contrast, Analytic.lean:95–101 and :221–228 quantify `x` before the existential `r,T,Φ`. The proof complexifies at that one `x` (:102), chooses its radii and bounds (:103–109), and constructs a jointly analytic map on that ball. This supplies one time interval common to the initial points **in that ball**. It supplies no compact `K`, no open neighbourhood of all of `K` with a single positive time interval, and no compatibility/gluing proof between choices at different centres. None of the twelve declarations or the internal proof performs a finite compact cover or such gluing. R1's compact theorem supplies solutions and uniform times, not joint analyticity of a single glued map. The handoff correctly discloses the narrower result; disclosure does not itself revise the assigned deliverable.

Consumer assessment:

1. **R3 is supported by the at-a-point result.** Signatures:442–449 ask for a ball about one `x`, not a compact-set flow. Joint analyticity on the open time/initial-data product supplies the derivatives needed to differentiate the solution identity, obtain the variational equation, and apply Hessian symmetry to prove form conservation. The initial-value identity holds for every point of the ball. The missing symplecticity clause is R3's work. The explicit H/x binders in that signed theorem can be retained; the R2 helper's implicit H/x binders do not alter the projected proposition.
2. **T9 can in principle be built from local analytic flow, but the necessary bridges remain unproved here.** For a parameter-dependent field, apply the generic finite-coordinate theorem to the augmented autonomous field `(I,z)' = (0,X_chi(I,z))`, using finite-coordinate identifications. Prove parameter constancy, compare with the chosen/maximal solutions by uniqueness, take a finite cover of a compact parameter neighbourhood times a confining state set, choose a common positive time, and glue the local maps. Continue to time one through finitely many analytic local transitions; identify the selected `p11c_flow` with these solutions. Quartic bounds and continuation are T9's separate tasks (design:255). Separate applications of the Hamiltonian helper at fixed I do not establish analyticity in I, and taking an infimum over arbitrary pointwise positive times does not establish a positive common time.

Thus there is no mathematical obstruction to the proposed downstream route, and no need to change a frozen/signature statement. Nevertheless, under the user's slice-COMPLETE requirement and the unrevised design:47,208,253, compact common-neighbourhood assembly is an unpaid **R2 deliverable**. A possible future proof in T9 is not an existing proof in this slice. Add a proved compact-neighbourhood flow/patching result (generic augmented-state applicability retained), or obtain an explicit design/ownership revision assigning that exact obligation to a named consumer and audit its completed proof. This audit does not silently make that reassignment.

The U5 derivative-convergence instruction is not itself a proof-soundness failure: the implementation uses the stronger holomorphic-uniform-limit theorem directly and differentiates the resulting analytic solution identity. It does not exchange derivatives with a merely real uniform limit. Derivative convergence need not be assumed to use this route.

## Declaration and graph-node coverage

All declaration names below are in `KAM.Planetary`; line numbers are in Analytic.lean.

| Node / responsibility | Declaration | Verdict | Reason |
|---|---|---|---|
| R2 coordinate adapter | `p11cPt` :37 | PASS | Actual real-linear time/state inclusion into complex coordinates. |
| R2 time coordinate | `p11cPt_zero` :45 | PASS | Exact time projection. |
| R2 state coordinates | `p11cPt_succ` :48 | PASS | Exact state projections. |
| R2 state inclusion | `p11cSp_p11cPt` :51 | PASS | Identifies the state block with the existing real inclusion. |
| R2 scaled time | `p11cTimeScale_p11cPt` :54 | PASS | Keeps initial data fixed and scales time by σ. |
| R2 reality | `p11cIsReal_realInclusion` :62 | PASS | Imaginary parts of real data vanish. |
| R2 reality | `p11c_eq_realInclusion` :65 | PASS | Reconstructs a real vector from its real part. |
| R2 integral-to-ODE bridge | `p11c_hasDerivAt_of_integral_eq` :70 | PASS | Continuity and the integral equation are appropriate helper premises, not assumed flow existence. Handles t=0 and negative t; T≤0 makes its conclusion vacuous. |
| R2 generic analytic flow | `p11c_analytic_flow_fin` :95 | PASS locally | Analytic germ and target neighbourhood suffice; produces a jointly analytic solution family, with no complex-extension hypothesis. No compact-uniform conclusion. |
| R2 field analyticity | `p11c_hamField_analyticAt` :206 | PASS | Derivative evaluations give exactly the frozen Hamiltonian field, including momentum sign. |
| R2 coordinate equivalence | `p11cPhaseEquiv` :215 | PASS | Actual continuous linear equivalence, no substitute phase carrier. |
| R2 Hamiltonian local flow | `p11c_analytic_hamiltonian_flow` :221 | PASS locally | Exactly the analytic/solution projection of R3's signed theorem; source premises only. |
| `bpP:p11b:e-ode`, design:86, shared R1–R3 | local R2 contribution above | PASS locally / incomplete as full node | R3 owns the signed symplectic theorem; no unsigned export pretends to prove the full global-domain external fact. |
| R2/U5 compact common-neighbourhood obligation | no declaration or internal proof | FAIL (F1) | Explicit design obligation absent from the slice. |
| T9 `bpP:p11b:flow`, `fl-bd`, `fl-an` | downstream consumers, not R2 exports | Not audited as proved | See consumer analysis; compactness, parameter constancy, uniqueness gluing and continuation remain necessary. |

No R2 declaration has a SIGNED counterpart in the supplied signature file. In particular, the local helper is not a renamed claim of `real_analytic_hamiltonian_local_flow`, and it lacks that theorem's symplecticity conclusion intentionally. Frozen-provider exact-type and seal-body probes are therefore not applicable. A scratch example copies the signed theorem's analytic/solution projection with its explicit H and x binder order and closes it with `exact p11c_analytic_hamiltonian_flow hW hH hx`; this tests actual R3 input compatibility without assuming symplecticity.

## Definitions, proof and import assessment

The only new definitions in the audited module are `p11cPt` and `p11cPhaseEquiv`: both are explicit coordinate maps with their intended meaning on the entire carrier. Neither has a junk branch, default or chosen flow. Zero-dimensional carriers are allowed; the radius division uses `‖e‖+1`, so it remains positive in that case.

The proof restricts the complex extension to a smaller ball inside the requested real neighbourhood, proves the complex limit is real on real inputs, transports the fixed-point integral through the continuous real-part map, and applies the fundamental theorem of calculus. The Phase transfer conjugates the actual vector field and transports HasDerivAt through the inverse continuous linear equivalence. No conclusion-shaped assumption or additional small-field hypothesis was found. Existence, analyticity, reality and the ODE identity are constructed rather than assumed. The local integral equation is available inside the proof; R3 can also recover its needed identity from the exported solution predicate.

Recursive KAM import inspection found 44 modules, no provider, and ten frozen modules, all **SEALED definitions** in the manifest: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm and Planetary.Phase. No DRAFT_SORRY frozen theorem is imported. Mathlib is the external library dependency.

## Independent checks

The independent receipts follow. All Lean/Lake work is serialized for this auditor with `LEAN_NUM_THREADS=1` and niceness 5. The targeted build uses the required compile gate. No heartbeat/recursion override, cache command, package mutation, full-library rebuild, or additional agent was used.

### Targeted build — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-r2 KAM.Planetary.PlanarTorsion.RealFlow.Analytic
```

Output:

```text
[inp-gate] slot 2 acquired 19:51:05 for KAM.Planetary.PlanarTorsion.RealFlow.Analytic
Build completed successfully (9090 jobs).
```

The wrapper runs `nice -n 5 lake build` on that target; the job count is Lake's reported dependency graph, not a command to rebuild the library from scratch. No warnings/errors were printed.

### Signed-projection applicability and all public theorem axioms — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/R2Audit.lean
```

The copied R3 input-projection example elaborated without warnings/errors. Exact axiom output:

```text
'KAM.Planetary.p11cPt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cPt_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cSp_p11cPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cTimeScale_p11cPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cIsReal_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_eq_realInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_hasDerivAt_of_integral_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_analytic_flow_fin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_hamField_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_analytic_hamiltonian_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.RealFlow.Analytic KAM.Planetary.PlanarTorsion.RealFlow.PicardData KAM.Planetary.PlanarTorsion.RealFlow.PicardComplex KAM.Planetary.PlanarTorsion.RealFlow.PicardOp
```

One invocation, including the three Picard dependency modules as hygiene checks. Exact output:

```text
replaying KAM.Planetary.PlanarTorsion.RealFlow.PicardOp
replaying KAM.Planetary.PlanarTorsion.RealFlow.PicardComplex
replaying KAM.Planetary.PlanarTorsion.RealFlow.PicardData
replaying KAM.Planetary.PlanarTorsion.RealFlow.Analytic
```

### Repository lint — exit 1; scoped module clean, inherited diagnostics retained

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p11c-r2/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (893 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The stale generated root is the brief's permitted exception; it was not regenerated. The frozen AmdConfinement line is an additional inherited lint failure, not covered by that generated-root exception. It lies outside this audit's module and is unchanged in the protected-path diff; frozen bytes must not be repaired by this auditor. Therefore full repository lint did **not** pass. Module-system validation, frozen guard and all 144 ABI hashes passed independently within that run.

### Static and protected-path checks — PASS

- Audited module: 262 lines; longest line 99 Unicode characters. Copyright, `module`, public imports, module docstring, exposed public noncomputable section all present.
- Comment-masked scan for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, and `set_option`: no matches in Analytic.lean.
- Extracted all twelve declaration short names and searched declaration sites throughout KAM: no duplicate short name outside this module. All declarations are inside `KAM.Planetary`; no root declaration, instance or harmful root shadow was introduced.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty (apart from Git's multiple-merge-base warning).
- `git diff --check inp...HEAD`: exit 0 (same warning only).
- `git diff --check` and `git diff --no-index --check /dev/null /root/code/KAM-inp-p11c-r2/docs/tracks/P/audits/R2-audit-1.md`: exit 0. Report contains no control characters other than newlines.
- Auditor scratch probe and two receipt logs deleted after transcription. Final status contains only this new report and the pre-existing untracked R2-handoff.md; no tracked modification.

## Errata, deviations and limits

No new pinned-paper erratum or frozen-statement defect was found. No primary PDF was re-audited: this is the requested Lean package/source-contract audit against the supplied blueprint/design/signature material. The known design-audit N1/N2 notes do not close F1. F1 is the exact R2 implementation/design deviation, with quoted authority and consumer analysis above; no assumption, norm, law or carrier was silently changed to repair it.

No implementation repair was attempted. Build, axiom and kernel success establish the submitted local results, not compact-set assembly, symplecticity, T9, a frozen anchor seal, or a planetary headline. The remaining uncertainty is the unformalized downstream compactness/patching route, not the soundness of the checked local proofs. Complete the assigned R2 compact common-neighbourhood obligation before claiming the original R2 slice complete.
