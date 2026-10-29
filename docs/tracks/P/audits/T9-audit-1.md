# T9 independent package audit 1

**Overall verdict: PASS WITH NOTES.** The T9 slice establishes the signed `KAM.Planetary.flow`
contract and all three assigned blueprint nodes. No proof, signature, carrier, constant-dependence,
or consumer-applicability defect was found. Notes concern inherited integration/generated-root
state and the distinction between package completion and frozen-anchor sealing.

## Scope and authority

Audited 2026-10-28 in `/root/code/KAM-inp-p11c-t9`, HEAD
`a0f6f39a49929a32bf1955ed6656b511f39fdfdc`. Initial comparison branch `inp` was
`bea4e8e486c920ad0f51758913e31756dd9e9554`.
Read AGENTS.md, PLAN, DECISIONS, the package-audit brief, the T9 handoff/AUDIT FOCUS,
P11C design and independent design audit, standalone signatures, Part 11b blueprint and graph
records, track-P statements, and relevant frozen definitions and ODE/R2 interfaces.
The user's exact worktree report destination overrides the brief's generic main-worktree destination.

The requested `git diff inp...HEAD` warns of multiple merge bases and uses
`19a3d0830989b00a03f86eb199bdd1a42c4f1fa4`. The other bases are
`eedc66febf1e2749337a502351ab1515c1779c15` and
`79e90422b35bfd0cb1b00a8cfdf7051122f6dbf4`.
Its 79-file comparison includes inherited I/N/P integration work. The complete scoped diff
is six new files, 926 source lines (962 diff lines). The seven T9 commits following
`c1ba4fe0` change exactly these six files; no unrelated implementation is audited as T9.
All six source files were read in full.

| File under `KAM/Planetary/PlanarTorsion/` | Lines | Maximum line width |
|---|---:|---:|
| `QuarticFlow.lean` | 138 | 100 |
| `QuarticFlow/Field.lean` | 177 | 100 |
| `QuarticFlow/Energy.lean` | 269 | 100 |
| `QuarticFlow/Spec.lean` | 79 | 100 |
| `QuarticFlow/Compact.lean` | 71 | 97 |
| `QuarticFlow/Analytic.lean` | 192 | 99 |

Authority hashes: standalone `P11CSignatures.lean`
`34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079`;
`P11C-LEAN-DESIGN.md` `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36`;
`p11b-planar-torsion.tex` `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1`.

## Nodes, signatures and consumers

| Node / anchor | Declaration or internal proof | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:flow` | `flow`, facade:42; `p11c_flow`, Spec:33 | PASS | Exactly SIGNED; source-only inputs, compact-uniform positive constants, analytic time-one map, [-1,1] trajectory, energy, cubic displacement, inverse on image. |
| `stepP:p11b:fl-bd` | Field:54-173; Energy:137-263; facade:55-85 | PASS | Quartic homogeneity gives cubic field bound; actual energy inequality, zero case, compact uniform data, maximal solution and continuation establish the required bound and existence. |
| `stepP:p11b:fl-an` | Compact:32; Analytic:33-188; facade:86-134 | PASS | Augmented parameters, compact common time, finite analytic iteration and uniqueness; mean-value displacement estimate and backward-trajectory inverse. |
| Frozen theorem anchors | None owned by T9 | N/A | This package contains infrastructure, no provider export or frozen seal. No anchor is declared seal-ready by this audit. |

The two SIGNED declarations are `p11c_flow` (signature:452-454) and `flow`
(signature:456-467). A mechanical comparison after removing only whitespace returns true
for the whole definition and the theorem header. A fresh Lean probe copies the signed
header under `T9Audit.signedFlow` and applies `KAM.Planetary.flow hO chi K hK hKO`;
a copied signed definition is checked against the implementation by `rfl`.
There is no missing or reordered binder, added premise, altered carrier or hidden instance input.
Provider=frozen-type and seal-body probes are inapplicable because T9 has no provider/anchor.

The blueprint:145 explicitly requires injectivity. The signed theorem encodes this as an
explicit left inverse rather than an `InjOn` conjunct. The scratch probe derives `InjOn`
on the entire small ball by applying the same negative-Hamiltonian map to an equality of images.
Thus the signed representation supplies the literal consumer requirement without a new premise.
The interval [-1,1] strengthens the blueprint's [0,1]. `AnalyticOnNhd` at every point of
K times the open slow ball supplies the stated neighbourhood analyticity.
Constants are selected after O, chi and K but before I,z, as required.

For the field bound C0 on `cthickening delta K`, the implementation selects
`C = 16*C0`, `r = sqrt(1/(64*C0))`. With u=slowLength squared this gives
`64*C0*u(z)<1`; the trajectory satisfies u(t)<=2u(z), and the image w satisfies
`32*C0*u(w)<=1`. The inverse therefore exists at w even if w is outside the original ball.
It is identified with t -> g(1-t) by uniqueness on [0,1]. No small-ball invariance is assumed.

The design:171,255 continuation warning is paid: Energy:251 obtains uniform data on a compact
closed ball; Energy:259 invokes `gen_confinement`, whose body (ODE/Continuation:155-179)
first obtains `gen_maximal` and then uses two-sided continuation with those uniform data.
Using this existing convenience theorem instead of a direct `gen_continuation_compact`
call is a verified proof-route variation, not a missing existence premise.

R2 usage is exactly the accepted compact flow interface
`p11c_analytic_flow_compact_nbhd` (RealFlow/AnalyticCompact:34-42): open W, analytic field,
compact K subset W, then a common open U, T>0, jointly analytic Phi and actual solutions.
Compact:32 transports it to finite-dimensional spaces via a continuous linear equivalence.
Analytic:124-188 applies it to (I,z)'=(0,X_I(z)), proves parameter constancy, compares by
uniqueness, and iterates one time-1/m map m times with every intermediate point in the
compact confining set. No Picard rate, derivative convergence rate, symplecticity, or extra
R2 assumption is consumed. The 21:38 ruling in the handoff is sufficient. R3's symplectic
result is not needed for this T9 proof; T11 retains the separate full-lift/symplectic task.
T10 receives the actual trajectory, analyticity and uniform cubic displacement; T11 and
Birkhoff assembly receive the same flow, existence and inverse. Their remaining theorems
are not claimed proved here.

The scoped proof nodes are implemented internally in the SIGNED result; no unsigned
export named for one of these graph nodes claims a narrower substitute. The reciprocal
comparison in the blueprint is replaced by a regularized Riccati argument; the displacement
integral estimate is replaced by the corresponding mean-value bound. Their required energy
and cubic conclusions are proved. Graph records still saying NOT_STARTED are left untouched;
this report is not a source-graph rewrite or a campaign theorem-closure claim.

## Every public theorem

All names below are in `KAM.Planetary`. Filename-only locators refer to the six files above.
Helper premises are analytic/source data or intermediate estimates proved at their call sites;
none is a constructed flow or desired final conclusion assumed in place of its proof.

| Declaration / locator | Verdict | Reason |
|---|---|---|
| `QuarticFlow.lean:38` `p11cQ_slowLength_le` | PASS | Explicit Euclidean slow length bounded by twice the existing Pi/product norm. |
| `QuarticFlow.lean:42` `flow` | PASS | SIGNED: identical binders, constants, domains, frozen field, trajectory, displacement and inverse. |
| `Analytic.lean:37` `p11cQ_aug_analytic` | PASS | Joint analyticity of the actual zero-parameter/physical-field product. |
| `Analytic.lean:42` `p11cQ_field_slice_contDiffOn` | PASS | Analyticity implies C1 for every I in O; no assumed regularity result. |
| `Analytic.lean:52` `p11cQ_aug_solution` | PASS | Zero parameter derivative forces constancy; second projection is the correct Hamilton ODE. |
| `Analytic.lean:72` `p11cQ_step` | PASS | Uniqueness on the connected intersection identifies the short flow with a shifted trajectory. |
| `Analytic.lean:97` `p11cQ_iterate_analyticAt` | PASS | Analyticity along every prior iterate suffices; zero iterate is identity. |
| `Analytic.lean:109` `p11cQ_continuous_u` | PASS | Continuity of the actual sum of four squares. |
| `Analytic.lean:114` `p11cQ_time_one_analytic` | PASS | Compact augmented-state neighbourhood, positive common time, finite iteration, local equality. |
| `Compact.lean:32` `p11cQ_flow_compact_nbhd` | PASS | Transports accepted R2 flow along a real continuous linear equivalence; no extra R2 demand. |
| `Energy.lean:33` `p11cQ_riccati` | PASS | Positive-datum comparison with epsilon=u(0)/10; arbitrary nonnegative K, including zero. |
| `Energy.lean:96` `p11cQ_u_nonneg` | PASS | Sum of nonnegative squares. |
| `Energy.lean:99` `p11cQ_slowLength_sq` | PASS | Exact square identity for the prescribed slow length. |
| `Energy.lean:102` `p11cQ_norm_sq_le` | PASS | Pi/product norm square bounded by the explicit Euclidean square. |
| `Energy.lean:122` `p11cQ_u_le` | PASS | Reverse norm comparison with the correct four-coordinate factor. |
| `Energy.lean:137` `p11cQ_energy_deriv` | PASS | Actual differentiated quadratic energy; cubic bound yields u prime <= 8 C u squared. |
| `Energy.lean:190` `p11cQ_forward_pos` | PASS | Riccati comparison on the connected segment; positivity is appropriate for this helper. |
| `Energy.lean:204` `p11cQ_forward` | PASS | Removes positive-datum restriction by uniqueness of the zero solution. |
| `Energy.lean:222` `p11cQ_two_sided` | PASS | Applies the forward estimate also to time reversal and the negative field. |
| `Energy.lean:245` `p11cQ_exists` | PASS | Produces existence and energy control from source bounds; compact uniform data and gen_confinement. |
| `Field.lean:31` `p11cQ_monomial_analytic` | PASS | Actual finite coordinate monomial, analytic everywhere. |
| `Field.lean:44` `p11cQ_monomial_smul` | PASS | Degree-four homogeneity with exactly the required sum-of-exponents premise. |
| `Field.lean:54` `p11cQ_eval_analytic` | PASS | Finite coefficient sum, joint in parameter and phase. |
| `Field.lean:68` `p11cQ_eval_smul` | PASS | Every summand has degree four, even outside the analytic parameter domain. |
| `Field.lean:77` `p11cQ_fderiv_slice_analytic` | PASS | Identifies the slice derivative with the joint derivative applied to (0,v). |
| `Field.lean:95` `p11cQ_eval_slice_analytic` | PASS | Restricts joint analyticity to a fixed allowed parameter. |
| `Field.lean:102` `p11cQ_field_analytic` | PASS | Derivative evaluations give the frozen field, without a surrogate representation. |
| `Field.lean:112` `p11cQ_fderiv_smul` | PASS | Differentiates homogeneity and cancels nonzero scaling; appropriate helper restriction. |
| `Field.lean:133` `p11cQ_field_smul` | PASS | Cubic homogeneity of the actual field for nonzero scalars. |
| `Field.lean:145` `p11cQ_field_bound` | PASS | Compact parameter times unit sphere; zero phase proved separately, nonzero phase rescaled. |
| `Spec.lean:39` `p11cQ_ham_neg` | PASS | Frozen field commutes with Hamiltonian negation, including its momentum sign. |
| `Spec.lean:46` `p11cQ_flow_eq` | PASS | ODE uniqueness removes choice dependence on [-1,1]. |
| `Spec.lean:59` `p11cQ_flow_spec` | PASS | Proves existence before selecting a solution; supplies initial value, ODE and energy. |

## Definition classification

| New definition | Classification | Whole-carrier and fallback assessment |
|---|---|---|
| `p11c_flow`, Spec:33 | SIGNED choice-based restricted solution | Exact signed total function: chooses a genuine solution on [-1,1] if one exists; returns z otherwise. Every claimed small-data use first proves existence; uniqueness identifies the choice. Values outside that time/domain contract are not used for dynamics or analyticity. |
| `p11cQ_u`, Energy:94 | Concrete polynomial | Sum of the four real coordinate squares on every Phase 2; no junk values or fallback. Proved equal to slowLength squared. |
| `p11cQ_aug`, Analytic:33 | Concrete autonomous product field | Literally (0, frozen Hamiltonian field at parameter I) on every input. Coefficients may be arbitrary outside O; all analytic uses lie in O. No assumed-flow or output field is bundled into it. |

There are no new structures, abbreviations, instances, substitute norms, or derivative
representations. The existing frozen Phase is the product of two `Fin 2 -> real` spaces;
the ambient norm remains Pi/product max. All reported physical slow bounds use the explicit
Euclidean slowLength. QuarticFamily has only coefficients and coefficient analyticity.
The actual frozen Hamiltonian field has (partial_p H,-partial_q H), as used throughout.

## Hygiene and independent checks

All Lean/Lake invocations below are serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
Lint's ABI subprocess inherits the same environment and scheduling priority. No cache reset,
package mutation, root regeneration, git mutation, or source repair was performed.

1. Targeted gate build (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-p11c-t9 KAM.Planetary.PlanarTorsion.QuarticFlow
```

```text
[inp-gate] slot 3 acquired 22:14:44 for KAM.Planetary.PlanarTorsion.QuarticFlow
Build completed successfully (9157 jobs).
```

The build replayed inherited unused-variable warnings from Kepler/Energy, Kepler/Mass
and Poincare/Chart. No scoped T9 warning or error occurred.

2. Exact-signature/definition/injectivity and all-public-theorem axiom probe (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T9Audit.lean
```

The probe contains the copied signed theorem closed by the actual theorem, the copied
signed definition checked by `rfl`, the derived `InjOn` example, and one `#print axioms`
for each of the 33 public theorems listed above. Exact output:

```text
'KAM.Planetary.p11cQ_slowLength_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_aug_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_field_slice_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_aug_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_iterate_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_continuous_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_time_one_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_flow_compact_nbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_riccati' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_u_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_slowLength_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_u_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_energy_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_forward_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_monomial_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_monomial_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_eval_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_eval_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_fderiv_slice_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_eval_slice_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_field_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_fderiv_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_field_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_field_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_ham_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_flow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_flow_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. One kernel replay invocation covering all six modules (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Planetary.PlanarTorsion.QuarticFlow \
  KAM.Planetary.PlanarTorsion.QuarticFlow.Field \
  KAM.Planetary.PlanarTorsion.QuarticFlow.Energy \
  KAM.Planetary.PlanarTorsion.QuarticFlow.Spec \
  KAM.Planetary.PlanarTorsion.QuarticFlow.Compact \
  KAM.Planetary.PlanarTorsion.QuarticFlow.Analytic
```

Exact output:

```text
replaying KAM.Planetary.PlanarTorsion.QuarticFlow
replaying KAM.Planetary.PlanarTorsion.QuarticFlow.Field
replaying KAM.Planetary.PlanarTorsion.QuarticFlow.Energy
replaying KAM.Planetary.PlanarTorsion.QuarticFlow.Compact
replaying KAM.Planetary.PlanarTorsion.QuarticFlow.Analytic
replaying KAM.Planetary.PlanarTorsion.QuarticFlow.Spec
```

4. Full source lint (exit 1, solely the expressly permitted stale generated root):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (960 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module check, frozen-anchor guard and all frozen ABI hashes pass. No other lint
failure is present. The generic root is intentionally left for the orchestrator under
the brief's explicit exception. Thus this is PASS WITH NOTES, not a claim that lint exited 0.

5. `git diff --check` and
`git diff --no-index --check /dev/null /root/code/KAM-inp-p11c-t9/docs/tracks/P/audits/T9-audit-1.md`
return 0 and 1 respectively, both with empty output (the no-index exit 1 records
the added report; it reports no whitespace errors). Report validation counts 33 theorem rows and 33 matching axiom receipts;
no pending placeholders or unexpected control characters remain.

The recursive project-import inventory contains 111 KAM modules and **zero providers or
frozen theorem anchors**. All frozen imports are definitions, so there is no imported
DRAFT_SORRY or cross-provider dependency to approve. Direct and transitive imports were
resolved against this checkout. All six files have copyright, module, public imports,
module documentation, public exposed noncomputable sections; none exceeds 1500 lines or
100 characters per line. Scoped forbidden-token/resource-override/instance scans find no
matches. All 34 unsigned helpers/definitions have unique public short names outside this
slice; the sole reused short name `flow` is SIGNED and is fully qualified as
`KAM.Planetary.flow`, distinct from `KAM.Canonical.flow` and `KAM.Nekhoroshev.flow`.
No root declaration or harmful root shadow is introduced.

The literal requested protected-path check
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
only `KAM.lean` has 30 inherited added imports. Frozen files, manifest and README are unchanged.
`git diff c1ba4fe0..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty:
T9 itself changes no protected path. The inherited root change predates all seven T9 commits
(last root commit `67626725`). This is recorded as a comparison-baseline note, not silently
reported as a clean three-dot protected-path check.

## Errata, deviations and limits

No new suspected pinned-paper erratum or false frozen statement was found. This audit checks
the requested Lean/signature/blueprint contracts; it does not claim a fresh primary-PDF audit.
The previously documented blueprint:148 gap (quoted graph note: “no edge supplies the initial
local/maximal solution or the uniform-data reduction on the confining ball”) is addressed by
the existing maximal-solution/compact-uniform-data route above. No source premise was added.
No new blueprint contradiction was found. The old complex-flow applicability gaps are not
used as proof shortcuts: T9 consumes the real R2 theorem, while real symplectic full lifting
remains R3/T11 work. P11C design-audit N1/N2 concern provenance/dispatch details, not a T9
statement defect; this checkout's design/signature hashes equal that design audit's hashes.

Implementation deviations are limited to whitespace wrapping, file splitting, the verified
`gen_confinement` route, and comparison/mean-value arguments replacing displayed reciprocal/integral
proof steps. They preserve the signed statements and all assigned mathematical conclusions.
No heartbeat design signal was encountered. The handoff's 135-line facade count is stale:
the submitted facade has 138 lines, still well within both limits.

Only `/root/code/KAM-inp-p11c-t9/docs/tracks/P/audits/T9-audit-1.md` is created as an audit
deliverable. The pre-existing untracked `T9-handoff.md` is preserved. Disposable probes and
receipt files in `.lake/abi-scratch/` are removed after transcription; no tracked source
or protected file is modified. Final status lists exactly those two untracked documents.

**Disposition:** accept the T9 infrastructure slice with the inherited/root notes above.
No T9 repair is required. This verdict does not seal a frozen anchor or close downstream
normal-form, full-lift, Birkhoff, or planetary headline theorems.
