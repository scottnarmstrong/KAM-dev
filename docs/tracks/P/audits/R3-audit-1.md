# Independent R3 audit 1

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-r3`.
Audited HEAD: `6e298e3e9c3151717b9dd888814c0d7c7d6f851a`.
Initial comparison ref `inp`: `eff45716c45678ce9fbb21a346ab5821d70a823b`.
Final comparison ref `inp`: `eedc66febf1e2749337a502351ab1515c1779c15`.
The ref advanced during the audit; both three-dot diffs are byte-identical
(SHA-256 `50201d96ef724db4d837c88b2d6af883254ffbaf5c5fb06886b03b0591d1e71b`),
with merge base `7c254d1ada904dce883560fd988ff208b2edcb35`.
Final three-dot whitespace and protected-path checks were repeated and passed.

**Verdict: PASS WITH NOTES for package R3.** The signed export
`KAM.Planetary.real_analytic_hamiltonian_local_flow` passes exact signature and proof review.
All R3 mathematical obligations are proved. This is infrastructure acceptance, not a frozen-anchor
seal or a claim that the planetary theorem is closed. No frozen theorem is implemented by this slice;
provider/frozen type equality and frozen seal-body probes are therefore not applicable.
The analogous signed-type and explicit-argument application probes pass.

The notes are the permitted stale generated root and the scope of the designed bridge: the signed
local Hamiltonian theorem is established, while compact-uniform parameter continuation and time-one
assembly remain downstream obligations. R3 neither uses nor needs the pending R2 compact
common-neighbourhood extension.

## Authority, comparison and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied package-audit brief,
`docs/tracks/P/audits/R3-handoff.md`, `docs/tracks/P/statement.md`,
`docs/tracks/P/design/P11C-LEAN-DESIGN.md`, its design audit
`docs/tracks/P/design/DESIGN-P11C-design-audit-1.md`, the relevant Part-11b blueprint, and
`/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`.
The user's explicit absolute destination overrides the generic brief's main-worktree destination.

Reviewed the full `git diff inp...HEAD`: five new RealFlow files, 1,044 inserted lines.
Four files (`Analytic`, `PicardComplex`, `PicardData`, `PicardOp`) are inherited R2 context.
`git show --stat HEAD` attributes exactly the 288-line `Variational.lean` addition to R3.
Only `KAM/Planetary/PlanarTorsion/RealFlow/Variational.lean` is audited for a package verdict;
there are no additional `Variational*.lean` files. R2 context is inspected for dependency
applicability, not independently re-certified here. The initial untracked `R3-handoff.md` is preserved.

## Declaration and node review

All declaration names below are in `KAM.Planetary`; line numbers refer to
`KAM/Planetary/PlanarTorsion/RealFlow/Variational.lean`.
The design node table at line 86 maps only `bpP:p11b:e-ode` to R1–R3; the R3 work row is line 209.
There is no unsigned export purporting to implement a different graph node.

| Node / obligation | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| R3 coordinate algebra | `p11cVar_clm_eq_sum` (44) | PASS | Arbitrary continuous linear functional decomposed over both finite coordinate blocks; no dimension-positivity premise. |
| R3 linearisation definition | `p11cVarLin` (59) | PASS | Literal Hamiltonian linearisation from any continuous bilinear form. |
| R3 frozen sign | `p11cVar_form_lin_left` (62) | PASS | Proves Omega(Mw,v) = -B(w,v) for the actual frozen form. |
| R3 frozen sign | `p11cVar_form_lin_right` (69) | PASS | Proves Omega(w,Mv) = B(v,w). |
| R3 Hessian cancellation | `p11cVar_form_add_form_eq_zero` (77) | PASS | Symmetric-bilinear-form helper; its symmetry premise is separately proved for the Hessian. |
| R3 product rule | `p11cVar_hasDerivAt_form` (84) | PASS | Differentiates the actual finite coordinate sum with both curve derivatives. |
| R3 field derivative | `p11cVar_hasFDerivAt_field` (110) | PASS | Constructs the full derivative of the frozen Hamiltonian field from analyticity of H. |
| R3 field derivative | `p11cVar_fderiv_field` (127) | PASS | Identifies that derivative with the explicit Hessian linearisation. |
| R3 Hessian symmetry | `p11cVar_hessian_symm` (134) | PASS | Analyticity supplies continuous second derivatives and Schwarz symmetry. |
| R3 infinitesimal conservation | `p11cVar_field_form` (139) | PASS | Specializes the algebraic cancellation to the Hessian; no symplecticity assumption. |
| R3 slice derivative | `p11cVar_fderiv_slice` (154) | PASS | Chain rule identifies the data slice derivative with joint derivative on (0,u). |
| R3 variational equation | `p11cVar_variational` (166) | PASS | Differentiates the proved solution equation on an open product domain and exchanges mixed derivatives by analytic Hessian symmetry. |
| R3 form derivative | `p11cVar_form_hasDerivAt` (230) | PASS | Combines both variational equations and infinitesimal cancellation to obtain derivative zero. |
| R3 frozen form conservation | `p11cVar_form_const` (242) | PASS | Constancy on connected Ioo(-T,T); explicit T>0 ensures the comparison time 0 is inside. |
| R3 symplecticity | `p11cVar_isSymplecticOn` (259) | PASS | Initial identity holds on an open data ball, hence its derivative is the identity; form preservation has factor exactly 1. |
| `bpP:p11b:e-ode`, signed R1–R3 bridge | `real_analytic_hamiltonian_local_flow` (277) | PASS | Exact signed statement: positive local radii, joint time/data analyticity, initial condition, actual ODE in W, and symplecticity for every local time. |

The signed theorem header is byte-for-byte equal to the header at signature-file lines 442–449
and design-appendix lines 758–765. The fresh probe copies that header under `r3AuditSignedCopy`
and proves it with `exact real_analytic_hamiltonian_local_flow hW H hH x hx`.
Both `type_of% @r3AuditSignedCopy` / `@real_analytic_hamiltonian_local_flow` assignments elaborate.
Thus implicit dimension/domain binders, explicit argument order, constants, carriers, and all
conjuncts match; the inner `{d : Nat}` does not add a harmful shadow binder.

The generic flow helpers accept a solution and analyticity as typing/source premises, as is
appropriate for conditional infrastructure. The final theorem constructs these with
`p11c_analytic_hamiltonian_flow`; it assumes neither a solution, variational equation, Hessian
symmetry nor form conservation. Membership in W is obtained from `IsSolutionIn` before applying
analyticity of H. Local equalities are promoted to neighbourhood equalities only inside the
open product or open ball, so totalized `fderiv` is not exploited at a nondifferentiable point.

## Definitions and imports

The only new public definition is exposed `p11cVarLin` (59–60):
`(fun i => B w (0, Pi.single i 1), fun i => -B w (Pi.single i 1, 0))`.
It is the intended object on its entire carrier, including dimension zero and nonsymmetric B;
no fallback, conditional choice, quotient carrier or junk value is introduced. Hessian symmetry
is required only for its cancellation theorem. Proof-local `Psi` is the given joint flow,
not an alternate representation. There are no new structures, abbreviations or instances.

The form is literally `sum (v.2*w.1 - v.1*w.2)` and the field is literally
`(partial_p H, -partial_q H)`. `Phase d` remains `(Fin d -> R) x (Fin d -> R)`.
`IsSymplecticOn 1` is the existing frozen-form preservation predicate from `KAM/Kepler/Basic.lean:31`;
`IsSolutionIn` is the actual domain-membership plus `HasDerivAt` predicate from `KAM/ODE/Basic.lean:41`.
No EuclideanSpace, hidden metric change, extra normalization or physical-time rescaling occurs.

Project-import traversal found 46 KAM modules, no providers and no frozen theorem imports.
The ten reachable frozen modules are all manifest-SEALED definitions: ActionNbhd, ComplexStrip,
HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals,
OmegaZero, SymplecticForm, and Planetary.Phase. No DRAFT_SORRY anchor is imported.
A repository declaration-name search found no reused public short name among the 16 new declarations.
All live in `KAM.Planetary`; no root declaration is introduced.

## Completeness, consumers and deviations

Blueprint `blueprint-P/parts/p11b-planar-torsion.tex:20` says:
“The flow of a real-analytic vector field depends real-analytically on time, initial data and
parameters on its (open) domain of definition.” The signed theorem deliberately supplies the
local Hamiltonian bridge, rather than that entire generic/global assertion. This is exactly the
narrowing accepted in the P11C design audit (signed statement row at line 53). R3 establishes the
whole signed bridge and every additional obligation in its work row: variational equation,
Hessian symmetry, and frozen-form conservation. It does not establish global analytic dependence
on a maximal flow domain or declare the whole generic external fact sealed.

Design consumers T9 (`flow`, compact-uniform time-one map) and T11 (`full_lift_hamiltonian`,
`lift_map`) need continuation/uniqueness, parameter attachment and full Hamilton equations beyond
this local theorem. Those remain explicitly assigned consumer obligations in design lines
255–257 and the node table; there is no production consumer of the new export yet in this
checkout. The local variational/form lemmas apply to any jointly analytic solution on their stated
open product, so a later common-neighbourhood flow can use them directly. R3 uses only R2's
local-at-a-point result and requires no R2 compact extension for its own proof. Acceptance here
must not be read as acceptance of the future T9/T11 applications without those bridges.

Method variation from design line 253: the proof differentiates the ODE identity obtained from
`IsSolutionIn`, rather than directly differentiating the integral equation. Analyticity permits
both derivative operations and mixed-derivative symmetry, so this changes no hypothesis or result.
No suspected pinned-source or blueprint mathematical defect was found in the R3 slice.
Primary-paper results outside this local infrastructure were not independently re-audited.

## Independent checks

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The targeted build used the mandatory compile gate. Lint is run only after the other Lean
processes finish because its ABI check launches Lean internally.

1. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.
2. `git diff --check inp...HEAD`: exit 0, empty output.
3. `LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-r3 KAM.Planetary.PlanarTorsion.RealFlow.Variational`:
   exit 0. Output: `[inp-gate] slot 2 acquired 20:44:45 for KAM.Planetary.PlanarTorsion.RealFlow.Variational`
   and `Build completed successfully (9092 jobs).` No warnings/errors.
4. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/R3Audit.lean`: exit 0;
   both type assignments and the signed explicit-argument copy elaborate without diagnostics.
   `#print axioms` for all 15 public theorems produced the following exact lines:

```text
'KAM.Planetary.p11cVar_clm_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_form_lin_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_form_lin_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_form_add_form_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_hasDerivAt_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_hasFDerivAt_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_fderiv_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_hessian_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_field_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_fderiv_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_variational' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_form_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_form_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_isSymplecticOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_analytic_hamiltonian_local_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

5. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.RealFlow.Variational`:
   exit 0. Exact output:

```text
replaying KAM.Planetary.PlanarTorsion.RealFlow.Variational
```

6. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`: exit 1 solely for the
   explicitly allowed generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (923 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

7. Direct source checks: 288 lines; maximum line width 100; forbidden-token scan empty;
   complete module header/public section present; all public definition bodies exposed.
   No heartbeat, recursion-depth or synthesis-heartbeat option is used.
8. The probe `.lake/abi-scratch/R3Audit.lean` was deleted after checking. No source,
   frozen, manifest, generated root, package dependency, or git state was edited.
   Final `git diff --check` passes; only this report is newly written by the auditor.

## Handoff

Auditor-authored file: `/root/code/KAM-inp-p11c-r3/docs/tracks/P/audits/R3-audit-1.md`.
No mathematical repair is requested for R3. The orchestrator may integrate the exact signed
local Hamiltonian bridge, retain the R2 compact-extension work as a separate obligation, and
regenerate the root in its authorized integration workflow. No frozen anchor is seal-ready
on the strength of this infrastructure audit alone. No unresolved R3 proof uncertainty or
suspected source erratum was found; the consumer and generic-node scope limits above remain.
