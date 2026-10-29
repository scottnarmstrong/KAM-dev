# T11 independent package audit 1

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-t11`.
Audited HEAD: `d053b6bfab86f2dd43a84f044f8b2f121fb455c2`.
Compared `inp...HEAD`; inp observed at `9fc6965a034a91dede3a0eaedd019e922f0a7b80`.

## Verdict

**PASS WITH NOTES** for the signed T11 infrastructure exports `full_lift_hamiltonian`
and `lift_map`. No frozen theorem anchor is
being sealed by this package.

| Signed export | Overall verdict |
|---|---|
| `KAM.Planetary.full_lift_hamiltonian` | PASS WITH NOTES |
| `KAM.Planetary.lift_map` | PASS WITH NOTES |

This verdict does not certify the complete physical
Birkhoff normalization, its rotation composition, or a track-P headline.

Authority: the supplied package-audit brief; AGENTS.md; PLAN.md; DECISIONS.md;
T11-handoff.md AUDIT FOCUS; P11C-LEAN-DESIGN.md §§1–7, especially lines 122–124,
173, 212, 245, 257; DESIGN-P11C-design-audit-1.md:57,76,158–159;
blueprint-P/parts/p11b-planar-torsion.tex:166–176; track-P statement conventions;
and `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`.
Signature file SHA-256:
`6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`.

Only the seven Lift files are audited. Their complete additions in `git diff
inp...HEAD` were checked identical to the source files read. All 55 public
source declarations (43 theorems, 12 definitions) are inventoried below.

## Notes requiring accurate scope

1. `git diff inp...HEAD` warns: `multiple merge bases, using
   f52aac33fd708e594fcc4c7193d930a31c740283`. It covers 165 files, including
   inherited changes outside T11. The protected-path test is **not empty**:
   `KAM.lean` has 88 insertions. Frozen files, manifest, and README have no changes
   in this comparison. The six T11 commits, from `4534956d` through `d053b6bf`,
   change only the seven Lift files; `git diff 4534956d^...HEAD --name-only`
   establishes this. Generated-root changes are inherited; no attempt was made
   to repair them or choose a friendlier base.
2. The source proposition and node table mention the inverse-rotation lift and
   composition T. The approved design audit explicitly narrows signed `lift_map`
   to the chi-flow lift: “composition supplied by BirkhoffResult” (design audit
   line 57). `p11c_rotationLift` is owned by Frame/T14, and the composed map's
   chart, injectivity, action, translation and physical-domain properties are
   required by `PlanarBirkhoffResult` (design lines 908–935), owned by Birkhoff/T16.
   No composition or U9 equality adapter is implemented in this slice. This is
   the approved boundary, not evidence that the complete source composition is
   proved. Later consumers must still assemble T and shrink its domain.
3. The generated-root lint exception is permitted by the brief; its exact fresh
   result is recorded below. The root was not regenerated.

## Signed fidelity and expanded premises

Whitespace-normalized comparison of the *entire bodies* of `p11c_liftFlow` and
`p11c_tube`, and the entire headers of `full_lift_hamiltonian` and `lift_map`,
returned `EXACT_NORMALIZED_MATCH True` for all four. No binder, implicitness,
quantifier order, radius, carrier, derivative, sign, or conclusion was changed.
A scratch probe copies each signature theorem under a fresh name and supplies
`by exact <export> hO hO' hK hKO chi`; copied definitions are checked equal by
`rfl`. This tests term-level consumption, not name reachability.

The following binder classification applies independently to both signed theorems.
It expands the only project-owned input bundle, `QuarticFamily O`.

| Input | Bin | Source / reason |
|---|---|---|
| `{O : Set (Fin 2 → ℝ)}` | TYPING | Blueprint 167: action domain; signature exact carrier. |
| `{O' : Set (Fin 2 → ℝ)}` | TYPING | Blueprint 167: relatively compact subdomain. |
| `hO : IsOpen O` | SOURCE | Flow setting, blueprint 140–148,167. |
| `hO' : IsOpen O'` | SOURCE | Blueprint 167 explicitly open. |
| `hK : IsCompact (closure O')` | SOURCE | Blueprint 167 explicitly compact closure. |
| `hKO : closure O' ⊆ O` | SOURCE | Blueprint 167 explicitly contained closure. |
| `chi.coeff : (Fin 4 → ℕ) → (Fin 2 → ℝ) → ℝ` | TYPING | Quartic coefficient data in the flow setting; Characters/Defs:34–41. |
| `chi.analytic : ∀ a, AnalyticOnNhd ℝ (chi.coeff a) O` | SOURCE | Analytic quartic family in the flow setting; no flow, bounds or chart bundled here. |

Counts per theorem after expanding chi: SOURCE 5, TYPING 3, STANDING 0,
RULED 0, EXCESS 0. There are no instance binders. Degree four is enforced by the
finite evaluation sum, not assumed as an extra result. Output binders r, I,
lam, z, g (and w,c for lift_map) have exactly the signature's scope. Radius is
chosen from the family and domains before the initial data and angle translations.

Unsigned helpers are conditional coordinate/ODE/analytic lemmas with distinct
`p11cL_` names; none claims to replace a source node by assuming its conclusion.
`p11cL_FlowSpec`, the derivative bound D, and inverse premise hinv are proved
locally from T9/compactness before use. They are absent from signed inputs.

## Node coverage and proof review

| Design node | Declaration / proof location | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:lift-map` | Lift.lean:40,71; Defs.lean:34,43 | PASS WITH NOTES | Exact approved signed chi-flow surface; rotation composition remains T14/T16 as authorized above. |
| `stepP:p11b:lm-ham` | Field.lean:169; Orbit.lean:56,90,165; Lift.lean:40 | PASS | Actual full Hamilton equations, endpoints, domain and angle integral. |
| `stepP:p11b:lm-prop` | Iterate.lean:42; Inverse.lean:48,57; Injective.lean:41,67,118; Lift.lean:71 | PASS WITH NOTES | Real analytic symplectic injective lift, action preservation by definition, all angle translations; composed T remains downstream. |

The full field uses the frozen `(position,momentum)` convention and assembled
`(phi,q;I,p)` order. `p11cL_field_assemble` proves `(partial_I chi, Xchi.position;
0, Xchi.momentum)`, with the correct negative position derivative in the momentum
block. `p11cL_partial_eq` holds the trajectory value fixed when taking the action
partial derivative: it does not differentiate the entire parameterized flow.

`p11cL_ext` recenters at time 1/2 and uses uniqueness, extending the controlled
slow trajectory to an open interval (-1/2,3/2). This supplies genuine endpoint
HasDerivAt statements for the integral, not only one-sided information.
`p11cL_orbit_solution` proves continuity and interval integrability of the action
partial derivative before using the fundamental theorem of calculus.
`full_lift_hamiltonian` takes half the T9 radius and uses the squared slow-length
bound to keep the entire orbit in the original-domain tube of radius 2r.

For chart regularity, a compact K3 bounds all actions, slow variables, and the
angle slab. `p11cQ_flow_compact_nbhd` supplies one real analytic short-time full
flow. Positive subdivision time 1/m lies inside its interval; induction and ODE
uniqueness identify every iterate with the explicit orbit through time one.
The orbit keeps intermediate iterates inside U. Local eventual equality on the
open slab transfers derivatives and analyticity, and R3's
`p11cVar_isSymplecticOn` plus the chain rule proves preservation of the frozen
symplectic form. Translation covariance extends the result to arbitrary angles.
There is no assumed global boundedness of the angle directions.

Injectivity uses the min of the two half-radii obtained from `flow` for chi and
its negated quartic family. The endpoint slow length is less than 2r, so the
negative-family solution applies there. `p11cL_reverse` proves time reversal by
uniqueness; the action derivative of -chi negates and the substitution 1-t
cancels the angle integrals. The slow inverse is taken from T9's proved last
clause, supplied in Lift.lean:94–99. The full left inverse then proves InjOn.

No complex SmallField shortcut: the transitive local import closure has 121
KAM modules, no `KAM.Canonical.*`, no provider, and no frozen theorem module.
No project `sorryAx` is accepted through this boundary; fresh axiom and kernel
checks are below. Local complexification inside already delivered R2 is not an
application of the prohibited complex-small-field canonical theorem.

## Definition classification

| Definition | Classification and full-carrier check |
|---|---|
| `p11c_liftFlow` | Literal signed assembled flow-plus-integral formula, exact body; the action derivative holds the slow value fixed. Total-function semantics are exactly the signature's; flow conclusions are proved on the tube. |
| `p11c_tube` | Literal signed set of action membership and strict Euclidean slow-length bound. |
| `p11cL_act` | Literal action-coordinate projection, all phase points. |
| `p11cL_ang` | Literal angle-coordinate projection, all phase points. |
| `p11cL_slow` | Literal slow position/momentum projection, all phase points. |
| `p11cL_ham` | Literal composition chi.eval with action/slow projections. |
| `p11cL_dom` | Literal preimage of O under action projection. |
| `p11cL_dI` | Literal directional Frechet derivative in the action direction; meaningful analytic interpretation proved at actions in O. |
| `p11cL_L` | Concrete continuous linear coordinate projection; apply theorem is rfl. |
| `p11cL_FlowSpec` | Explicit internal conjunction projecting already proved T9 flow properties; a conditional helper interface, never a signed/source assumption. |
| `p11cL_nbhd` | Concrete open portion of tube with angle norm <1, later removed by translation. |
| `p11cL_negFamily` | Coefficientwise negation with proved analytic coefficients; eval equals -chi.eval. |

For all 12: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS
N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A;
DEFINITION_VERDICT PASS. No new choice, junk branch, structure instance, axiom,
or invented fallback is introduced. The *upstream signed* `p11c_flow` has an
explicit existence-choice/fallback definition (QuarticFlow/Spec.lean:34–39);
T11 uses only its proved T9 specification and uniqueness on the controlled
interval. This report does not endorse uncontrolled off-domain values as flows.

## Complete declaration inventory

All names below are in `KAM.Planetary`. Public helper signatures were read along
with their proofs. Conditional helpers have the explicit mathematical premises
stated above and never replace an unconditional signed theorem.

| Declaration | Exact source locator | Verdict | Reason |
|---|---|---|---|
| `full_lift_hamiltonian` | `KAM/Planetary/PlanarTorsion/Lift.lean:40` | PASS | Signed exact type/body. |
| `lift_map` | `KAM/Planetary/PlanarTorsion/Lift.lean:71` | PASS | Signed exact type/body. |
| `p11c_liftFlow` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:34` | PASS | Signed exact type/body. |
| `p11c_tube` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:43` | PASS | Signed exact type/body. |
| `p11cL_act` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:48` | PASS | Literal adapter; see definition audit. |
| `p11cL_ang` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:51` | PASS | Literal adapter; see definition audit. |
| `p11cL_slow` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:54` | PASS | Literal adapter; see definition audit. |
| `p11cL_ham` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:58` | PASS | Literal adapter; see definition audit. |
| `p11cL_dom` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:62` | PASS | Literal adapter; see definition audit. |
| `p11cL_dI` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:65` | PASS | Literal adapter; see definition audit. |
| `p11cL_act_assemble` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:69` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_ang_assemble` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:73` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_slow_assemble` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:77` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_assemble_eq` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:81` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_tube_iff` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:86` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_liftFlow_eq` | `KAM/Planetary/PlanarTorsion/Lift/Defs.lean:89` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_L` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:33` | PASS | Literal adapter; see definition audit. |
| `p11cL_L_apply` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:46` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_single_cc` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:48` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_single_cn` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:57` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_single_nc` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:67` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_single_nn` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:77` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_ham_analytic` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:85` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_dom_isOpen` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:89` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_fderiv_ham` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:92` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_fderiv_slice` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:106` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_partial_eq` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:118` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_dI_analyticAt` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:134` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_L_mom_c` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:141` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_L_mom_n` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:149` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_L_pos_c` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:157` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_L_pos_n` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:162` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_field_assemble` | `KAM/Planetary/PlanarTorsion/Lift/Field.lean:169` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_negFamily` | `KAM/Planetary/PlanarTorsion/Lift/Injective.lean:32` | PASS | Literal adapter; see definition audit. |
| `p11cL_negFamily_eval` | `KAM/Planetary/PlanarTorsion/Lift/Injective.lean:35` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_reverse` | `KAM/Planetary/PlanarTorsion/Lift/Injective.lean:41` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_left_inverse` | `KAM/Planetary/PlanarTorsion/Lift/Injective.lean:67` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_injOn` | `KAM/Planetary/PlanarTorsion/Lift/Injective.lean:118` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_act_shift` | `KAM/Planetary/PlanarTorsion/Lift/Inverse.lean:34` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_ang_shift` | `KAM/Planetary/PlanarTorsion/Lift/Inverse.lean:38` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_slow_shift` | `KAM/Planetary/PlanarTorsion/Lift/Inverse.lean:42` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_liftFlow_translate` | `KAM/Planetary/PlanarTorsion/Lift/Inverse.lean:48` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_chart_tube` | `KAM/Planetary/PlanarTorsion/Lift/Inverse.lean:57` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_asm_continuous` | `KAM/Planetary/PlanarTorsion/Lift/Iterate.lean:34` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_chart_local` | `KAM/Planetary/PlanarTorsion/Lift/Iterate.lean:42` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_FlowSpec` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:35` | PASS | Literal adapter; see definition audit. |
| `p11cL_hasDerivAt_append` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:43` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_slow_lt_of_sq` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:52` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_ext` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:56` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_orbit_solution` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:90` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_norm_le_slow` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:133` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_nbhd` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:138` | PASS | Literal adapter; see definition audit. |
| `p11cL_nbhd_isOpen` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:141` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_exists_bound` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:153` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |
| `p11cL_orbit_exists` | `KAM/Planetary/PlanarTorsion/Lift/Orbit.lean:165` | PASS | Coordinate/derivative/ODE/iteration/inverse helper; premises discharged in signed exports. |

## Fresh validation receipts

All Lean-facing commands were serialized, using `LEAN_NUM_THREADS=1` and
`nice -n 5`. No second Lean/Lake operation was launched while another audit
operation was active. The gate was allowed to wait.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t11 KAM.Planetary.PlanarTorsion.Lift
```

Exit 0. Output includes:

```text
[inp-gate] slot 2 acquired 22:51:10 for KAM.Planetary.PlanarTorsion.Lift
Build completed successfully (9167 jobs).
```

All seven audited modules were replayed successfully. Nonfatal scoped warnings:
Field:90 unused i; Orbit:207,226 deprecated push_neg; Inverse:54 unused
Fin.append_right and unnecessary `<;>`; Injective:83 deprecated push_neg;
Lift:68 deprecated push_neg and Lift:40 unused hO'. Additional inherited unused
variable warnings occurred in Hamiltonian.Algebra/Chart and Kepler modules.
There were no errors or proof holes. No heartbeat or recursion override was used.
This is a targeted build with existing artifacts, not a clean rebuild or a
claim that all upstream compilation was repeated.

### Signature and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T11Audit.lean
```

Exit 0, no diagnostics beyond the 43 requested axiom lines. The probe imports
Lift, copies the two signed definition commands under audit_ names and checks
`example : audit_<name> = <name> := rfl`; it copies the two signed theorem
headers under audit_ names with bodies
`by exact <name> hO hO' hK hKO chi`. All copied commands come from the pinned
signature path and hash above. It then prints axioms for every public theorem
in the inventory. Exact output:

```text
'KAM.Planetary.full_lift_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lift_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_act_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_ang_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_slow_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_assemble_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_tube_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_liftFlow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_L_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_single_cc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_single_cn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_single_nc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_single_nn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_ham_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_dom_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_fderiv_ham' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_fderiv_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_partial_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_dI_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_L_mom_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_L_mom_n' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_L_pos_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_L_pos_n' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_field_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_negFamily_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_left_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_act_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_ang_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_slow_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_liftFlow_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_chart_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_asm_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_chart_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_hasDerivAt_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_slow_lt_of_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_orbit_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_norm_le_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_nbhd_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_exists_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cL_orbit_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No other axiom, sorryAx, or project axiom occurs. The checks include the main
exports and every helper, including conditional helpers.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Lift KAM.Planetary.PlanarTorsion.Lift.Defs KAM.Planetary.PlanarTorsion.Lift.Field KAM.Planetary.PlanarTorsion.Lift.Orbit KAM.Planetary.PlanarTorsion.Lift.Iterate KAM.Planetary.PlanarTorsion.Lift.Inverse KAM.Planetary.PlanarTorsion.Lift.Injective
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.PlanarTorsion.Lift
replaying KAM.Planetary.PlanarTorsion.Lift.Defs
replaying KAM.Planetary.PlanarTorsion.Lift.Iterate
replaying KAM.Planetary.PlanarTorsion.Lift.Injective
replaying KAM.Planetary.PlanarTorsion.Lift.Field
replaying KAM.Planetary.PlanarTorsion.Lift.Inverse
replaying KAM.Planetary.PlanarTorsion.Lift.Orbit
```

### Source lint, anchor guard and ABI

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the brief's permitted stale generated-root exception.
Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1040 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module-format check, frozen-anchor guard, and all 144 elaborated ABI hashes pass.
No other source-lint failure was reported. The stale root was not regenerated.



### Static and protected-path checks

`git diff --check` and the scoped
`git diff --check inp...HEAD -- KAM/Planetary/PlanarTorsion/Lift.lean KAM/Planetary/PlanarTorsion/Lift`
exit 0 (the latter emits only the documented merge-base warning).
The source scan finds no sorry/admit/axiom/unsafe/opaque/EuclideanSpace or option
override in scoped code. All seven files have the required copyright, module,
public imports, module docstring, exposed public noncomputable section.
Lengths/max character widths:

| File under PlanarTorsion | Lines | Maximum line width |
|---|---:|---:|
| Lift.lean | 103 | 98 |
| Lift/Defs.lean | 100 | 97 |
| Lift/Field.lean | 194 | 99 |
| Lift/Orbit.lean | 239 | 99 |
| Lift/Iterate.lean | 175 | 99 |
| Lift/Inverse.lean | 108 | 99 |
| Lift/Injective.lean | 129 | 98 |

Total 1048 lines. A repository declaration-name scan found no duplicate public
theorem short names. All 41 unsigned theorem helpers and all 10 unsigned
definitions use p11cL_; every declaration is inside KAM.Planetary, with no root
shadow or global instance. The 121-module local import traversal finds no
provider/frozen-theorem/Canonical import. No provider seal probe is applicable:
this package exports infrastructure, not a manifest-bound theorem provider.

Exact protected-path command:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Nonempty: KAM.lean only, 88 additions (inherited). Its exact T11-local check
`git diff 4534956d^...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
The untracked preexisting T11-handoff.md was left intact.


## Suspected defects, deviations and limits

No new pinned-source mathematical erratum or frozen-declaration defect found.
The inherited blueprint `lm-prop` applicability gap is explicit at
p11b-planar-torsion.tex:175: “Hamiltonian flows are symplectic” cites complex
N symplectic/canonical results without their SmallField/gauge hypotheses.
P11C-LEAN-DESIGN.md:173 already records this; T11 instead supplies the full real
field/variational argument, without altering a source premise.

The design node/package table mentions rotation composition in T11, while its
signed surface and approved design audit put the final composition in
BirkhoffResult. This report retains that boundary explicitly. The remainder of
the blueprint proposition, including the physical composed map's image and
inverse-rotation adapter equality, is not newly certified by this audit.
The statement.md draft-status prose is historical; current owner decisions and
exact signatures control this package.

Repository mutations: this report only; temporary audit probes/logs in
`.lake/abi-scratch/` are removed after receipt extraction. No state-changing git,
source edit, frozen/manifest edit, root generation, cache fetch, or library clean.

## Final closeout

Independent targeted build, exact signature/body probes, all 43 axiom checks,
and one seven-module kernel replay passed. Lint has only the authorized stale
root exception; protected-path history contains the explicitly recorded inherited
root diff. Overall verdict remains **PASS WITH NOTES** for both signed T11 exports.
No further scoped proof gap or added premise was identified. The composed
rotation/Birkhoff result remains a downstream obligation, as the approved design
states. No frozen theorem closure is claimed.
