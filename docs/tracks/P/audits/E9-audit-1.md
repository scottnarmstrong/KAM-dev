# E9 independent package audit 1

Overall verdict: **PASS WITH NOTES** for E9 / `bpP:p14:lift`.
No frozen anchor is proved or proposed for sealing by this slice. The provider/frozen-type and
frozen-seal-body tests are therefore not applicable; the signed ordinary theorem was tested instead.

## Scope and authority

Audited only `KAM/Planetary/Exponential/Lift.lean`, at HEAD
`c7f3c5add88f44ddcb3d7b333be04fe9cac9ba24`, against `inp...HEAD`.
The initially observed inp ref was `b6dab3a6fc8453330a4abaa465a782e1aa713798`;
this is a merge-base comparison, not a request to audit later changes on inp.
The diff adds this one 327-line module. Its SHA-256 is
`a21f031edce932858882930ce34c5a8641c2192f165e45715a92f66c4d6a7b34`.

Read AGENTS, PLAN, DECISIONS, the package audit brief, E9 handoff and AUDIT FOCUS;
P14 design (E9 row at 382, complete assigned node rows 165–170, conventions and consumer plan),
both P14 design audits; p14a 247–255 and its stopped consumer 281–283;
track-P statement's low-AMD/additions interfaces; relevant frozen definitions and the downstream
PlanetaryExponentialSafety anchor. Dependency interfaces were inspected only to assess E9.
The user's explicit report path overrides the generic brief's main-worktree output instruction.
Only this report and temporary `.lake/abi-scratch/` audit artifacts were written; no git mutation.

Signed authority: `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:343–352`, SHA-256
`24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.
The entire `lift` declaration header, up to its proof delimiter, is **byte-identical** to this signature.
Implementation helpers have no corresponding signed declarations; they are checked against their
local mathematical obligations, rather than treated as additional graph-node exports.

## Declaration and node ledger

All names below are in `KAM.Planetary`; line numbers refer to Lift.lean.

| Node / obligation | Declaration or proof location | Verdict | Reason |
|---|---|---|---|
| Pulled-back Hamiltonian | `liftChartHam`, 52 | PASS | Literal movingHamiltonian composed with poincareProd at both fixed parameters 1. |
| Compact zero-angle base | `liftQ`, 56 | PASS | Zero fast angles, closed action window, chartAMD upper bound. |
| li-proj chart-field transport | `liftPhysicalDeriv`, 63 | PASS | Uses the actual symplectic chart via phaseCast and poincareProdCast; differentiability is explicit. |
| li-max open domain | `isOpen_chartSafe`, 102 | PASS | Actual collision-free preimage inside product chart domain. |
| Chart-domain inclusion | `chartSafe_subset_dom`, 105 | PASS | Intersection projection, valid for arbitrary masses. |
| Hamiltonian regularity | `analyticOnNhd_liftChartHam`, 108 | PASS | Analytic composition on chartSafe, positive masses only. |
| li-max C1 field | `contDiffOn_liftField`, 113 | PASS | Analytic Hamiltonian gives C1 Hamiltonian field on the open domain. |
| Negative lattice shift | `liftFastShift_neg`, 118 | PASS | Actual frozen radian shift, componentwise negation. |
| Invariant domain | `chartSafe_shift_iff`, 124 | PASS | Both directions from lattice invariance; inverse shift proved. |
| li-max periodic field | `liftField_periodic`, 135 | PASS | Differentiates local Hamiltonian periodicity on the invariant open domain. |
| Closed compact-base set | `liftQ_isClosed`, 151 | PASS | Continuous coordinate equalities and non-strict inequalities. |
| Slow-coordinate bound | `liftQ_slow_bound`, 167 | PASS | Quadratic sum controls each slow coordinate; coarse bound works for every AMDBox. |
| Fast-action bound | `liftQ_fast_bound`, 180 | PASS | Closed action interval controls absolute coordinate by finite sum. |
| li-cont compact base | `liftQ_isCompact`, 190 | PASS | Closed and bounded in finite-dimensional Pi/product sup norm. Does not claim compactness of unrestricted angles. |
| Angle-zeroing identity | `chartAMD_zeroAngle`, 217 | PASS | Preserves both slow blocks in the frozen assemble order. |
| li-cont orbit membership | `liftQ_of_orbit`, 227 | PASS | Dictionary transfers physical outer bounds to zero-angle closed cylinder. |
| li-cont safe cylinder | `liftQ_mem_chartSafe`, 242 | PASS | EnlargedData supplies source geometric inequalities; E3 proves safety, not an assumed safety field. |
| `bpP:p14:lift` | `lift`, 252 | PASS | Exact signed telescope and full signed conclusion, no extra premise or weakened carrier. |
| `stepP:p14:li-init` | `lift`, 266–273 | PASS | Onto prograde chart gives w0; frozen solution collision clause gives chartSafe membership. |
| `stepP:p14:li-max` | `lift`, 274–275 | PASS | gen_maximal on open chartSafe with C1 field; periodicity separately proved and consumed below. |
| `stepP:p14:li-proj` | `lift`, 276–288 | PASS | Pointwise chart transport, moving_ode, uniqueness on intersection containing zero. |
| `stepP:p14:li-cont` | `lift`, 289–312 | PASS | E8 uniform data on cylinder over liftQ; both endpoint contradictions use only times already in the physical segment. |
| `stepP:p14:li-concl` | `lift`, 313–323 | PASS | Segment lies strictly inside maximal interval; dictionary gives exact physical action/AMD identities. |

This accounts for all six design-table records assigned to Exponential/Lift, all 16 public theorems,
and both definitions. No unsigned export is named as a graph node with a narrower conclusion.

## Statement fidelity, completeness and consumers

`lift` permits every real mu, arbitrary admissible n, and l≤0≤r, including the singleton [0,0].
It retains `Phase (n*2)` for physical points and `Phase (n+n)` for chart points, the frozen
Hamiltonian and collision predicates, and radian fast shifts. No conclusion-shaped hypothesis,
new instance, fictitious inverse chart, or implicit continuation assumption is introduced.

The signed result omits the blueprint's explicitly written differentiability, open action bounds,
strict AMD bound and enlarged-cylinder membership. These are recoverable from its own conclusion:
analyticOnNhd_liftChartHam gives differentiability at each safe point; action/AMD identities and
hout give strict outer bounds; original_cylinder_subset gives enlarged membership. With any
EnlargedData, kappa_pos and amd_lt also give workingCylinder membership. A fresh **proved**
`auditConsumer` probe checked all five facts together from exactly the signed lift premises and
EnlargedData; exit 0. This covers the E11 st-seg needs at p14a:281 and the E9→E11 plan at design:447.
Future E10/E11 field-identification, erosion and N-root obligations are outside E9; they are not
assumed or claimed discharged here.

For continuation, under Tp≤r every time 0≤t<Tp is in [l,r], so the projected equality supplies
outer-region bounds before applying gen_continuation. It then forces Tp=top, contradicting Tp≤r.
The negative endpoint uses the symmetric valid restriction. Neither argument uses physical bounds
past the given interval. The maximal chart solution therefore exists on a neighborhood of the closed
segment and supplies actual two-sided HasDerivAt even at l and r.

## Definition classification

- `liftChartHam`: intended total composition on its entire carrier. No altered Hamiltonian, dummy
  value or fallback. All derivative applications are restricted to chartSafe.
- `liftQ`: intended closed zero-angle cylinder base on its entire carrier. It remains a legitimate
  set even for inadmissible B (possibly empty); closedness/compactness do not assume admissibility.
  Positive-mass/admissibility/enlargement premises enter only the orbit and domain bridges.

## Independent validation

Every Lean/Lake invocation used default resources, nice priority 5 and LEAN_NUM_THREADS=1;
validation stages ran serially. The build waited for the prescribed compile gate.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e9 KAM.Planetary.Exponential.Lift`
   (wrapper executes `nice -n 5 lake build ...`): **exit 0**.
   Exact terminal summary: `Build completed successfully (9137 jobs).`
   No Lift warning. Replayed unused-variable warnings occur in Energy, Poincare/Chart, Mass,
   RealDomain, Hamiltonian/Algebra and Hamiltonian/Chart.
2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E9Audit.lean`: **exit 0**.
   The probe copies the signed declaration under auditLift, proves it by applying lift to its
   explicit binders in order, and checks both `example : type_of% @auditLift := @lift` and the
   reverse assignment. It also proves auditConsumer as described above.
3. `#print axioms` for every theorem in the ledger: all 16 produce exactly
   `[propext, Classical.choice, Quot.sound]`. Full output follows:

```text
'KAM.Planetary.liftPhysicalDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_chartSafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chartSafe_subset_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_liftChartHam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.contDiffOn_liftField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.liftFastShift_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chartSafe_shift_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.liftField_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.liftQ_isClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.liftQ_slow_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.liftQ_fast_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.liftQ_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chartAMD_zeroAngle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.liftQ_of_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.liftQ_mem_chartSafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.Lift`: **exit 0**.
   Exact output:

```text
replaying KAM.Planetary.Exponential.Lift
```

5. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`: **exit 1**.
   Exact output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p14-e9/KAM/Frozen/Planetary/Theorems/AmdConfinement.lean:77:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (889 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

   The module checker, frozen-anchor guard and all 144 ABI hashes pass. The two diagnostics
   are recorded below; full repository lint is not clean. An initial preliminary lint run was
   stopped before ABI elaboration and replaced by this complete serial, thread-limited run.

## Hygiene and notes

Static module checks: copyright, module, public imports, module documentation and exposed public
section present; 327 total lines, no line over 100 characters; no forbidden proof escape, resource
override or EuclideanSpace token. No ambient carrier substitution. No new helper short name is reused
anywhere else in KAM. Mathlib's Submodule.liftQ is namespaced, not a root constant being shadowed.

A static recursive traversal of the 91-module KAM import closure found **no provider and no frozen
theorem imports**. Thus no DRAFT_SORRY or sealed-theorem dependency is hidden in the proof; only frozen
definitions are used. The theorem axiom checks independently exclude sorryAx.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
`git diff --check inp...HEAD` passes with no output.

N1 (nonblocking name note): the signature requires KAM.Planetary.lift; the existing
KAM.Planetary.SecularSpectrum.lift at SecularSpectrum/Lift.lean:34 has the same short name in a
nested namespace. This is not a new unsigned helper collision. Callers opening that namespace
should qualify the E9 theorem. No current E9 call resolves to the spectral theorem.

N2 (repository lint): the frozen AmdConfinement line-length defect (77:101) is outside E9 and
unchanged by its diff. It is an additional failure beyond the brief's allowed generated-root
exception, so the full lint command is explicitly recorded as failing. The generated-root
staleness is the expected permitted exception. Neither file was modified. The handoff's claim
that inp later fixed the frozen line is not used to waive the defect in this checkout.
This is why the overall package verdict carries notes rather than claiming a clean repository gate.

## Defects, deviations and limits

No suspected new blueprint or pinned-source mathematical defect was found. The signed narrowing is
accounted for by the independently elaborated consumer probe. No new source deviation was introduced.
This audit verifies the E9 slice and its actual dependency types/axioms; it is not a fresh pinned-PDF
review, a proof of the other P14 packages, or closure of planetaryExponentialSafety.

The report is the sole persistent audit edit; scratch probe files are removed after verification.
