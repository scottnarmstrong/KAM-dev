# SO-GRAPHM independent audit 2

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sographm`.
HEAD: `a637d023c692c2c73bb663c1bba601dffe5337b3`; comparison branch `inp`:
`6cad95806f4dbeafc1933f733daf875fdb3b097a`.
Scope: only `KAM/SpinOrbit/Graph/Inverse.lean`; full comparison `git diff inp...HEAD`.
The user's explicit absolute report destination overrides the generic brief's main-worktree destination.

## Verdict

**FAIL package naming hygiene. Mathematical exact-torus slice: PASS WITH NOTES.**
Both endpoints, `KAM.SpinOrbit.soBarrier_of_torus` and
`KAM.SpinOrbit.soBarrier_of_exact_torus`, pass mathematical review, build, axiom inspection,
integration elaboration and kernel replay. There is no frozen anchor or provider export here;
no seal-readiness claim applies to an anchor.

The particular names listed in audit 1 were repaired, the formerly overlong header was wrapped,
and the module docstring now names the actual inverse declarations. However, the broader explicit
requirement “no public short name reused from Mathlib or KAM” is still false:

| Audited declaration | Existing public declaration | Existing source locator |
|---|---|---|
| `KAM.SpinOrbit.SoGraph.Torus.graph` (178) | `Function.graph` | `Mathlib/Basic/Rel.lean:567` |
| `KAM.SpinOrbit.SoGraph.Torus.orbit` (200) | `MulAction.orbit` | `Mathlib/GroupTheory/GroupAction/Defs.lean:49` |
| `KAM.SpinOrbit.SoGraph.Torus.orbit` (200) | `KAM.Planetary.orbit` | `KAM/Planetary/PlanarTorsion/OrbitJet.lean:67` |
| `KAM.SpinOrbit.SoGraph.Torus.invariant` (222) | `ProbabilityTheory.Kernel.IsReversible.invariant` | `Mathlib/Probability/Kernel/Invariance.lean:63` |

These are helper declarations, including a theorem (`invariant`), so the finding does not depend
on whether the naming rule includes definitions. Rename them with distinctive short names,
or obtain an explicit narrower naming rule. Fully qualified declarations remain distinct;
no unsoundness or harmful root shadow was found. Lean confirms the existing `Function.graph`
and `MulAction.orbit` coexist, and opening `SoGraph.Torus` resolves the unqualified names to the
new helpers. The handoff's unrestricted “short-name check OK” claim is therefore refuted.
This extends the previous audit's non-exhaustive naming finding; it is not a new mathematical defect.

## Round-2 change fidelity

Compared `git diff 032b279f..HEAD -- KAM/SpinOrbit/Graph/Inverse.lean` against the full
`git diff inp...HEAD`. The latter adds 448 lines of Lean plus the existing handoff/audit-1 documents.
The repair changes `strictMono` to `soStrictMono` and the eight inverse-family identifiers
(`exists_inv`, `inv_unique`, `inv_spec`, `inv_apply`, `continuous_inv`, `inv`, `inv_add_one`,
`inv_φ_add_one`) to the documented `soGraphInv` family. Every reference was updated.

An independent Python comparison applied exactly this identifier map to the audit-1 source
(`git show 032b279f:KAM/SpinOrbit/Graph/Inverse.lean`), removed comments and whitespace from
both sources, and returned:

```text
RENAME_NORMALIZED_CODE_IDENTICAL True
LINES 448 MAX_CHARS 99 THEOREMS 29
FORBIDDEN []
TRANSITIVE_KAM_IMPORTS 52
QUARANTINE_IMPORTS []
```

Thus no statement, binder, premise, conclusion, constant, proof step or definition body changed
apart from consistent helper renaming. Both public endpoint names and types are unchanged.
The repaired helper short names had no other explicit declaration matches in the independent
KAM/Mathlib source scan. The three remaining reused short names above suffice to fail the rule.

## Authority, statements and slice completeness

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied audit brief, handoff
(including ROUND 2 FOCUS), audit 1, Revision 4 design
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, the main plan
`/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`, and
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §I. Inspected the frozen definitions
`IsPrimaryOnStrip`, `IsRealOnReals`, `invarianceError` and `IsDiophantine`, and the landed
clock, physical Hamiltonian, barrier, isoenergetic output and frequency-scaling interfaces.
There is no local SO statement file or SO frozen theorem surface to compare.

**Signed declaration equality and provider/frozen seal probes: not applicable.** Neither new endpoint
is in SOSignatures §I (1396–1432). That section signs the certificate client
`SoGraphCert`, `checkSoGraph`, `soBarrier_of_cert` and the already-landed `SoBarrier`.
Design §6 (422–423, 454, 466) explicitly assigns the pre-gate exact-torus inversion to
`Graph/Inverse` and the later certificate-to-barrier pipeline to `Graph/Cert`.
No signed declaration was substituted or renamed by this patch.

The assigned exact-torus slice is complete: global surjectivity and unique inversion at every
real clock phase, joint inverse continuity, both shift laws, a continuous doubly periodic momentum
graph, uniform real bounds, and invariance in precisely SO-CONF's `SoBarrier` sense
(`KAM/SpinOrbit/Barrier.lean:37–44`). The invariance proof compares every solution on every
allowed ordered-connected time interval with the constructed torus orbit by `gen_uniqueness`;
it is not restricted to one phase or forward time.

`g1_explicit` (`KAM/Iso/Apost/G1.lean:95`) returns `Charts.IG1Body`
(`KAM/Iso/Charts/Inputs.lean:69–80`), giving holomorphy, primary/realness and exact invariance
at `sinf • ωstar`, with `1 < sinf`; its final strip width is positive by its input.
Its source Diophantine premise is on `ωstar`. The fresh integration probe obtains the required
same-γ, same-τ scaled premise by `KAM.Iso.Linear.isDiophantine_smul hdio hs.le`, then applies
the actual new endpoint. The positive slope margin and momentum bounds remain explicit geometric
inputs, owned by the later certificate/Cauchy-transfer package, not consequences silently attributed
to G1. No certificate theorem or Cauchy-transfer inequality is certified here.

At Inverse 365–375, `fderiv_soHC_apply` proves `∂J soHC = 1` on `univ`;
`clock_frequency` at j=1 derives `sinf * ωstar 1 = 1` and `φ = y+c`.
The module does not assume these identities or divide by an unproved nonzero coordinate.
The real torus bundle assumes source continuity, periods, slope and physical flow equations,
not graph existence or graph invariance. No extra conclusion-shaped hypothesis, energy condition,
immersion assumption, twist or irrationality premise is introduced into the exact-torus slice.

## Declaration review

All rows implement the design's exact-torus inversion node; helpers have no separate signed nodes.
Line numbers refer to the audited source at HEAD. PASS rows concern each declaration;
the naming failure still blocks package acceptance.

| Node / line | Fully qualified declaration | Verdict | Reason |
|---|---|---|---|
| exact-torus / 39 | `KAM.SpinOrbit.SoGraph.mul_sub_le` | PASS | Derivative lower bound gives global linear growth. |
| exact-torus / 47 | `KAM.SpinOrbit.SoGraph.graphAbs_sub_le` | PASS | Handles both argument orders with positive m. |
| exact-torus / 61 | `KAM.SpinOrbit.SoGraph.soStrictMono` | PASS | Positive slope gives strict monotonicity; old short name removed. |
| exact-torus / 69 | `KAM.SpinOrbit.SoGraph.Torus` | PASS | Source data only: continuity, periods, slope and flow equations. |
| exact-torus / 84 | `KAM.SpinOrbit.SoGraph.Torus.Q_add_int` | PASS | All positive and negative integer translations. |
| exact-torus / 97 | `KAM.SpinOrbit.SoGraph.Torus.contQ_left` | PASS | Continuity on every real spatial slice. |
| exact-torus / 100 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_exists` | PASS | IVT between integer translates, for every q and phase. |
| exact-torus / 111 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_unique` | PASS | Positive-slope estimate gives uniqueness. |
| exact-torus / 119 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv` | PASS | Choice from proved existence on the whole carrier. |
| exact-torus / 122 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_spec` | PASS | Inverse equation holds everywhere. |
| exact-torus / 126 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_apply` | PASS | Uniqueness recovers every original torus parameter. |
| exact-torus / 132 | `KAM.SpinOrbit.SoGraph.Torus.continuous_soGraphInv` | PASS | Joint continuity from the uniform positive-slope estimate. |
| exact-torus / 165 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_add_one` | PASS | Spatial lift equivariance from uniqueness. |
| exact-torus / 170 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_periodic_φ` | PASS | Clock periodicity from uniqueness. |
| exact-torus / 178 | `KAM.SpinOrbit.SoGraph.Torus.graph` | FAIL (naming) | Correct momentum composed with inverse; reused Mathlib short name. |
| exact-torus / 180 | `KAM.SpinOrbit.SoGraph.Torus.continuous_graph` | PASS | Joint continuity by composition. |
| exact-torus / 185 | `KAM.SpinOrbit.SoGraph.Torus.graph_apply` | PASS | Graph agrees with original torus at every real parameter. |
| exact-torus / 191 | `KAM.SpinOrbit.SoGraph.graphHasDerivAt_line` | PASS | Moves source derivative from zero to every time; wrapped header. |
| exact-torus / 200 | `KAM.SpinOrbit.SoGraph.Torus.orbit` | FAIL (naming) | Actual physical trajectory at arbitrary initial time; reused Mathlib/KAM short name. |
| exact-torus / 204 | `KAM.SpinOrbit.SoGraph.Torus.hasDerivAt_orbit` | PASS | All three physical flow components verified at every time. |
| exact-torus / 217 | `KAM.SpinOrbit.SoGraph.Torus.orbit_mem` | PASS | Every explicit torus orbit stays in the graph. |
| exact-torus / 222 | `KAM.SpinOrbit.SoGraph.Torus.invariant` | FAIL (naming) | ODE uniqueness proves exact IsInvariantSet; reused Mathlib theorem short name. |
| exact-torus / 249 | `KAM.SpinOrbit.soBarrier_of_torus` | PASS | All seven landed SoBarrier fields constructed with the stated bounds. |
| exact-torus / 277 | `KAM.SpinOrbit.SoGraph.realPt` | PASS | Canonical Fin 2 real-to-complex embedding. |
| exact-torus / 280 | `KAM.SpinOrbit.SoGraph.realQ` | PASS | Actual q-coordinate real part on the whole carrier. |
| exact-torus / 284 | `KAM.SpinOrbit.SoGraph.realP` | PASS | Actual p-coordinate real part on the whole carrier. |
| exact-torus / 287 | `KAM.SpinOrbit.SoGraph.realPt_mem` | PASS | All real points belong to every positive-width strip. |
| exact-torus / 290 | `KAM.SpinOrbit.SoGraph.real_comp` | PASS | Unpacks the frozen realness predicate without strengthening it. |
| exact-torus / 294 | `KAM.SpinOrbit.SoGraph.realQ_eq` | PASS | Realness reconstructs complex q from its real part. |
| exact-torus / 300 | `KAM.SpinOrbit.SoGraph.realP_eq` | PASS | Realness reconstructs complex p from its real part. |
| exact-torus / 307 | `KAM.SpinOrbit.SoGraph.graphHasDerivAt_lineK` | PASS | Holomorphic derivative restricted to every real line. |
| exact-torus / 322 | `KAM.SpinOrbit.SoGraph.realPt_line` | PASS | Coordinate identity along physical frequency (ν,1). |
| exact-torus / 326 | `KAM.SpinOrbit.SoGraph.realPt_zero_line` | PASS | Coordinate identity along the spatial direction. |
| exact-torus / 331 | `KAM.SpinOrbit.SoGraph.hasDerivAt_re_comp` | PASS | First-coordinate derivative projected to its real part. |
| exact-torus / 337 | `KAM.SpinOrbit.SoGraph.hasDerivAt_re_comp₂` | PASS | Action-coordinate derivative projected to its real part. |
| exact-torus / 352 | `KAM.SpinOrbit.soBarrier_of_exact_torus` | PASS | Landed clock lemma supplies clock identity; exact real barrier returned. |

## Definition classification

Seven new object declarations, all exposed by `@[expose] public noncomputable section`:

- `SoGraph.Torus`: Prop-valued source-data structure; no inverse or invariant-graph field.
- `Torus.soGraphInv`: Classical choice from proved existence for all real q and φ; independent
  uniqueness proof, no fallback or junk branch.
- `Torus.graph`: actual momentum at the inverse torus parameter and shifted clock phase.
- `Torus.orbit`: explicit physical trajectory with arbitrary initial time; unused proof bundle
  argument is harmless.
- `realPt`: canonical embedding of real Fin 2 coordinates into complex coordinates.
- `realQ`, `realP`: actual coordinate real parts for every input Kinf; complex reconstruction
  uses the separately stated realness predicate exactly where needed.

No new abbreviation, hidden instance, substituted object or numerical fallback.

## Independent validation

All Lean/Lake commands below ran serially, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No full build, clean, cache fetch, package mutation or state-changing git command was used.
Only the report and temporary `.lake/abi-scratch/` probes/logs were written by this auditor.

1. Targeted compile gate, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sographm KAM.SpinOrbit.Graph.Inverse
[inp-gate] slot 1 acquired 14:20:54 for KAM.SpinOrbit.Graph.Inverse
⚠ [3191/3203] Replayed KAM.ODE.Exit
warning: KAM/ODE/Exit.lean:36:0: automatically included section variable(s) unused in theorem `KAM.ODE.gen_exit`:
  [NormedSpace ℝ E]
Build completed successfully (3203 jobs).
```

The replayed dependency warning is outside this source; no warning in Inverse.

2. Axiom and endpoint-type probe, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOGraphMAudit2.lean
'KAM.SpinOrbit.SoGraph.mul_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.graphAbs_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.soStrictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.Q_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.contQ_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soGraphInv_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soGraphInv_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soGraphInv_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soGraphInv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.continuous_soGraphInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soGraphInv_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soGraphInv_periodic_φ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.continuous_graph' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.graph_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.graphHasDerivAt_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.hasDerivAt_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.orbit_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.realPt_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.real_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.realQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.realP_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.graphHasDerivAt_lineK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.realPt_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.realPt_zero_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.hasDerivAt_re_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.hasDerivAt_re_comp₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_exact_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This queries all 29 new public theorems, not just the two endpoints. It also prints the actual
endpoint types. All dependencies are within the brief's permitted axiom set.
One exploratory `#check SetRel.graph` resolved to an application of `Function.graph`, rather
than a constant of that name; it is not evidence for a `SetRel.graph` declaration. The independent
integration probe correctly checks `Function.graph` and supplies the naming evidence used above.

3. Kernel replay, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Graph.Inverse
replaying KAM.SpinOrbit.Graph.Inverse
```

4. Integration/name-resolution probe, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOGraphMIntegration2.lean
Function.graph.{u_1, u_2} {α : Type u_1} {β : Type u_2} (f : α → β) : SetRel α β
MulAction.orbit.{u_2, u_3} (γ : Type u_2) {α : Type u_3} [SMul γ α] (a : α) : Set α
```

The source-derived application described above elaborates. Opening `SoGraph.Torus` in separate
queries prints `KAM.SpinOrbit.SoGraph.Torus.graph` and `.orbit`, confirming the actual helper names.

5. Static/import/protected-path checks: 448 lines; maximum 99 Unicode characters; correct
copyright, module header, public imports, docstring and public exposed section. No forbidden
proof escape, resource override, `EuclideanSpace` or `native_decide` token. Recursive KAM import
walk visits 52 modules and no provider or frozen theorem anchor. Frozen definition imports are
permitted; no theorem-state seal check is applicable.

`git diff --check inp...HEAD` and `git diff --check` pass.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.

6. Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1292 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
LINT_EXIT=1
```

The only lint complaint is the explicitly permitted stale generated root. Module structure,
frozen-anchor guard and all 144 elaborated ABI hashes pass. Line-length lint now passes;
no source or generated-file repair was performed. This lint exception does not waive the
separate helper-name requirement.

All audit-created scratch probes and logs were removed after transcribing the receipts. Final
`git diff --check` passed and protected-path differences remained empty. The only persistent
auditor addition is this report.

## Defects, uncertainty and deviations

No suspected pinned-source or blueprint defect found. No frozen statement defect, hypothesis
repair or mathematical deviation introduced. The remaining naming violation is a deviation from
the explicit audit focus; the handoff's short-name claim is inaccurate. The stale generated root
is governed by the brief's explicit exception and must not be regenerated during this audit.

This report certifies the exact-torus core only. The signed certificate consumer, Cauchy transfer,
candidate range widening, lunar numerical checks and final confinement application remain outside
this package. No production source was repaired by the auditor.
