# SO-GRAPHM independent audit 3

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-sographm`.
Audited HEAD: `2819408977ec58b79246a2875cfdc0a8dee6e565`.
Live comparison branch `inp`: `b59aecd164d64fdf27bf6cd842aba325161e7d81`.
Merge base: `a9ea7f5ba1625446b8a5ba4a408bc32e51800abe`.
Reviewed the full `git diff inp...HEAD`; sole production change is the new 448-line
`KAM/SpinOrbit/Graph/Inverse.lean`. Other changes are the handoff and audits 1 and 2.
The explicit user destination overrides the generic brief's main-worktree destination.

## Verdict

**PASS WITH NOTES for SO-GRAPHM. Round-3 public naming findings: CLOSED.**
Both `KAM.SpinOrbit.soBarrier_of_torus` and
`KAM.SpinOrbit.soBarrier_of_exact_torus` pass independent statement/proof review,
axiom checks, targeted build, consumer elaboration and kernel replay.
No frozen anchor or provider export is implemented here; frozen-type equality and
seal-body probes are not applicable, and this is not an anchor seal-readiness claim.

No statement or proof changed beyond consistent helper renaming. All 36 explicitly
written public declaration short names are distinct from other public declaration
headers in KAM and Mathlib. No harmful root shadow was found. All source lines have
at most 100 Unicode characters; module structure and the inverse docstring are correct.

The notes are scope and the brief's permitted generated-root lint exception.
The certificate client and Cauchy transfer are still later work, as the design assigns.

## Round-3 repair and naming evidence

Independently compared `git diff a637d023..HEAD -- KAM/SpinOrbit/Graph/Inverse.lean`
and `git diff inp...HEAD`. Applied exactly the seven identifier replacements below
to `git show a637d023:KAM/SpinOrbit/Graph/Inverse.lean`, then removed comments and
whitespace from that source and current source and compared the entire code:

```text
graph -> soGraphFun
continuous_graph -> continuous_soGraphFun
graph_apply -> soGraphFun_apply
orbit -> soOrbit
hasDerivAt_orbit -> hasDerivAt_soOrbit
orbit_mem -> soOrbit_mem
invariant -> soGraph_invariant
RENAME_NORMALIZED_CODE_IDENTICAL True
DECLARATIONS 36 THEOREMS 29
LINES 448 MAX_CHARS 100
FORBIDDEN []
TRANSITIVE_KAM_IMPORTS 52
QUARANTINE_IMPORTS []
```

Thus all binder orders, hypotheses, conclusions, constants, definition bodies and
proof steps are preserved under this identifier map. Both public endpoint names
and their statements are literally unchanged.

A separate Python scan used `scripts/check_lean_modules.py`'s `code_mask`, then
matched declaration headers for theorem/lemma/def/abbrev/structure/class/instance,
including qualified names and visibility modifiers, and compared final name
components in every other KAM and Mathlib Lean file. It returned:

```text
SCANNED_OTHER_FILES 9913 EXPLICIT_PUBLIC_NAMES 36
PUBLIC_SHORT_NAME_COLLISIONS []
PRIVATE_ONLY_MATCHES [('KAM/Canonical/CompositionCoeff.lean', 'realPt_mem')]
```

The match is explicitly `private theorem realPt_mem` at
`KAM/Canonical/CompositionCoeff.lean:38`. It is not a public helper collision and
therefore does not violate the focus. The handoff's literal claim that *every*
declaration-header scan has no match is slightly too broad if private headers are
included. Its substantive claim about public short names is verified. No further
rename is required by the stated public-name rule. This is a source-header scan,
not a claim about every automatically generated projection name in the environment.

## Authority, fidelity and completeness

Read current `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied package
brief, SO-GRAPHM handoff including ROUND 3 FOCUS, and audit 2. Checked Revision 4
`/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md` §6,
`/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md` (including O4), and
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §I (1396–1432).
Read the relevant Track-I statement context and searched blueprint-I for a separate
SO graph node; there is no dedicated SO statement file or frozen graph theorem.
Reviewed the frozen `IsPrimaryOnStrip`, `IsRealOnReals`, `invarianceError` and
`IsDiophantine` definitions and the landed clock, Hamiltonian, barrier, IG1 output
and frequency-scaling interfaces.

The exact-torus endpoints are **unfrozen helpers**, not signed declarations in
SOSignatures §I. That section signs `SoBarrier`, `SoGraphCert`, `checkSoGraph` and
`soBarrier_of_cert`; none is introduced or substituted here. Design §6 explicitly
assigns the pre-gate exact-torus inversion to `Graph/Inverse` (422, 454) and the
certificate consumer to `Graph/Cert` (423, 466). Signed-declaration equality is
therefore not applicable to the new declarations. Requiring the certificate
consumer in this package would exceed its assigned slice.

The real-variable proof establishes global existence and uniqueness of the inverse
for **every** real spatial coordinate and clock phase. The quantitative inequality
`m * |x' - x| ≤ |Q x' y - Q x y|` proves inverse uniqueness and joint continuity.
Both shift laws are proved. The graph is continuous, doubly periodic and takes
values in the original `[lo, hi]`. Inverse choice has no junk branch.

At Inverse 222–238, an arbitrary solution on an arbitrary ordered-connected time
set is compared with the explicit torus orbit through its graph point, by
`KAM.ODE.gen_uniqueness`. This proves precisely `IsInvariantSet`
(`KAM/ODE/Exit.lean:107–109`), for every allowed initial and final time, with no
forward-time or fixed-phase restriction. The endpoint constructs all seven fields
of the actual `SoBarrier` (`KAM/SpinOrbit/Barrier.lean:37–44`).

For the complex bridge, `fderiv_soHC_apply` proves `∂J soHC = 1` on `univ`
(Inverse 365–370), and the landed `clock_frequency` at j=1 derives
`sinf * ωstar 1 = 1` and `φ = y + c`. These facts are not extra assumptions.
Holomorphy and positive strip width give derivatives at every real point;
primary equivariance and realness give the real periods and physical equations.
No division by an unproved nonzero coordinate, energy constraint, immersion,
twist or new irrationality premise is smuggled into this slice.

`KAM.Iso.Apost.g1_explicit` (G1.lean:95) supplies `IG1Body`
(`KAM/Iso/Charts/Inputs.lean:69–80`): holomorphy, primary/realness, exact invariance
at `sinf • ωstar`, and `1 < sinf` on a positive-width final strip. Its original
Diophantine premise on `ωstar` yields the required same-γ, same-τ scaled premise
by `KAM.Iso.Linear.isDiophantine_smul hdio hs.le`. A fresh elaborated consumer
probe applies this scaling lemma and the actual new endpoint together.

The positive slope and momentum bounds are explicit geometric source premises,
not consequences claimed from G1 alone. Their certificate/Cauchy transfer, the
`mono > disp/ρ∞` inequality, range widening, numerical witnesses and the final
confinement application remain outside this exact-torus package. The later
rotated-frame lunar client in the current plan is likewise not certified here;
these generic physical-coordinate lemmas remain valid for their stated `soHC`.
No conclusion-shaped hypothesis or unproved graph field is present in `Torus`.

## Declaration review

Each row implements the design's exact-torus node. Helpers have no separate signed
blueprint statement. Fully qualified names and current source lines follow.

| Node / line | Lean declaration | Verdict | Reason |
|---|---|---|---|
| exact-torus / 39 | `KAM.SpinOrbit.SoGraph.mul_sub_le` | PASS | Derivative lower bound gives global linear growth. |
| exact-torus / 47 | `KAM.SpinOrbit.SoGraph.graphAbs_sub_le` | PASS | Both argument orders handled with positive slope. |
| exact-torus / 61 | `KAM.SpinOrbit.SoGraph.soStrictMono` | PASS | Positive slope implies strict monotonicity. |
| exact-torus / 69 | `KAM.SpinOrbit.SoGraph.Torus` | PASS | Source continuity, periods, derivative and flow equations only. |
| exact-torus / 84 | `KAM.SpinOrbit.SoGraph.Torus.Q_add_int` | PASS | All integer spatial translations, including negative integers. |
| exact-torus / 97 | `KAM.SpinOrbit.SoGraph.Torus.contQ_left` | PASS | Continuity on every real spatial slice. |
| exact-torus / 100 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_exists` | PASS | IVT gives surjectivity for every q and clock phase. |
| exact-torus / 111 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_unique` | PASS | Positive-slope bound gives uniqueness. |
| exact-torus / 119 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv` | PASS | Choice from proved global existence; no fallback. |
| exact-torus / 122 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_spec` | PASS | Inverse equation holds on the whole carrier. |
| exact-torus / 126 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_apply` | PASS | Unique inverse recovers every torus parameter. |
| exact-torus / 132 | `KAM.SpinOrbit.SoGraph.Torus.continuous_soGraphInv` | PASS | Joint continuity from uniform positive slope and continuity of Q. |
| exact-torus / 165 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_add_one` | PASS | Spatial equivariance follows from uniqueness. |
| exact-torus / 170 | `KAM.SpinOrbit.SoGraph.Torus.soGraphInv_periodic_φ` | PASS | Clock periodicity follows from uniqueness. |
| exact-torus / 178 | `KAM.SpinOrbit.SoGraph.Torus.soGraphFun` | PASS | Actual momentum composed with global inverse; distinctive new name. |
| exact-torus / 180 | `KAM.SpinOrbit.SoGraph.Torus.continuous_soGraphFun` | PASS | Joint continuity by composition; rename only. |
| exact-torus / 185 | `KAM.SpinOrbit.SoGraph.Torus.soGraphFun_apply` | PASS | Graph agrees with source torus everywhere; rename only. |
| exact-torus / 191 | `KAM.SpinOrbit.SoGraph.graphHasDerivAt_line` | PASS | Moves time-zero flow equation to every real time. |
| exact-torus / 200 | `KAM.SpinOrbit.SoGraph.Torus.soOrbit` | PASS | Explicit physical trajectory with arbitrary initial time; rename only. |
| exact-torus / 204 | `KAM.SpinOrbit.SoGraph.Torus.hasDerivAt_soOrbit` | PASS | All three physical differential equations at every time; rename only. |
| exact-torus / 217 | `KAM.SpinOrbit.SoGraph.Torus.soOrbit_mem` | PASS | Explicit trajectory stays in the graph; rename only. |
| exact-torus / 222 | `KAM.SpinOrbit.SoGraph.Torus.soGraph_invariant` | PASS | ODE uniqueness proves the exact landed invariant-set predicate; rename only. |
| exact-torus / 249 | `KAM.SpinOrbit.soBarrier_of_torus` | PASS | Constructs all seven SoBarrier fields, with original bounds. |
| exact-torus / 277 | `KAM.SpinOrbit.SoGraph.realPt` | PASS | Canonical real-to-complex embedding of Fin 2 coordinates. |
| exact-torus / 280 | `KAM.SpinOrbit.SoGraph.realQ` | PASS | Actual real q coordinate for every input Kinf. |
| exact-torus / 284 | `KAM.SpinOrbit.SoGraph.realP` | PASS | Actual real p coordinate for every input Kinf. |
| exact-torus / 287 | `KAM.SpinOrbit.SoGraph.realPt_mem` | PASS | All real points lie in every positive-width complex strip. |
| exact-torus / 290 | `KAM.SpinOrbit.SoGraph.real_comp` | PASS | Unpacks the frozen realness predicate without strengthening it. |
| exact-torus / 294 | `KAM.SpinOrbit.SoGraph.realQ_eq` | PASS | Realness reconstructs complex q from its real part. |
| exact-torus / 300 | `KAM.SpinOrbit.SoGraph.realP_eq` | PASS | Realness reconstructs complex p from its real part. |
| exact-torus / 307 | `KAM.SpinOrbit.SoGraph.graphHasDerivAt_lineK` | PASS | Holomorphic derivative restricts to every real line. |
| exact-torus / 322 | `KAM.SpinOrbit.SoGraph.realPt_line` | PASS | Coordinate identity along the physical frequency (nu,1). |
| exact-torus / 326 | `KAM.SpinOrbit.SoGraph.realPt_zero_line` | PASS | Coordinate identity along the first spatial direction. |
| exact-torus / 331 | `KAM.SpinOrbit.SoGraph.hasDerivAt_re_comp` | PASS | Projects derivative to the real q coordinate. |
| exact-torus / 337 | `KAM.SpinOrbit.SoGraph.hasDerivAt_re_comp₂` | PASS | Projects derivative to the real p coordinate. |
| exact-torus / 352 | `KAM.SpinOrbit.soBarrier_of_exact_torus` | PASS | Clock lemma plus real bridge yields the actual SoBarrier. |

## Definition classification

Seven new objects, all covered by `@[expose] public noncomputable section`:

- `SoGraph.Torus`: Prop-valued bundle of source continuity, periods, slope and flow data;
  no inverse, graph-existence or graph-invariance conclusion field.
- `Torus.soGraphInv`: classical choice from existence proved for all real inputs,
  with separately proved uniqueness and inverse equations; no fallback.
- `Torus.soGraphFun`: actual source momentum at the inverse spatial parameter and shifted phase.
- `Torus.soOrbit`: explicit physical flow trajectory; the unused proof-bundle argument is harmless.
- `realPt`: canonical real-to-complex Fin 2 embedding on its entire carrier.
- `realQ`, `realP`: actual coordinate real parts for arbitrary Kinf; complex reconstruction
  uses the separately stated realness premise where required.

No new abbreviation or instance and no substituted object.

## Independent checks

All Lean/Lake commands ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`.
Lint was started only after kernel replay and both Lean probes had exited.
Only this report and audit-prefixed scratch files under `.lake/abi-scratch/` were
written; no production edits, full build, clean, package mutation or state-changing git.

Targeted build, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sographm KAM.SpinOrbit.Graph.Inverse
[inp-gate] slot 1 acquired 14:33:05 for KAM.SpinOrbit.Graph.Inverse
⚠ [3191/3203] Replayed KAM.ODE.Exit
warning: KAM/ODE/Exit.lean:36:0: automatically included section variable(s) unused in theorem `KAM.ODE.gen_exit`:
  [NormedSpace ℝ E]
Build completed successfully (3203 jobs).
```

The warning is in a replayed dependency; no warning in the audited module.

Axiom and endpoint-type probe, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOGraphMAudit3.lean
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
'KAM.SpinOrbit.SoGraph.Torus.continuous_soGraphFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soGraphFun_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.graphHasDerivAt_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.hasDerivAt_soOrbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soOrbit_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.soGraph_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
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

This queried all 29 public theorems, and `#check @...` printed both actual endpoint
types. All axiom sets are exactly the permitted `[propext, Classical.choice, Quot.sound]`.

Kernel replay, exit **0**:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Graph.Inverse
replaying KAM.SpinOrbit.Graph.Inverse
```

Consumer probe, exit **0**, no output:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOGraphMIntegration3.lean
```

The probe imports Inverse and Iso.Linear.Tools, uses the exact endpoint signature
with the input premise changed to `IsDiophantine γ τ ωstar` plus `1 < sinf`, and
closes by the actual endpoint after applying `isDiophantine_smul hdio hs.le`.
This validates the G1-output interface described above; it does not independently
rerun a numerical certificate or supply the outstanding geometric bounds.

The 448-line source has the required copyright, module keyword, three public
imports, module docstring and exposed public section. Maximum line length is 100.
Static code scan finds no proof escapes, resource overrides, `EuclideanSpace` or
`native_decide`. Recursive KAM imports visit 52 modules with no provider or frozen
theorem anchor; imported frozen definitions are permitted.

`git diff --check inp...HEAD` and `git diff --check`: exit **0**, no output.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.

Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1292 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
LINT_EXIT=1
```

The only lint complaint is the explicitly permitted stale generated `KAM.lean`.
Module checks, frozen-anchor guard and all 144 ABI hashes pass. No regeneration
was performed.

## Defects, uncertainty and deviations

No suspected pinned-source, blueprint or frozen-statement defect found in this scope.
No hypothesis repair, mathematical deviation or production fix introduced.
The private-name match qualifies the handoff's overbroad scan description only;
the required public-name hygiene is satisfied. The generated-root exception is
explicitly authorized by the audit brief and does not justify modifying KAM.lean.
The exact-torus core is complete; the separate signed certificate pipeline and
final lunar application remain unverified by this report.

All audit-created probes and logs are removed after recording the receipts.
Final report-path, whitespace and protected-path checks are recorded below.

Final verification: report exists at the exact requested absolute path;
`git diff --check inp...HEAD` and `git diff --check` exit 0;
protected-path comparison remains empty. Worktree status contains only
`?? docs/tracks/SO/audits/SO-GRAPHM-audit-3.md`. No other persistent auditor change.
