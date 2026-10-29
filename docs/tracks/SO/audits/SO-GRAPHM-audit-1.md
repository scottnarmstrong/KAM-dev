# SO-GRAPHM independent audit 1

Audit date: 2026-10-29. Checkout: `/root/code/KAM-inp-sographm`, HEAD `032b279f`.
Scope: **only** `KAM/SpinOrbit/Graph/Inverse.lean`; compare `git diff inp...HEAD`.
The user's exact report destination overrides the generic brief's MAIN-worktree destination.

## Verdict

**FAIL package hygiene; mathematical exact-torus slice PASS WITH NOTES.** No frozen anchor is proved or sealed by this package, and no provider export is introduced. Both `KAM.SpinOrbit.soBarrier_of_torus` and `KAM.SpinOrbit.soBarrier_of_exact_torus` pass proof review, elaboration, axiom inspection and kernel replay. Do not accept the package against the explicit audit focus until the line-length and reused-helper-name requirements below are resolved.

1. **Line-length violation:** `KAM/SpinOrbit/Graph/Inverse.lean:189` has **102 Unicode characters**, exceeding 100. The handoff says "No lines > 100 columns" and "only complaint KAM.lean is out of date"; neither matches this checkout. Split this theorem header. This is a substantive lint failure beyond the permitted stale-root exception.
2. **Reused public helper short names:** the focus explicitly requires "no reused public HELPER short name". At least `Torus.inv_unique` (111), `Torus.continuous_inv` (130), `Torus.inv_apply` (125), `Torus.inv_spec` (122), `Torus.exists_inv` (100), and `SoGraph.strictMono` (61) reuse existing Mathlib declaration short names. In particular Mathlib has root `inv_unique` in `Mathlib/Algebra/Group/Basic.lean:225` and `ContinuousInv.continuous_inv` exported as `continuous_inv` in `Mathlib/Topology/Algebra/Group/Defs.lean:51–55`. A Lean probe confirms `open KAM.SpinOrbit.SoGraph.Torus in #check inv_unique` resolves to the newly introduced helper, whereas `_root_.inv_unique` remains the algebra theorem. Thus the stated literal naming restriction is not satisfied, although the fully qualified declarations are distinct and no unsoundness follows. Rename affected helpers with distinctive names or obtain an explicit narrowing of this rule. The earlier renames to `graphAbs_sub_le` and `graphHasDerivAt_line(K)` are present.

## Authority, signatures and completeness

Read repository `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied package audit brief and handoff; the live Revision 4 design `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md`; the main plan `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`; and `/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §I. There is no local `docs/tracks/SO/statement.md` and no SO frozen theorem surface to compare. Relevant frozen definitions inspected: `IsPrimaryOnStrip`, `IsRealOnReals`, `InvarianceError`, `IsDiophantine` (and their carriers/imports).

**Signed declaration equality: not applicable in this module.** SOSignatures lines 1396–1432 signs the client surface `SoGraphCert`, `checkSoGraph`, `soBarrier_of_cert` (plus `SoBarrier`, which is already landed in Barrier). Neither new barrier theorem in Inverse occurs in that signed surface. Revision 4 design lines 422–423 and 454/466 explicitly split pre-gate `Graph/Inverse` (exact torus ⇒ graph) from post-gate `Graph/Cert` (certificate ⇒ barrier). Hence no signed declaration was silently replaced, but this report does **not** certify `soBarrier_of_cert` or the full certificate pipeline. Frozen/provider type-equality and seal-body probes are inapplicable, rather than counted as passes.

The assigned exact-torus inversion slice is complete: for every real clock phase it proves surjectivity, uniqueness, joint inverse continuity, both shift laws, physical-flow invariance, and the exact `SoBarrier lo hi` required by SO-CONF. The design's `mono > disp/ρinf` Cauchy transfer and candidate p-range widening are explicitly the later SO-GRAPH/Cert responsibility. They remain unpaid by this module and must not be inferred from its successful build.

### Compatibility with g1_explicit and clock

`KAM.Iso.Apost.g1_explicit` (`KAM/Iso/Apost/G1.lean:95`) returns `Charts.IG1Body`; its body (`KAM/Iso/Charts/Inputs.lean:69–80`) supplies positive final strip width from the theorem input, `1 < sinf`, holomorphy, primary/realness and exact invariance at `sinf • ωstar`. Its source premise is Diophantine on `ωstar`. This implies the new theorem's Diophantine premise on `sinf • ωstar` with the **same γ,τ**, by landed `KAM.Iso.Linear.isDiophantine_smul hdio hs.le` (`KAM/Iso/Linear/Tools.lean:38`). The integration probe elaborates precisely this application, retaining the three separately owed geometric inputs `m > 0`, the derivative lower bound, and lower/upper real momentum bounds.

`soBarrier_of_exact_torus:363–373` derives `∂J soHC = 1` on `univ` using `fderiv_soHC_apply`, then applies the actual landed `clock_frequency` at j=1. It derives `sinf * ωstar 1 = 1`, `φ=y+c`, and frequency `(ν,1)`; no separately assumed clock identity or conclusion-shaped graph premise is inserted. No division by an unproved nonzero coordinate is used. The exact-torus theorem imposes no energy, immersion, twist, extra regularity, or irrationality premise beyond what this step needs.

The real-data bundle `Torus` assumes the source flow equations and strict spatial slope, not graph existence or invariance. Its inversion is global in q and phase, not a single phase section. The proof constructs global torus orbits and compares arbitrary solutions using `gen_uniqueness`, so invariance is on all allowed connected time intervals and in both time directions. The returned carrier and all fields match landed `KAM/SpinOrbit/Barrier.lean:37–44` exactly.

## Declaration-by-declaration review

Line numbers refer to `KAM/SpinOrbit/Graph/Inverse.lean`. Helpers have no separately signed blueprint node; rows compare them with the exact-torus slice of design §6/§7. FAIL labels below concern hygiene, not theorem truth.

| Node / line | Fully qualified declaration | Verdict | Reason |
|---|---|---|---|
| exact-torus / 39 | `KAM.SpinOrbit.SoGraph.mul_sub_le` | PASS | Derivative lower bound implies linear growth; source hypotheses only. |
| exact-torus / 47 | `KAM.SpinOrbit.SoGraph.graphAbs_sub_le` | PASS | Both orders of the real arguments handled; positive m retained. |
| exact-torus / 61 | `KAM.SpinOrbit.SoGraph.strictMono` | FAIL (hygiene) | Strict monotonicity follows from positive slope. Reuses a Mathlib helper short name (e.g. InitialSeg.strictMono). |
| exact-torus / 69 | `KAM.SpinOrbit.SoGraph.Torus` | PASS | Source data bundle: continuity, shift laws, derivative lower bound, and exact flow equations; no inverse or invariant-graph conclusion assumed. |
| exact-torus / 84 | `KAM.SpinOrbit.SoGraph.Torus.Q_add_int` | PASS | Positive and negative integer shifts proved. |
| exact-torus / 97 | `KAM.SpinOrbit.SoGraph.Torus.contQ_left` | PASS | Continuity on each entire real slice. |
| exact-torus / 100 | `KAM.SpinOrbit.SoGraph.Torus.exists_inv` | FAIL (hygiene) | IVT between consecutive integer translates; every q and every phase y. Reused short name exists_inv. |
| exact-torus / 111 | `KAM.SpinOrbit.SoGraph.Torus.inv_unique` | FAIL (hygiene) | Positive-slope estimate proves uniqueness. Reuses root inv_unique (Mathlib/Algebra/Group/Basic.lean:225). |
| exact-torus / 119 | `KAM.SpinOrbit.SoGraph.Torus.inv` | PASS | Classical choice from proved existence; defined on every q,φ without fallback. |
| exact-torus / 122 | `KAM.SpinOrbit.SoGraph.Torus.inv_spec` | FAIL (hygiene) | Chosen inverse equation at every q,φ. Reused short name inv_spec (Mathlib/Topology/Homotopy/HomotopyGroup.lean:598). |
| exact-torus / 125 | `KAM.SpinOrbit.SoGraph.Torus.inv_apply` | FAIL (hygiene) | Uniqueness identifies original parameter. Reused short name inv_apply (e.g. Pi.inv_apply). |
| exact-torus / 130 | `KAM.SpinOrbit.SoGraph.Torus.continuous_inv` | FAIL (hygiene) | Joint continuity via m times inverse-distance estimate. Reuses ContinuousInv.continuous_inv, exported as continuous_inv. |
| exact-torus / 163 | `KAM.SpinOrbit.SoGraph.Torus.inv_add_one` | PASS | Lift equivariance follows from uniqueness. |
| exact-torus / 168 | `KAM.SpinOrbit.SoGraph.Torus.inv_φ_add_one` | PASS | Every clock phase handled; unit-periodicity follows from uniqueness. |
| exact-torus / 176 | `KAM.SpinOrbit.SoGraph.Torus.graph` | PASS | Actual momentum composed with the inverse and φ-c. |
| exact-torus / 178 | `KAM.SpinOrbit.SoGraph.Torus.continuous_graph` | PASS | Joint composition of continuous maps. |
| exact-torus / 183 | `KAM.SpinOrbit.SoGraph.Torus.graph_apply` | PASS | Graph agrees with original torus at all real parameters. |
| exact-torus / 189 | `KAM.SpinOrbit.SoGraph.graphHasDerivAt_line` | FAIL (hygiene) | Flow derivative moved from time zero to arbitrary time; line 189 has 102 characters. |
| exact-torus / 198 | `KAM.SpinOrbit.SoGraph.Torus.orbit` | PASS | Actual physical orbit at frequency (ν,1), with arbitrary time origin. |
| exact-torus / 202 | `KAM.SpinOrbit.SoGraph.Torus.hasDerivAt_orbit` | PASS | All three physical field components verified at every real time. |
| exact-torus / 215 | `KAM.SpinOrbit.SoGraph.Torus.orbit_mem` | PASS | Entire torus orbit lies in graph. |
| exact-torus / 220 | `KAM.SpinOrbit.SoGraph.Torus.invariant` | PASS | gen_uniqueness gives exactly ODE.IsInvariantSet on univ for every OrdConnected solution interval. |
| exact-torus / 247 | `KAM.SpinOrbit.soBarrier_of_torus` | PASS | Constructs every SoBarrier field, including both periods, invariance and global bounds; unsigned exact-torus helper. |
| exact-torus / 275 | `KAM.SpinOrbit.SoGraph.realPt` | PASS | Canonical real embedding (x,y) into complex Fin 2 coordinates. |
| exact-torus / 278 | `KAM.SpinOrbit.SoGraph.realQ` | PASS | Real part of q-coordinate at the real point, on its whole carrier. |
| exact-torus / 282 | `KAM.SpinOrbit.SoGraph.realP` | PASS | Real part of p-coordinate at the real point, on its whole carrier. |
| exact-torus / 285 | `KAM.SpinOrbit.SoGraph.realPt_mem` | PASS | All real points lie in every positive-width strip. |
| exact-torus / 288 | `KAM.SpinOrbit.SoGraph.real_comp` | PASS | Unpacks frozen IsRealOnReals without strengthening it. |
| exact-torus / 292 | `KAM.SpinOrbit.SoGraph.realQ_eq` | PASS | Realness identifies complex q with its real part. |
| exact-torus / 298 | `KAM.SpinOrbit.SoGraph.realP_eq` | PASS | Realness identifies complex p with its real part. |
| exact-torus / 305 | `KAM.SpinOrbit.SoGraph.graphHasDerivAt_lineK` | PASS | Holomorphic derivative restricted to real scalars along any real line. |
| exact-torus / 320 | `KAM.SpinOrbit.SoGraph.realPt_line` | PASS | Coordinate identity for the flow line. |
| exact-torus / 324 | `KAM.SpinOrbit.SoGraph.realPt_zero_line` | PASS | Coordinate identity for the first-coordinate direction. |
| exact-torus / 329 | `KAM.SpinOrbit.SoGraph.hasDerivAt_re_comp` | PASS | Continuous linear projection of angle derivative. |
| exact-torus / 335 | `KAM.SpinOrbit.SoGraph.hasDerivAt_re_comp₂` | PASS | Continuous linear projection of action derivative. |
| exact-torus / 350 | `KAM.SpinOrbit.soBarrier_of_exact_torus` | PASS | Calls landed clock_frequency, derives all real-torus fields, and returns exact SoBarrier; remaining monotonicity/range inputs belong to Graph/Cert. |

## Definition classification

All seven new object declarations were inspected on their whole carriers:

- `SoGraph.Torus`: Prop-valued source-data structure, with no conclusion-shaped field.
- `Torus.inv`: Classical choice from proved existence for every real q,φ; uniqueness proved independently. No junk branch.
- `Torus.graph`: actual momentum at inverse parameter and shifted clock phase.
- `Torus.orbit`: explicit real physical trajectory at arbitrary initial time; its unused bundle argument is harmless.
- `realPt`: canonical real-to-complex Fin 2 map, not EuclideanSpace.
- `realQ`, `realP`: real coordinate projections of arbitrary Kinf; realness is separately used exactly where complex reconstruction requires it.

Bodies are exposed by the `@[expose] public noncomputable section`. There are no new abbreviations, hidden instances, numerical fallbacks, or substituted mathematical objects.

## Independent validation

All Lean/Lake invocations used `LEAN_NUM_THREADS=1` and `nice -n 5`, serially within this audit. No concurrent audit-owned Lean processes, full-library rebuild, cache update, or clean. Other sessions on the host are outside this audit's control.

1. Full `git diff inp...HEAD`: exactly one new source, 446 lines. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: **empty**, exit 0. `git diff --check inp...HEAD`: exit 0. The pre-existing untracked handoff was read and left unchanged.
2. Targeted compile gate:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sographm KAM.SpinOrbit.Graph.Inverse
[inp-gate] slot 1 acquired 12:37:17 for KAM.SpinOrbit.Graph.Inverse
⚠ [3191/3203] Replayed KAM.ODE.Exit
warning: KAM/ODE/Exit.lean:36:0: automatically included section variable(s) unused in theorem `KAM.ODE.gen_exit`:
  [NormedSpace ℝ E]
Build completed successfully (3203 jobs).
```

Exit 0. The replayed dependency warning is outside the audited source; no warning in Inverse.

3. Axiom probe: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOGraphMAudit.lean`, exit 0. It imports only Inverse, queries **all 29 new public theorems**, and prints both public endpoint types. Exact axiom output:

```text
'KAM.SpinOrbit.SoGraph.mul_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.graphAbs_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.Q_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.contQ_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.exists_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.inv_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.inv_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.inv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.continuous_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.inv_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.Torus.inv_φ_add_one' depends on axioms: [propext, Classical.choice, Quot.sound]
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

4. Kernel replay (one module covers both endpoints and all helpers):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Graph.Inverse
replaying KAM.SpinOrbit.Graph.Inverse
LEANCHECKER_EXIT=0
```

A first replay's tool session closed before its exit status was recoverable; the command was repeated serially with an explicit shell exit-code receipt. Only the latter is the claimed exit-0 receipt.

5. Integration and name-resolution probe: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOGraphMIntegration.lean`. The source-derived application supplies scaled Diophantine via the landed lemma; no certificate theorem or frozen anchor is imported. Final result and lint receipt below. An initial diagnostic query incorrectly addressed the exported alias as `_root_.continuous_inv`; corrected to `ContinuousInv.continuous_inv` before the final run. This diagnostic error did not affect the successful axiom or build probes.

6. Static source scan: 446 lines; maximum line length 102 at line 189. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, or `set_option` matches. Module header, copyright, public imports, module docstring and public exposed section present. A recursive import walk finds 52 KAM modules and **no provider or frozen theorem-anchor imports**, including transitively; manifest theorem state checks are consequently unnecessary. Frozen definition imports are permitted.

7. Integration probe final run: **exit 0**. Besides the source-derived application, its name queries printed:

```text
ContinuousInv.continuous_inv.{u} {G : Type u} {inst✝ : TopologicalSpace G} {inst✝¹ : Inv G} [self : ContinuousInv G] :
  Continuous fun a => a⁻¹
inv_unique.{u_4} {M : Type u_4} [CommMonoid M] {x y z : M} (hy : x * y = 1) (hz : x * z = 1) : y = z
ContinuousInv.continuous_inv.{u} {G : Type u} {inst✝ : TopologicalSpace G} {inst✝¹ : Inv G} [self : ContinuousInv G] :
  Continuous fun a => a⁻¹
KAM.SpinOrbit.SoGraph.Torus.inv_unique {Q dQ : ℝ → ℝ → ℝ} {m : ℝ} {Pp : ℝ → ℝ → ℝ} {ν c : ℝ}
  (T : SoGraph.Torus Q Pp dQ ν c m) {x x' y : ℝ} (h : Q x y = Q x' y) : x = x'
```

8. Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
Lean lines over 100 characters:
/root/code/KAM-inp-sographm/KAM/SpinOrbit/Graph/Inverse.lean:189:102
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1292 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
LINT_EXIT=1
```

**FAIL:** the stale generated root is allowed by the brief, but line 189 is not. No root regeneration or source repair was performed. The lint's ABI subprocess ran only after the integration probe and kernel replay finished; niceness and `LEAN_NUM_THREADS=1` were inherited.

Scratch probes and audit-created kernel/lint logs were removed after these receipts were transcribed. Final `git diff --check` passed; protected-path diff remained empty. Only this report was added by the auditor.


## Defects, uncertainties and deviations

No suspected defect in a pinned mathematical source was found; this package uses the design's elementary inversion/ODE route rather than a newly transcribed source theorem. No frozen declaration defect or statement repair is proposed. The two hygiene findings above are package deviations from the explicit focus; the handoff's lint and line-length claims are contradicted by the independent checks.

The module docstring at lines 21–23 advertises `soGraphInv`, `soGraphInv_spec`, `soGraphInv_unique`, `continuous_soGraphInv`, `soGraphInv_add_one`, `soGraphInv_periodic_φ`; the actual names are the `SoGraph.Torus.*` declarations tabulated above. Update that documentation during the hygiene repair. This is not a signed-signature mismatch.

No proof of the later signed certificate consumer, no Cauchy transfer, no candidate data verification and no final lunar barrier/confinement theorem is certified here. Those are outside this package's pre-gate slice. This audit changes only its report and temporary scratch probes; it does not edit Lean, generated files, frozen files, manifest, or git state.
