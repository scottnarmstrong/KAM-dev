# P12-C independent package audit 1

**Verdict: PASS WITH NOTES for the four-module P12-C infrastructure slice.** All five signed declarations match the authoritative signatures; the joint construction and its applicable source-characterization/delivery gates pass. No blocking mathematical or interface defect was found. This package supplies no provider and seals no frozen anchor. P-PLANAR, P-FIXED and P-G are not independently certified or sealed by this audit.

Audit date: 2026-10-29. Audited HEAD: `d775cfa33857efd3efd0725c8398516a0e7bc864`. Report destination is this package worktree, as explicitly required by the user, overriding the generic brief's main-worktree destination.

## Scope and comparison boundary

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the complete P12-C handoff including AUDIT FOCUS, the P1213 design characterization section and SOURCE_GAP disposition, both P1213 design audits, the P12 blueprint, the relevant track-P statement clauses and frozen predicates/root interfaces. Implementation ownership is limited to:

| File | Lines | SHA256 |
|---|---:|---|
| `KAM/Planetary/PlanarAssembly/ChartData.lean` | 72 | `bab1e17715823eed667f061b9c01e58f0464645b32bdab6584e686391a3a2cd9` |
| `KAM/Planetary/PlanarAssembly/SlowSmall.lean` | 138 | `38433b8c392a55a871955fac761a2aac4dd1bf789f34d798babf3834612625b7` |
| `KAM/Planetary/PlanarAssembly/DataBox.lean` | 83 | `da8ed209a9a477bc742dea65875c78df5825a8c45400e94ec933b5752c30f5a8` |
| `KAM/Planetary/PlanarAssembly/Data.lean` | 332 | `d8a727284f9b3a6ac9e5defe9ff28451d31d68cbaa6028ef3e27fa64a7f04694` |

Authoritative signature file: `/root/code/KAM-inp/.drafts/design/P1213Signatures.lean`, SHA256 `1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447`. Design SHA256: `da905471b106707950e1de2c433228a74a967117f81e07cd767a1c7ffea05768`. These match revision 2 reviewed in the existing design delta audit.

`git diff inp...HEAD` was captured in full and the four added module bodies reviewed in full. At the comparison, `inp` was `3fcfb654e1e10a82cc4ab57401156fc446225ce1`. Git warns that there are multiple merge bases and selects `294f2ea91804f097dbfaaf0ecb491105d5264e72`; the other bases returned by `git merge-base --all inp HEAD` are `f92e938abfd109ef2d7c98888b25dc25e2bf978d` and `e743c7e4d5495f5476da88acaffc298cf6b03b6e`. The selected three-dot diff contains 18 files, 2350 insertions and 80 deletions: the four scoped files plus inherited T20/T21, B16, graph/audit changes and six generated root imports. Those inherited implementations are not being re-audited as packages here; upstream exports used by P12-C were inspected for their types, proof route and axiom closure.

The literal protected-path check is **not empty**: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` shows only six `KAM.Planetary.WeakKAM.Tori*` root imports. They come from inherited commit `b327bf59` (`Regenerate KAM.lean (P11B-B16)`), not any of the four P12-C commits `e0516426`, `f1f1b099`, `f369d006`, `d775cfa3`. No frozen, manifest or README change occurs in this diff. This inherited root change is a recorded integration exception, not a falsely reported empty check. The generated root was not edited.

## Signed interfaces, construction and consumers

All five full commands/types were mechanically compared after whitespace normalization, including complete named arguments (not just text before a named-argument `:=`). Results:

```text
total_chart full command/signature equality True
perturbation full command/signature equality True
chart_of_birkhoff full command/signature equality True
chart_hamiltonian_of_preserves_fast full command/signature equality True
pg_hypotheses full command/signature equality True
```

The fresh Lean probe copied each signed theorem's complete telescope under an audit name and used only `by exact <delivered theorem> <all explicit binders in order>`. It also elaborated `example : type_of% @<delivered theorem> := @<audit theorem>` for each theorem. Both copied definitions were compared to their implementations by `rfl`. There is no provider/frozen-export equality or seal-body obligation for this infrastructure-only package; inventing one would expand the assigned scope.

`Data.lean:144-145` eliminates `patch` exactly once and its `PlanarBirkhoffResult` exactly once, selecting one action cube, O', quartic family F, homological solution chi and T. Every chart, collision/domain, lattice, averaged-jet and tube clause is built from these same witnesses. `Data.lean:219-233` selects the moving branch of the same result and returns the corresponding P0, literal `2 * p11c_sigma`, and literal `p11c_beta`. The physical positivity/order/eta inputs precede all existential choices; coupling is quantified only in conclusions. No result bundle, chart property, flow existence, jet identity or BNF conclusion is added to the root premises.

The signed projection contains all exact P-G input clauses at a=b=2 and mu0=1, using the actual frozen `HasFastDiffeomorphism`, `HasSecularBirkhoffForm`, cylinder and Hamiltonian definitions. Its chart and tube outputs meet the designed physical transport consumers. The finer source characterizations are intentionally supplied through the upstream common construction, not through the narrowed existential projection alone (design:64-68; design audits 1 N1 / 2 N1).

## Required characterization and delivery gates

**Actual objects and same cube/domain: PASS.** Let p=(G,m0,m), Ka=`closedBall a0 r` and Oa=`ball a0 (2*r)` from the single T21 `patch` at `Patch.lean:102`. The map from axes to actions is the actual `PlanarData.actions`; inverse axes are `PlanarData.axes`. T16's `PlanarBirkhoffResult` (`Birkhoff/Defs.lean:42-73`) places `actions '' Ka` inside O', with compact closure inside `actions '' Oa`; the same F/chi/T precede the universal choice of either physical perturbation. In particular the two models are not identified by eliminating independent existential statements.

The source dictionary, with actual owning declarations, is:

| Source object/certificate | Actual owner and proof location | Result |
|---|---|---|
| Axis cube / positive determinant bound | `patch`, `Patch.lean:102`; the returned inner cube, outer cube and positive B are used at Data:144-174,223-230 | Same T21 cube; B is a proved uniform lower bound. Its numerical minimum identity is not an extra consumer requirement. |
| C0 | `SecularForm.constantTerm`, `SecularForm/Coefficients.lean:37`, evaluated at `p.axes I` for `p11cSecularData p hp` | The literal Part-8 constant, not a renamed free P0. |
| deltaS | `SecularForm.modelDelta`, `SecularForm/Momentum.lean:557` | `(2*m0)⁻¹ * sum_i m_i^4*(G*m0)^2/I_i^2`, exactly the action-only difference. |
| Fixed P0=C0 | T16 `P0 I = p11c_secular (p11c_hatFix p) I 0`, `Birkhoff/Defs.lean:62-63`; `p11cB_secular_eq` (Jets:64); `SecularForm.rayRemainder_zero` (Quadratic/Jet:81) at zero | Proved from delivered exports in the fresh audit probe, with `p11cB_actions_axes`; holds for positive I with admissible inverse axes, hence throughout this same action cube. |
| Moving P0=C0+deltaS | The same T16 P0 clause for `p11c_hatMov`; `p11cB_secular_mov`, Birkhoff/Average:58; `SecularForm.identification`, Momentum:579; `p11cB_circular_mem`, Birkhoff/Domain:56 | Proved in the probe; the integrability/collision-domain guard is discharged by the actual circular point at these same actions, not omitted. |
| Omega=2 sigma | Literal T16 clauses at Defs:65-73 and returned formula Data:231; `p11c_sigma_eq_sigma`, SpectralAdapter:291 | Same ordered Part-8 spectral data; no missing factor 2. |
| beta=beta-hat | Actual T13 `p11c_beta` / `beta_def`, Beta:34-44; `beta_formula`; `p11cB_average_beta`, Birkhoff/BetaAvg:37 | Proved torus average with the frozen `1/2 * sum beta_ij R_i R_j` normalization; same axes and frame. |
| Common Birkhoff map | Defs:46-60, `T = p11c_rotationLift p ∘ p11c_liftFlow chi.eval`; `birkhoff_form` and `patch` | One T on `p11c_tube O' rS` for both physical models, before either model's P0 is chosen. |

The fresh proof checks for the two constant identities have no new assumption beyond `p.Valid`, positive actions and inverse axes in `p11c_axes`. These conditions hold on the action cube: positive endpoints follow from DataBox; `p11cB_axes_actions` and the good-cube clause yield the inverse-axis condition. For either T16 P0 witness, its displayed equality to the secular value at zero composes directly with those checks. The identities persist on V and its closure, both contained in that same action cube. The probe is validation of existing exports; it adds no production certificate or premise. The signed `pg_hypotheses` projection deliberately hides these equalities, as its existing comment states.

**Applicable SOURCE_GAP rows: PASS through delivered real exports.**

| Retained gap | Delivered proof route and applicability check |
|---|---|
| `stepP:p11b:bt-rot#lift` analytic eigenframe | Explicit normalized eigenvector frame `p11c_frame`; nonzero norm from positive off-diagonal; `p11c_frame_analyticAt` and `global_planar_frame` in Frame:106,130; `p11c_rotationLift_chart` at Frame:247. The chosen outer cube is in `p11c_axes`. No simply-connectedness shortcut or choice of a merely continuous eigenbasis. |
| `stepP:p11b:fl-bd` uniform real existence | `p11cQ_exists`, QuarticFlow/Energy:245, actually invokes `gen_uniform_compact` and `gen_confinement`, not just an a-priori inequality. `p11cQ_flow_spec` gives the chosen real solution; `flow`, QuarticFlow:42, bounds the cubic field uniformly on a compact thickening and shrinks the radius before time one. Zero initial data are covered by uniqueness. |
| `stepP:p11b:li-tay` real Lie/Taylor | `real_lie_taylor`, NormalForm/Taylor:64, proves the real integral Taylor formula along an actual real solution; `lie`, NormalForm:62, supplies the actual `flow` solution, real analytic brackets and compact remainder estimates. No complex small-field theorem is applied to a bare real analytic generator. |
| `stepP:p11b:lm-prop` full lift/symplectic applicability | `full_lift_hamiltonian` and `lift_map`, Lift:40,71, include the fast-angle derivative/integral. Lift/Iterate:140-150 applies `p11cVar_isSymplecticOn` to the full real Hamiltonian and its actual analytic solution map, then iterates it; inverse and translation arguments extend the chart to the tube. T16 composes that chart with the rotation chart in Birkhoff/Compose. |

The graph's alternative roots-continuity route and the general-n Part-11a wrapper are not used here; P-G's own source gaps remain obligations of P-G, with no theorem import or assumed P-G conclusion in P12-C. This audit does not purport to re-prove unrelated upstream packages or pinned papers.

## Node and declaration ledger

PA means `KAM.Planetary.PlanarAssembly`; other new helpers are in `KAM.Planetary`. Every design-table row assigned to P12-C is listed. Internal proof steps need no separate public theorem.

| Node / declaration | Delivered declaration or proof location | Verdict | Reason |
|---|---|---|---|
| `bpP:p12:data` | PA.pg_hypotheses, Data:83,144-233 | PASS | Single shared tuple, actual patch/map/jets; only physical source premises. |
| `bpP:p12:data#pg-data` | Same, Data:231-328 | PASS | All P-G data and H1-H6 jointly, mu0=1. |
| `bpP:p12:perturbation` | PA.total_chart, PA.perturbation; upstream kepler_h and jets | PASS | Signed literal compositions; source jet dictionary checked above. |
| `bpP:p12:chart` | PA.pg_hypotheses, Data:192-218,249-312 | PASS | All chart, domain, derivative, lattice, Hamiltonian and tube clauses. |
| `stepP:p12:ch-dom` | Data:43-63,192-212,249-251 | PASS | Open invariant tube and actual collision-free product-chart image. |
| `stepP:p12:ch-chart` | PA.chart_of_birkhoff, ChartData:43; Data:213,252-254 | PASS | Real analytic/symplectic composition; invertible derivative. |
| `stepP:p12:ch-lat` | Data:214-218,255-260 | PASS | Fast 2pi lattice, injectivity modulo it, no slow lattice assumption. |
| `stepP:p12:ch-ham` | PA.chart_hamiltonian_of_preserves_fast, ChartData:56; Data:261-263 | PASS | Exact physical splitting, action preservation, arbitrary real coupling. |
| `stepP:p12:ch-tube` | p12c_slow_small; Data:264-304 | PASS | Stronger tube clause for every positive r<=r0, independent of the extra 2r² condition. |
| `bpP:p12:pg-hypotheses` | PA.pg_hypotheses | PASS | Exact signed output; all consumer clauses are proved. |
| `stepP:p12:pg-sets` | Data:157-177,234-248 | PASS | Nonempty connected bounded V, open W containing closure V, exact collar constants. |
| `stepP:p12:pg-h1` | Data:305-307 | PASS | Closure-cylinder lies strictly inside analytic tube; joint analyticity by second projection. |
| `stepP:p12:pg-h2` | Data:308-313 | PASS | Constant coupling family and proved fast periodicity. |
| `stepP:p12:pg-h3` | Data:314-317 | PASS | Existing fast_diffeo on positive expanded box W. |
| `stepP:p12:pg-h4` | Data:318-321 | PASS | T16's same-model BNF restricted to V and reduced radius. |
| `stepP:p12:pg-h56` | Data final two proof branches | PASS | Same T21 determinant lower bound and symmetry on inverse axes in the inner cube. |
| `bpP:p12:chart#cylinder-domain` | Data:192-208 | PASS | Closure of disc cylinder, not only open-cylinder containment, lies inside O. |
| PA.chart_of_birkhoff | ChartData:43 | PASS | Exact signed conditional helper; its chart premises are discharged in the joint construction. |
| PA.chart_hamiltonian_of_preserves_fast | ChartData:56 | PASS | Exact signed conditional helper, preserves frozen Hamiltonian and carriers. |
| p12c_flow_zero | SlowSmall:31 | PASS | Cubic homogeneity forces field(0)=0; real uniqueness identifies chosen flow with zero solution. |
| p12c_slow_T | SlowSmall:48 | PASS | Unconditional identity for actual total lift; independent of fast angle. |
| p12c_slow_small | SlowSmall:89 | PASS | Compact action set plus guarded continuity yields uniform positive rho; conditional helper with distinct name. |
| p12c_actions_sq | DataBox:28 | PASS | Literal sqrt action identity under nonnegative axis coordinate. |
| p12c_actions_nonneg | DataBox:35 | PASS | Real sqrt and positive masses; no extra axis-sign premise. |
| p12c_box | DataBox:41 | PASS | Positive ordered endpoints and closed box inside actual cube image; inverse axes construct the witness. |
| continuous_assemble_zero (private) | SlowSmall:61 | PASS | Coordinate continuity for compactness argument. |
| continuous_slow_part (private) | SlowSmall:70 | PASS | Continuous actual slow projection. |
| slowLength_lt_of_norm (private) | SlowSmall:75 | PASS | Explicit finite-coordinate Euclidean-length versus sup-norm bound with factor 3. |
| tube_isOpen (private) | Data:43 | PASS | Actual action/slow-length preimage conditions. |
| shift_mem_tube (private) | Data:51 | PASS | Fast shift leaves actions and slow block unchanged. |
| slowLength_lt (private) | Data:65 | PASS | Two oscillator discs at radius <=rS/2 lie strictly in length ball of radius rS. |

No unsigned public export is presented as a source graph slug while stating a weaker conclusion. The signed names follow the signature authority; implementation details such as W's larger positive box and a further radius reduction do not weaken their stated or downstream consumer conclusions.

## Definitions and fallbacks

Exactly two new public definitions, no new structure/abbrev/instance:

- `PA.total_chart`: literal total composition `poincareProd m (G*m0) ∘ T` on the entire phase carrier. Matches the signed body; no off-domain zero extension.
- `PA.perturbation`: literal actual `fMov G m0 m` evaluated at that chart, constant in real coupling on the entire carrier. Matches the signed body; no surrogate Hamiltonian or junk branch.

The local `set` bindings V,K0,W,r0,O,C,p are concrete proof witnesses, not new standing assumptions. Upstream `p11c_flow` has an explicit fallback to the initial point when a real solution does not exist (QuarticFlow/Spec:34). P12-C does not rely on that fallback: `flow` supplies existence on the consumed small domain, and `p12c_flow_zero` supplies an actual zero solution before applying `p11cQ_flow_eq`. Outside that domain p12c_slow_T is merely an identity for the total selected map. There is no new fallback masquerading as a flow theorem.

## Independent validation

Commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5` for Lean/Lake work. No heartbeat/recursion/synthesis budget change, clean/update/cache command, global rebuild or package dependency modification was used. The build was submitted through the required compile gate. A first static lint attempt was stopped before ABI elaboration; the complete lint below was rerun under the required environment after the build. No overlapping audit-owned Lean invocations were used.

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-p12c \
  KAM.Planetary.PlanarAssembly.ChartData \
  KAM.Planetary.PlanarAssembly.SlowSmall \
  KAM.Planetary.PlanarAssembly.DataBox \
  KAM.Planetary.PlanarAssembly.Data
```

Exit 0; gate invokes `nice -n 5 lake build`:

```text
[inp-gate] slot 2 acquired 00:33:37 for KAM.Planetary.PlanarAssembly.ChartData KAM.Planetary.PlanarAssembly.SlowSmall KAM.Planetary.PlanarAssembly.DataBox KAM.Planetary.PlanarAssembly.Data
Build completed successfully (9381 jobs).
```

This targeted invocation replayed dependencies from the worktree overlay. It reports upstream warnings plus two warnings in the audited file:

```text
warning: KAM/Planetary/PlanarAssembly/Data.lean:58:35: This simp argument is unused:
  Fin.append_right
warning: KAM/Planetary/PlanarAssembly/Data.lean:155:12: This simp argument is unused:
  Real.dist_eq
```

These do not affect theorem soundness, but contradict the handoff's warning-free claim for the new files. Suggested cleanup belongs to the writer; no source repair was made during this audit.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, **only the explicitly permitted generated-root exception**:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1160 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Static inspection confirms all four files have the copyright/module/public imports/module docstring/public section headers, exposed definitions, fewer than 1500 lines, no line over 100 characters, no forbidden escape/override or EuclideanSpace in code. The 335-module KAM import closure has **zero frozen theorem modules and zero provider modules**: hence no DRAFT_SORRY theorem import, no P-G import (sealed or otherwise), and no provider quarantine exception is needed.

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py \
  /root/code/KAM-inp-p12c KAM.Planetary.PlanarAssembly.ChartData \
  KAM.Planetary.PlanarAssembly.SlowSmall KAM.Planetary.PlanarAssembly.DataBox \
  KAM.Planetary.PlanarAssembly.Data
```

Exit 0: `short-name check OK (no reused public short name)`. Signed source names such as `total_chart`/`perturbation` are deliberately nested under PlanarAssembly, as the design requires; the unsigned helper names are unique. No harmful root shadow was introduced.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P12CAudit.lean
```

Final exit 0, no warnings/errors. This verifies exact signature bodies and reverse type probes plus the fixed/moving constant identifications described above. Preliminary probe-generation errors (named-argument delimiter extraction, missing noncomputable section, and an explicit secular rewrite) were corrected in scratch only; they were not package failures. The final probe and every audited public theorem contain no sorry. Axiom receipts from the final successful run follow; each contains only the three permitted axioms:

```text
'KAM.Planetary.PlanarAssembly.chart_of_birkhoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.chart_hamiltonian_of_preserves_fast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.p12c_flow_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p12c_slow_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p12c_slow_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p12c_actions_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p12c_actions_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p12c_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.pg_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkhoff_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.global_planar_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lift_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_secular_mov' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_secular_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.beta_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_sigma_eq_sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_fixed_C0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_moving_C0_deltaS' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_lie_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lie' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.full_lift_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_average_beta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.forward_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.collar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.fast_diffeo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.product_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IsChart.bijective_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.movingHamiltonian_poincareProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_poincareProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_field_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_field_slice_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cQ_flow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_T_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_actions_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_axes_actions' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_circular_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_estimate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.rayRemainder_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Planetary.PlanarAssembly.ChartData \
  KAM.Planetary.PlanarAssembly.SlowSmall \
  KAM.Planetary.PlanarAssembly.DataBox \
  KAM.Planetary.PlanarAssembly.Data
```

Exit 0, one invocation. Exact verbose output:

```text
replaying KAM.Planetary.PlanarAssembly.Data
replaying KAM.Planetary.PlanarAssembly.DataBox
replaying KAM.Planetary.PlanarAssembly.SlowSmall
replaying KAM.Planetary.PlanarAssembly.ChartData
```

`git diff --check inp...HEAD` exited 0 (with the merge-base warning described above). Scratch probes are deleted at closeout. No state-changing git operation was performed. The only persistent audit-owned repository edit is this report; the pre-existing untracked handoff is retained.

## Notes, source defects and limits

1. **Nonblocking integration/hygiene notes:** inherited generated-root diff, stale generated root accepted by the brief, and two local unused-simp warnings. The literal protected-path check must not be reported as empty, nor the targeted build as warning-free.
2. **Documented implementation deviations:** Data:183 uses `r0 = min (rS/2) rho`, and Data:231 chooses delta=1. The uniform-continuity radius is fixed before coupling and makes the tube conclusion hold for every r<=r0, so delta's conditional bound is redundant and sound. W is the positive expanded box `(lo/2,2*hi)` rather than the literal outer-axis image from blueprint D4; the signed projection only requires an open neighborhood with fast diffeomorphism, which is proved. These choices preserve all assigned consumer needs. B's exported property is the required positive lower bound rather than an exported numerical-minimum equality.
3. **No new suspected pinned-paper erratum or false frozen statement.** The blueprint's zero extensions are superseded by the audited design's literal total compositions. The blueprint's quantitative slow-flow route is replaced locally by the proved qualitative uniform smallness plus a radius reduction; no source claim is assumed. The existing design SOURCE_GAP rows were checked against actual delivered real exports, as detailed above.
4. **Scope:** accepting these infrastructure clauses neither certifies the whole inherited three-dot change nor proves the physical KAM headlines. The narrowed signed existential intentionally does not expose the finer jets or identify independently chosen outputs of a future FixedAssembly theorem; P13-A must use the same upstream joint construction when claiming that identification.
