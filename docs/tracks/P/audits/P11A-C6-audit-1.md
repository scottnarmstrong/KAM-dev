# P11A-C6 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the C6 helper package. `KAM.Planetary.affine_flow` and `KAM.Planetary.affine_flow_param` pass their exact design contracts. No frozen theorem anchor or provider is delivered by C6, so this is not a seal of P-G, P-PLANAR, P-FIXED, or any campaign headline.

## Scope and authority

Audited worktree `/root/code/KAM-inp-p11ac6`, HEAD `3049422e5f5ff56779edc93953d48ccdb9123f77`; comparison `inp` resolved to `edcbb41e1257f22557319e7e7038488867953a93`. Used `git diff inp...HEAD` as requested. The diff has 13 paths: the five C6 additions and eight inherited integration/name-renaming paths, which are outside the explicit audit scope. The protected-path diff for `KAM/Frozen manifest KAM.lean README.md` is empty. The existing untracked handoff was left untouched.

Read AGENTS.md, PLAN, DECISIONS, the common package brief, C6 handoff/AUDIT FOCUS, P11A design row C6 and proof/node mapping, the three design audits, track P statement, source blueprint `blueprint-P/parts/p11a2-cutoff-step.tex:203-226`, and the ten SEALED frozen definitions in the import closure. The focus narrows the generic provider/seal brief to exactly the five modules below. The user's explicit absolute output path overrides the generic brief's instruction to write in the main inp worktree.

The signature file is absent in this package worktree; the shared authoritative `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` was read directly, never imported or edited. Its current SHA-256 is `36f4f5b6da43859e9008cb3e1e0a611d926146805a63b4420de6e1fb540a3d1b`. All four required definition/structure declarations and both theorem headers agree after removing comments and whitespace. Older design-audit snapshot hashes are historical, not the current signature hash.

## Results by export and declaration

| Export / anchor | Verdict | Meaning |
|---|---|---|
| `KAM.Planetary.affine_flow` | PASS | Exact source/design helper type; fresh-name implementation application checked. |
| `KAM.Planetary.affine_flow_param` | PASS | Exact joint-holomorphy type; all explicit binders applied in order. |
| Frozen anchors / providers | N/A | No new anchor or provider in this package; no sealing claim. |

Every declaration below is in namespace `KAM.Planetary`; all are public through the exposed public noncomputable sections. Internal helper statements are local suppliers for the cited node, rather than replacements for its full aggregate statement.

| Node / responsibility | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| `af-flow` | `flow_displacement` (AffineFlow.lean:30) | PASS | Trajectory mean-value inequality yields sharp component displacements. |
| `af-deriv` | `norm_affineGauge_eq` (AffineFlow.lean:75) | PASS | Gauge norm equals scaledNorm (s/2) sigma. |
| `af-deriv` | `fderiv_flow_sub_id` (AffineFlow.lean:80) | PASS | Weighted 2 kappa plus unweighted 2 kappa + kappa s/sigma, using triangular blocks. |
| `af-rest` | `field_real` (AffineFlow.lean:144) | PASS | Reality of the frozen complex Hamiltonian field derived from RealOn. |
| `bpP:p11a:affine-flow` | `affine_flow` (AffineFlow.lean:165) | PASS | Exact design theorem; all conjuncts proved with source hypotheses only. |
| `affine-flow construction` | `p11Affine` (AffineFlowBasic.lean:30) | PASS | Literal scalar affine Hamiltonian, with complex bilinear pairing. |
| `affine-flow construction` | `p11Flow` (AffineFlowBasic.lean:33) | PASS | Literal existing Canonical.flow on the frozen field and stated open domain. |
| `af-deriv` | `p11GaugeBound` (AffineFlowBasic.lean:37) | PASS | Pointwise induced bound in the explicit scaled max norm. |
| `affine-flow source data` | `P11AffineHyp` (AffineFlowBasic.lean:40) | PASS | All 12 fields are source premises; zero A allowed; no output field. |
| `af-field` | `fderiv_p11Affine_apply` (AffineFlowBasic.lean:58) | PASS | Explicit differential; only pointwise differentiability assumed. |
| `domain-def` | `mem_Dom_iff` (AffineFlowBasic.lean:86) | PASS | Exact specialization of action neighbourhood of the singleton zero. |
| `af-field` | `differentiableOn_p11Affine` (AffineFlowBasic.lean:90) | PASS | Holomorphy on the full strip times all actions; stronger domain than needed. |
| `af-field` | `field_fst` (AffineFlowBasic.lean:103) | PASS | Frozen positive angle component equals p1. |
| `af-field` | `field_snd` (AffineFlowBasic.lean:112) | PASS | Negative transpose derivative plus inhomogeneous term; correct field sign. |
| `af-field` | `field_bound` (AffineFlowBasic.lean:122) | PASS | Bounds A and (n+1)sA/sigma, using coordinatewise Cauchy estimates. |
| `af-field construction` | `affineGauge` (AffineFlowBasic.lean:160) | PASS | Actual continuous linear equivalence; positivity comes from H. |
| `af-field` | `kappa_le_half` (AffineFlowBasic.lean:164) | PASS | Exactly source smallness 4(n+1)A <= sigma. |
| `af-field` | `kappa_nonneg` (AffineFlowBasic.lean:169) | PASS | Nonnegativity follows from source premises. |
| `af-field` | `smallField` (AffineFlowBasic.lean:173) | PASS | Proves all SmallField fields from H; no hidden analytic input. |
| `af-flow` | `norm_affineGauge_le_iff` (AffineFlowGauge.lean:26) | PASS | Exact componentwise description of scaled closed balls. |
| `af-flow` | `mem_gaugeInterior` (AffineFlowGauge.lean:34) | PASS | General sufficient radius margins; strict domain membership retained. |
| `af-rest` | `complexStrip_add_int` (AffineFlowGauge.lean:62) | PASS | Real integer translations preserve the strip. |
| `af-rest` | `periodic_single_int` (AffineFlowGauge.lean:67) | PASS | Local unit-periodicity implies integer single-coordinate periodicity. |
| `af-rest` | `periodic_int` (AffineFlowGauge.lean:91) | PASS | Finite-coordinate lattice periodicity; no off-strip hypothesis. |
| `af-rest` | `fderiv_periodic_int` (AffineFlowGauge.lean:116) | PASS | Local eventual equality yields equality of derivatives; valid even without differentiability. |
| `af-flow` | `strip_sub_sigma_subset` (AffineFlowGauge.lean:127) | PASS | Source-positive sigma gives strip inclusion. |
| `af-rest` | `field_add_int` (AffineFlowGauge.lean:132) | PASS | Both field components use local periodicity and derivative periodicity. |
| `af-rest` | `image_add_int_Dom` (AffineFlowGauge.lean:148) | PASS | Both image inclusions; inverse integer translation explicit. |
| `af-flow` | `U_sub_half` (AffineFlowGauge.lean:165) | PASS | U lies in the closed-gauge-ball interior of radius 1/2. |
| `af-flow` | `V_sub_one` (AffineFlowGauge.lean:170) | PASS | V lies in the closed-gauge-ball interior of radius 1. |
| `af-flow` | `V_sub_U` (AffineFlowGauge.lean:175) | PASS | Nested open domains with correct strip/action losses. |
| `af-simple` | `fst_solution` (AffineFlowSimple.lean:28) | PASS | Actual projected trajectory solves the angle ODE on [-1,1]. |
| `af-simple` | `contDiffOn_p1` (AffineFlowSimple.lean:41) | PASS | Real C1 regularity derived from complex holomorphy. |
| `af-simple` | `flow_fst_indep` (AffineFlowSimple.lean:50) | PASS | ODE uniqueness with identical angle initial data. |
| `af-simple` | `flow_affine_comb` (AffineFlowSimple.lean:69) | PASS | Convex action combination remains in Omega and solves the same ODE. |
| `af-simple construction` | `affTheta` (AffineFlowSimple.lean:151) | PASS | Angle projection of the existing flow at zero action. |
| `af-simple construction` | `affV` (AffineFlowSimple.lean:154) | PASS | Action projection at zero action. |
| `af-simple construction` | `affM` (AffineFlowSimple.lean:157) | PASS | Actual action partial derivative at zero; regularity proved before use. |
| `af-flow` | `flow_differentiableAt` (AffineFlowSimple.lean:161) | PASS | flow_b on the open gauge interior, for every time in [-1,1]. |
| `af-simple` | `flow_fst_eq` (AffineFlowSimple.lean:167) | PASS | Time-one specialization of angle independence. |
| `af-simple` | `flow_snd_affine` (AffineFlowSimple.lean:172) | PASS | One-sided derivative on [0,1] identifies the affine slope with affM. |
| `af-simple` | `affTheta_differentiableAt` (AffineFlowSimple.lean:214) | PASS | Composition with zero-action section; no assumed derivative. |
| `af-simple` | `zero_mem_U` (AffineFlowSimple.lean:222) | PASS | Zero action lies in U by strict source positivity of s. |
| `af-deriv` | `fderiv_flow_fst` (AffineFlowSimple.lean:229) | PASS | Derivative of local angle identity; no action-to-angle block. |
| `af-simple` | `fderiv_flow_eta` (AffineFlowSimple.lean:251) | PASS | D Phi (0,b) = (0,M b) using local affine identity. |
| `af-simple` | `aff_duality` (AffineFlowSimple.lean:289) | PASS | Symplectic pairing gives (DTheta a) dot (M b) = a dot b. |
| `af-rest(f) construction` | `paramField` (ParameterFlow.lean:28) | PASS | Zero parameter velocity and the literal fibrewise frozen Hamiltonian field. |
| `af-rest(f)` | `fderiv_partial` (ParameterFlow.lean:33) | PASS | Chain rule identifies angle partial derivative with joint derivative on (a,0). |
| `af-rest(f)` | `paramField_differentiableOn` (ParameterFlow.lean:46) | PASS | Joint holomorphy proved by derivative regularity, not assumed as a field premise. |
| `af-rest(f) construction` | `paramGauge` (ParameterFlow.lean:96) | PASS | Actual product equivalence diag(delta0 inverse,W). |
| `af-rest(f)` | `norm_paramGauge` (ParameterFlow.lean:100) | PASS | Exact max product gauge identity. |
| `bpP:p11a:affine-flow(f)` | `affine_flow_param` (ParameterFlow.lean:106) | PASS | Exact design theorem; local parameter ball suffices, no uniform boundary margin. |

## Definition classification and refutation attempts

Nine new definitions and one structure were inspected. `p11Affine` is the literal affine Hamiltonian on its whole Pi-product carrier; `p11GaugeBound` is exactly the scaled induced inequality. `P11AffineHyp` contains dimension, radius/positivity, smallness, holomorphy, strip-local periodicity and the two source bounds only. It assumes no trajectory, canonical map, derivative estimate, inverse, or parameter-flow conclusion.

`p11Flow` aliases the existing totalized `Canonical.flow`, which chooses an actual solution when one exists and otherwise returns its initial point (`KAM/Canonical/Flow.lean:54`). The intended analytic interpretation is restricted to the proved gauge interiors and times [-1,1]. `smallField`, `U_sub_half`, `V_sub_one`, and `flow_a` discharge existence and uniqueness before every relevant use; no theorem exploits the fallback. `affTheta` and `affV` project that same flow at zero action. `affM` is its actual action partial derivative at zero: although total `fderiv` is zero at nondifferentiability points, the implementation proves differentiability on U before using it and identifies the slope by unique one-sided differentiation. Outside the claimed domains these are ordinary total extensions, with no claimed analytic interpretation.

`affineGauge` and `paramGauge` construct genuine invertible continuous linear maps with explicit positive denominators. Their proof arguments cannot encode additional premises. `paramField` is exactly `(0,X_phi_b)` for all inputs, with no selected extension or substitute field.

The field has the frozen sign `(p1,-Dp0-(Dp1)^T eta)`. Coordinate Cauchy bounds yield A_eta=(n+1)sA/sigma and the precise kappa=2(n+1)A/sigma<=1/2. The sharper displacement A cannot be inferred from the gauge bound alone: the proof correctly applies the mean-value inequality to each component along actual trajectories. Closed gauge balls fit the open strip/action domains because the initial memberships are strict.

Angle independence uses actual ODE uniqueness. For action affinity the proof replaces the proposed linear-ODE route by convex combinations of trajectories, proves those combinations remain in Omega, invokes uniqueness, and differentiates on [0,1] at zero. This is a valid proof-route variation without changed premises. Symplecticity supplies the exact bilinear duality `(DTheta a) dot (M b)=a dot b`; in finite square dimension this identifies M as the inverse transpose. No conjugate/Hermitian pairing is substituted.

The weighted 2 kappa derivative bound is consumed on V. The proof uses the zero action-to-angle block to derive the fixed max-norm bound `2 kappa+kappa*s/sigma`, preserving the potentially large lower-left block. Separate diagonal and lower-left estimates in blueprint clause (d) are consequences of the exported gauge bound and block identities, rather than separately named public theorems. No unjustified fixed-norm comparison is used.

The parameter proof constructs an actual augmented holomorphic SmallField, chooses a ball around each b0 inside open B, and uses uniqueness to identify its flow locally with `(b,Phi_b z)`. The parameter component is zero, so the local gauge leaves the field bound unchanged. H at b and H at b0 differ only in proof arguments to the same scale equivalence; proof irrelevance does not add an assumption. No uniform distance to the boundary of B is assumed. Empty B is handled vacuously; A=0 is allowed throughout without division by A.

## Dependency, naming and hygiene review

The recursive project import closure contains 57 KAM modules, no provider and no frozen theorem (DRAFT_SORRY or otherwise). Its ten frozen imports are all manifest-kind `definition`, state `SEALED`: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary Phase. All were read against the relevant norms/carriers/sign conventions.

No new public fully qualified name duplicates another declaration in KAM. A source scan's same-short-name candidates resolve to other namespaces: `KAM.Canonical.CanonData`, `KAM.Canonical.ComposeData`, `KAM.Planetary.OscFlowHyp`, `KAM.Iso.R3bp`, `KAM.Iso.ExactAux`, and `KAM`. No new instances or ambient norm changes occur. All five files have copyright, module, public imports, module docstring and exposed public section; no forbidden token, option override or EuclideanSpace occurs.

Actual line counts: AffineFlowBasic 199; AffineFlowGauge 184; AffineFlowSimple 311; AffineFlow 227; ParameterFlow 179 (1100 total). Every file is well below 1500.

## Independent validation receipts

All Lean/Lake commands below were serial within this audit, with `LEAN_NUM_THREADS=1` and niceness 5. The build wrapper supplies `nice -n 5` internally. No library-wide build, cache download, cleanup, update, or generated-root regeneration was run.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac6 KAM.Planetary.MaximalStep.ParameterFlow KAM.Planetary.MaximalStep.AffineFlow
   ```

   Output (exit 0):

   ```text
   [inp-gate] slot 2 acquired 13:56:50 for KAM.Planetary.MaximalStep.ParameterFlow KAM.Planetary.MaximalStep.AffineFlow
   Build completed successfully (9103 jobs).
   ```

2. Complete signature comparison and fresh probe:

   The Python comparison removed comments and whitespace from the four complete data declarations and both complete theorem headers, retaining every `let ... := ...` in `affine_flow`. All six matched. The probe copied both design statements under fresh names and used exactly these bodies:

   ```lean
   by exact affine_flow H
   by exact affine_flow_param hB p0 p1 h0 h1 H
   ```

   It also checked both `example : type_of% @affine_flow := @audit_c6_affine_flow` and the corresponding parameter example, and printed axioms of every public theorem in the table. It never imported the sorry-bearing design file. Provider/frozen seal probes are inapplicable because C6 has neither; these fresh-name design probes check the corresponding helper interface directly.

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC6Audit.lean
   ```

   Exit 0. Exact axiom output for all 42 theorems:

   ```text
'KAM.Planetary.flow_displacement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_affineGauge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_flow_sub_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.field_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.affine_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_p11Affine_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_Dom_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_p11Affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.field_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.field_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.field_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.kappa_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.kappa_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.smallField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_affineGauge_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_gaugeInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complexStrip_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.periodic_single_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.periodic_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_periodic_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.strip_sub_sigma_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.field_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.image_add_int_Dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.U_sub_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.V_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.V_sub_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fst_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.contDiffOn_p1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.flow_fst_indep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.flow_affine_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.flow_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.flow_fst_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.flow_snd_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.affTheta_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.zero_mem_U' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_flow_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_flow_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.aff_duality' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.paramField_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_paramGauge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.affine_flow_param' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.ParameterFlow KAM.Planetary.MaximalStep.AffineFlow KAM.Planetary.MaximalStep.AffineFlowSimple KAM.Planetary.MaximalStep.AffineFlowGauge KAM.Planetary.MaximalStep.AffineFlowBasic
   ```

   Exit 0. Complete output:

   ```text
replaying KAM.Planetary.MaximalStep.AffineFlowBasic
replaying KAM.Planetary.MaximalStep.AffineFlowGauge
replaying KAM.Planetary.MaximalStep.AffineFlowSimple
replaying KAM.Planetary.MaximalStep.AffineFlow
replaying KAM.Planetary.MaximalStep.ParameterFlow
   ```

4. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the explicitly permitted generated-root staleness. Complete output:

   ```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (650 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   Module checks, frozen-anchor guard, and all 144 frozen ABI hashes passed. No other lint complaint occurred.

5. Static checks: recursive import/manifest classification as above; namespace-aware public-name scan found no fully qualified duplicate; forbidden-token scan of the five files produced no matches; `git diff --check inp...HEAD` exited 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited 0 with no output. Final report whitespace check passed; all five audit-created scratch files (probe, inventory, axiom log, kernel log, lint log) were deleted. Final `git status --short` lists only this report and the pre-existing untracked handoff. No tracked repository path was modified by this audit.

## Notes, uncertainties and suspected defects

1. **Dependency wording needs qualification.** Design `docs/tracks/P/design/P11A-LEAN-DESIGN.md:717` says “no W/measure dependency”; handoff says “No imports of ... W/measure modules.” C6 directly imports C0 Basic, and `KAM/Planetary/MaximalStep/Basic.lean:12` publicly imports `KAM.Planetary.WeakMeasure.Basic`. Thus there is a transitive dependency on W0 for shared carriers. There is no dependency on the weak-measure estimates or PGMeasure, and no such estimate is used by these proofs. This inherited carrier coupling is an architectural/documentation note, not a proof failure; the literal claim of no W import in the closure would be false.
2. **Handoff file sizes are stale.** Its 198/184/309/223/176 counts differ from the current 199/184/311/227/179. The cap is respected.
3. The general lint's generated-root exception is recorded with its actual receipt below; generated files were not repaired. No fresh default-heartbeat design signal arose.

No new suspected pinned-paper erratum or frozen-declaration defect was found. The blueprint source at p11a2:203-226 is consistent with the implementation and accepted design. The independent source-paper transcription beyond this supplied local blueprint is not part of this focused package audit. No source statement, norm, constant dependence, carrier, or hypothesis was silently repaired. No implementation edits were made. All audit probes/logs were created only under `.lake/abi-scratch/` and removed after recording results; only this report is the audit's persistent addition.
