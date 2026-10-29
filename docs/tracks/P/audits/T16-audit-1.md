# T16 independent package audit 1

**Overall verdict: PASS WITH NOTES for T16 (`KAM.Planetary.birkhoff_form`).** The signed declarations match exactly, the scoped graph slice is established, and no added premise or consumer obstruction was found. This is an infrastructure-package verdict. T16 has no provider or frozen theorem anchor; it does not seal `planarTwoPlanetKAM` or `fixedSunPlanetaryKAM`.

Audit dates: 2026-10-28–29 UTC.

Audit scope: only `KAM/Planetary/PlanarTorsion/Birkhoff.lean` and its 15 `Birkhoff/*.lean` modules. Read-only upstream checks were made to establish applicability. Authority: user instructions (including this worktree's exact report destination), AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T16 handoff/AUDIT FOCUS, P11C design and design audit, P1213 design, Part-11b blueprint, track-P statement, frozen root telescopes and Birkhoff/physical predicates. Only this report is a lasting edit; disposable probes reside in this worktree's `.lake/abi-scratch/` and are removed.

Reviewed HEAD `f62f2b53ff3a065beae6d25a19ea9a1b146f72c9`; `inp` observed at `fd85905402ce93e14121657af8bd95cde40d35e4`. `git diff inp...HEAD` warns of multiple merge bases and selects `086928650ca9281e65a68123f75f45436881167a`. Its full inventory has 35 new Lean files / 5030 insertions, including inherited Quartic, NormalForm, Lift and Beta work. This audit assesses the requested 16-file T16 slice (2022 physical lines, maximum 311), not those inherited packages anew. Protected-path diff is empty. The supplied handoff was already untracked at entry and was not changed.

## Signed fidelity, scope and consumers

The current authoritative signature file `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` has SHA-256 `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`. Whitespace-normalized comparison returns True for the full definitions `p11c_phi4` and `PlanarBirkhoffResult`, and for the complete `birkhoff_form` telescope. Independent copies under fresh names elaborate; both definition-function equalities close by `rfl`; the copied signed theorem closes with `exact birkhoff_form p hp a0 rho hgoodK`, and `example : type_of% @auditT16_birkhoff_form := @birkhoff_form` elaborates. No provider/seal-body probe is applicable because T16 supplies no anchor.

**Focus 1 — omitted Hamiltonian equation: PASS WITH NOTES, deliberate consumer deduction, not a missing T16 proof obligation.** Blueprint `blueprint-P/parts/p11b-planar-torsion.tex:208` says “$H^\Psi\circ T=h(\Lambda)+\mu P$ ... ($T$ preserves $\Lambda$)”. The signed predicate at `Birkhoff/Defs.lean:42` instead gives exact T, fast-action preservation, angle covariance, image in the physical domain and actual pullbacks. This deliberate interface choice is expressly justified in `docs/tracks/P/design/DESIGN-P11C-design-audit-1.md:182`: “action preservation, angle-translation covariance and upstream physical periodicity give the Hamiltonian split and hperiod.”

The deduction uses existing exports, not a new assumption: `Poincare/Product.lean:343` and `:349` give the moving/fixed physical Hamiltonian splits at `T w`; `hProd` at `:54` depends only on `fast (T w).2`. The signed action equality (`Birkhoff/Defs.lean:54`) identifies that with `fast w.2`, and its next domain clause supplies the product-chart hypothesis. Scratch consumer probes verify both resulting identities for arbitrary real coupling and the actual `p11c_hatMov`/`p11c_hatFix` pullbacks. The generic blueprint identity `(h ∘ fast + mu*fhat) ∘ T = h ∘ fast + mu*(fhat ∘ T)` is the same substitution.

P12-C's exact planned helper is `PlanarAssembly.chart_hamiltonian_of_preserves_fast` (`P1213-LEAN-DESIGN.md:514`); P13-A's counterpart is `FixedAssembly.chart_of_preserves_fast` (`:643`). Both require exactly that action equality and physical-domain membership. `kepler_h`, `total_chart` and `perturbation` (`:418–430`) are literal restrictions/compositions, so these identities translate to the planned degenerate Hamiltonians. P12-C's joint `pg_hypotheses` retains the Hamiltonian equation as an output (`:550`); P12-E consumes that joint result for physical transport. The frozen root telescopes have only physical input data and return actual moving/fixed physical tori; neither introduces an additional normalization premise. General-n P-FIXED uses its separate wrapper; the two-planet branch uses this same fixed map. Thus the missing standalone clause cannot be treated as root closure, but it does not obstruct either consumer.

Periodicity likewise follows from the signed angle covariance specialized to `c i = 2*pi*k i`, action preservation and `poincareProd_lattice`; the physical functions composed with the product chart then agree. Coupling independence is literal (`fun _ => fhat ∘ T`). P12/P13 still own the closed-cylinder restriction, boundary collar, chart transport, frequency patch/torsion, P-G assembly and other advertised delivery gates. On `r0=r/2`, the closed oscillator cylinder has slow length at most `sqrt 2*r0 < r`, so the signed open-tube analyticity supplies their required margin. This report verifies interface sufficiency, not downstream implementation completion.

**Focus 2 — positivity: PASS.** `Choice.lean:103` defines the local action set by positivity and an axis thickening. `p11cB_actions_pos` derives positivity from `p.Valid` and positive ordered axes. `Constants.lean:41–65` obtains thickened axes inside the good cone and derives positivity on the compact action image; `Result.lean:72–78` repeats the explicit attachment for its restriction. `p11cB_domain` legitimately requires positive actions because `p11c_frameActionDomain` alone admits negative ones. That helper premise is discharged, never added to the signed theorem. The negative-radius/empty-cube case is handled by compact-set thickenings without an unstated nonemptiness premise.

**Focus 3 — actual T11/T14 consumption: PASS.** `Constants.lean:71` calls `lift_map` and supplies its chart/injectivity/covariance outputs to `p11cB_result`. `Result.lean:100` passes them through `p11cB_T_props`. `Compose.lean:44` calls `p11c_rotationLift_chart`, proves its image-domain premise from the unchanged actions, and composes the two charts and injections. `global_planar_frame` is used in `Jets.lean:205`, `BetaAvg.lean:43` and `Map.lean:96`; it supplies actual oriented orthogonality and diagonalization. `full_lift_hamiltonian` is upstream T11 work, not needed a second time in this composition proof.

## Scoped graph nodes

All labels below have prefix `bpP:p11b:` or `stepP:p11b:` in the design node table at `P11C-LEAN-DESIGN.md:130–136`. Proof-local fragments are not unsigned exports pretending to state stronger nodes.

| Node | Declaration / proof locator | Verdict | Reason |
|---|---|---|---|
| birkhoff-form | `birkhoff_form`; `p11cB_main`; `PlanarBirkhoffResult` | PASS WITH NOTES | Signed output exact; elementary clause-(a) deductions assigned to consumers as above. |
| bt-rot | `p11cB_quad_rot`; `p11cB_average_beta`; `global_planar_frame` applications | PASS | Global sorted oriented frame; no simply-connectedness premise needed. |
| bt-rot#lift | `p11cB_T_props`, `p11cB_T_assemble`, `p11cB_result` | PASS | Actual T11 lift and T14 rotation lift composed on proved domains. Analytic angle lift is bypassed by the global matrix route. |
| bt-K | `p11cB_domain`, `p11cB_secular_analyticAt`, `p11cB_R_analyticAt`, `p11cB_R_jetEq` | PASS | Physical domain uniform by compactness/periodicity; actual fixed average, quadratic bridge, quartic jet and evenness. |
| bt-nf | `p11cB_family`, `p11cB_NR4`, `homological` and `lie` calls in Constants; `p11cB_average_beta` | PASS | Concrete rotated quartic, NR4 from finite-mode product, sixth-order Lie estimate and exact beta factors. |
| bt-avg | `p11cB_secular_T`, `p11cB_secular_mov`, `p11cB_estimate` | PASS | Actual transformed torus integral, correct radian normalization, moving correction cancels. |
| bt-frozen | `p11cB_fhat_clause`; two branches in `p11cB_result` | PASS | T15 invoked only after proving integrability and sixth-order bound for both actual pullbacks. |

## Every new public declaration

All names are in `KAM.Planetary`; locators below are relative to `KAM/Planetary/PlanarTorsion/`. Conditional assembly lemmas have distinct `p11cB_*` names and do not replace signed results. Their hypotheses (Lie bound, flow bound, physical domain, chart data) are intermediate proof inputs explicitly discharged by `p11cB_main`; none becomes a premise of `birkhoff_form`.

| Declaration | File:line | Verdict | Fidelity / meaning |
|---|---|---|---|
| `birkhoff_form` (theorem) | `Birkhoff.lean:42` | PASS WITH NOTES | Signed telescope exactly; proof applies stronger p11cB_main and drops unused Oa-good premise. |
| `p11cB_secular_T` (theorem) | `Birkhoff/Average.lean:32` | PASS | Actual radian torus average; angle-translation invariance and the moving action-only correction. |
| `p11cB_secular_mov` (theorem) | `Birkhoff/Average.lean:58` | PASS | Actual radian torus average; angle-translation invariance and the moving action-only correction. |
| `p11cB_frame_eq` (theorem) | `Birkhoff/BetaAvg.lean:31` | PASS | SO(2) frame/projector identification; literal half-sum beta form with frozen oscillator actions. |
| `p11cB_average_beta` (theorem) | `Birkhoff/BetaAvg.lean:37` | PASS | SO(2) frame/projector identification; literal half-sum beta form with frozen oscillator actions. |
| `p11cB_family` (theorem) | `Birkhoff/Chi.lean:31` | PASS | Physical quartic realization, unchanged coefficient restriction, and analytic 2-sigma frequency. |
| `p11cB_restrict` (def) | `Birkhoff/Chi.lean:67` | PASS | Physical quartic realization, unchanged coefficient restriction, and analytic 2-sigma frequency. |
| `p11cB_restrict_eval` (theorem) | `Birkhoff/Chi.lean:71` | PASS | Physical quartic realization, unchanged coefficient restriction, and analytic 2-sigma frequency. |
| `p11cB_freq_analyticOnNhd` (theorem) | `Birkhoff/Chi.lean:74` | PASS | Physical quartic realization, unchanged coefficient restriction, and analytic 2-sigma frequency. |
| `p11cB_average_congr` (theorem) | `Birkhoff/Chi.lean:81` | PASS | Physical quartic realization, unchanged coefficient restriction, and analytic 2-sigma frequency. |
| `p11cB_phi4_continuousAt` (theorem) | `Birkhoff/Choice.lean:31` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_goodA_isOpen` (theorem) | `Birkhoff/Choice.lean:39` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_NR4` (theorem) | `Birkhoff/Choice.lean:49` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_O` (def) | `Birkhoff/Choice.lean:103` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_O_isOpen` (theorem) | `Birkhoff/Choice.lean:106` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_O_mono` (theorem) | `Birkhoff/Choice.lean:117` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_actions_pos` (theorem) | `Birkhoff/Choice.lean:121` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_axes_actions` (theorem) | `Birkhoff/Choice.lean:132` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_actions_mem_O` (theorem) | `Birkhoff/Choice.lean:145` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_O_closure` (theorem) | `Birkhoff/Choice.lean:151` | PASS | Finite modes give NR4; positive action collar, inverse axis/action identities and compact closure. |
| `p11cB_liftFlow_act` (theorem) | `Birkhoff/Compose.lean:29` | PASS | Composition consumes the rotation-lift chart and the lift-map properties on their actual domains. |
| `p11cB_T_props` (theorem) | `Birkhoff/Compose.lean:33` | PASS | Composition consumes the rotation-lift chart and the lift-map properties on their actual domains. |
| `p11cB_main` (theorem) | `Birkhoff/Constants.lean:34` | PASS | All analytic/jet/domain/flow hypotheses paid here; r,C chosen before arbitrary Oa. |
| `p11c_phi4` (def) | `Birkhoff/Defs.lean:35` | PASS | Signed definition; exact text modulo whitespace and definitional-equality probe. |
| `PlanarBirkhoffResult` (def) | `Birkhoff/Defs.lean:42` | PASS | Signed definition; exact text modulo whitespace and definitional-equality probe. |
| `p11cB_diag` (theorem) | `Birkhoff/Diag.lean:31` | PASS | Actual derivatives/continuous linear rotation; evenness kills odd derivatives, polynomial coefficients exact. |
| `p11cB_rotCLM` (def) | `Birkhoff/Diag.lean:43` | PASS | Actual derivatives/continuous linear rotation; evenness kills odd derivatives, polynomial coefficients exact. |
| `p11cB_rotCLM_apply` (theorem) | `Birkhoff/Diag.lean:49` | PASS | Actual derivatives/continuous linear rotation; evenness kills odd derivatives, polynomial coefficients exact. |
| `p11cB_diag_comp` (theorem) | `Birkhoff/Diag.lean:54` | PASS | Actual derivatives/continuous linear rotation; evenness kills odd derivatives, polynomial coefficients exact. |
| `p11cB_diag_odd` (theorem) | `Birkhoff/Diag.lean:71` | PASS | Actual derivatives/continuous linear rotation; evenness kills odd derivatives, polynomial coefficients exact. |
| `p11cB_iteratedDeriv_poly` (theorem) | `Birkhoff/Diag.lean:90` | PASS | Actual derivatives/continuous linear rotation; evenness kills odd derivatives, polynomial coefficients exact. |
| `p11cB_good` (def) | `Birkhoff/Domain.lean:34` | PASS | Actual collision-free chart domain; positive circular actions, compact angle cell, lattice reduction. |
| `p11cB_good_isOpen` (theorem) | `Birkhoff/Domain.lean:37` | PASS | Actual collision-free chart domain; positive circular actions, compact angle cell, lattice reduction. |
| `p11cB_planeLength_pos` (theorem) | `Birkhoff/Domain.lean:40` | PASS | Actual collision-free chart domain; positive circular actions, compact angle cell, lattice reduction. |
| `p11cB_fin2_ne` (theorem) | `Birkhoff/Domain.lean:53` | PASS | Actual collision-free chart domain; positive circular actions, compact angle cell, lattice reduction. |
| `p11cB_circular_mem` (theorem) | `Birkhoff/Domain.lean:57` | PASS | Actual collision-free chart domain; positive circular actions, compact angle cell, lattice reduction. |
| `p11cB_domain` (theorem) | `Birkhoff/Domain.lean:137` | PASS | Actual collision-free chart domain; positive circular actions, compact angle cell, lattice reduction. |
| `p11cB_estimate` (theorem) | `Birkhoff/Estimate.lean:34` | PASS | Conditional assembly lemma; supplied Lie bound yields the actual transformed-average bound. |
| `p11cB_rotC` (def) | `Birkhoff/Family.lean:34` | PASS | Explicit rotated polynomial identity, finite monomial extraction, analytic quartic family. |
| `p11cB_quartic_rot` (theorem) | `Birkhoff/Family.lean:52` | PASS | Explicit rotated polynomial identity, finite monomial extraction, analytic quartic family. |
| `p11cB_basic_extract` (theorem) | `Birkhoff/Family.lean:60` | PASS | Explicit rotated polynomial identity, finite monomial extraction, analytic quartic family. |
| `p11cB_family_of_coeffs` (theorem) | `Birkhoff/Family.lean:92` | PASS | Explicit rotated polynomial identity, finite monomial extraction, analytic quartic family. |
| `p11cB_fhat_clause` (theorem) | `Birkhoff/FhatClause.lean:30` | PASS | Conditional assembly lemma; proves actual pullback analyticity, integrability and frozen expansion. |
| `p11cB_K` (def) | `Birkhoff/Jets.lean:36` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_C` (def) | `Birkhoff/Jets.lean:40` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_freq` (def) | `Birkhoff/Jets.lean:43` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_R` (def) | `Birkhoff/Jets.lean:47` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_actions_axes` (theorem) | `Birkhoff/Jets.lean:51` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_secular_eq` (theorem) | `Birkhoff/Jets.lean:64` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_rotate_analyticAt` (theorem) | `Birkhoff/Jets.lean:68` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_secular_analyticAt` (theorem) | `Birkhoff/Jets.lean:92` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_rotate_smul` (theorem) | `Birkhoff/Jets.lean:114` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_rotate_zero` (theorem) | `Birkhoff/Jets.lean:118` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_sigma_analyticAt` (theorem) | `Birkhoff/Jets.lean:121` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_R_analyticAt` (theorem) | `Birkhoff/Jets.lean:132` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_quad_rot` (theorem) | `Birkhoff/Jets.lean:198` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_secular_even` (theorem) | `Birkhoff/Jets.lean:220` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_R_jetEq` (theorem) | `Birkhoff/Jets.lean:232` | PASS | Physical analytic secular function, exact second/fourth jets, evenness and vanishing five-jet. |
| `p11cB_rotationLift_assemble` (theorem) | `Birkhoff/Map.lean:32` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_T_assemble` (theorem) | `Birkhoff/Map.lean:59` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_assemble_continuous` (theorem) | `Birkhoff/Map.lean:77` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_assemble_eta` (theorem) | `Birkhoff/Map.lean:83` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_slowLength_sq` (theorem) | `Birkhoff/Map.lean:89` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_rot_sq` (theorem) | `Birkhoff/Map.lean:93` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_rot_abs_lt` (theorem) | `Birkhoff/Map.lean:109` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_Zs_good` (theorem) | `Birkhoff/Map.lean:119` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_T_good` (theorem) | `Birkhoff/Map.lean:154` | PASS | Literal assembled composite map, action/angle bookkeeping, orthogonal length and physical-domain bounds. |
| `p11cB_tube_mono` (theorem) | `Birkhoff/Result.lean:33` | PASS | Conditional assembly with explicit provenance for all hypotheses in Constants; same T for both models. |
| `p11cB_result` (theorem) | `Birkhoff/Result.lean:37` | PASS | Conditional assembly with explicit provenance for all hypotheses in Constants; same T for both models. |

## Definition classification

Every new definition is exposed by its module's `@[expose] public noncomputable section`. No new abbreviation, structure, global instance or root-level declaration occurs.

| Definition | Classification / whole-carrier behavior | Verdict |
|---|---|---|
| `p11c_phi4` | Exact finite product over all nonzero integer modes of l1 size at most four encoded in `Fin 9`; total physical spectral formula. Nonzero product supplies every divisor, with factor two handled explicitly. | PASS |
| `PlanarBirkhoffResult` | Exact signed output predicate. Existential output data, never an assumed normalization premise in the signed theorem. | PASS |
| `p11cB_good` | Literal intersection of product-chart domain and preimage of collision-free physical domain. | PASS |
| `p11cB_rotCLM` | Continuous linear map rotating both slow blocks by the supplied matrix for every input; no orthogonality assumed for its definition. | PASS |
| `p11cB_rotC` | Six explicit polynomial coefficients of the rotated Gram quartic, valid for arbitrary real coefficients/g/s; exact ring identity proves it. | PASS |
| `p11cB_K` | Actual fixed secular integral at the frame-rotated point for all arguments; analyticity is asserted only on the proved physical neighborhood. | PASS |
| `p11cB_C` | Same actual fixed secular integral at zero slow variables. | PASS |
| `p11cB_freq` | Literal `2 * sigma`, not an arbitrary auxiliary frequency. | PASS |
| `p11cB_R` | Exact subtraction of constant/quadratic/quartic from K; vanishing five-jet is proved, not built into an input. | PASS |
| `p11cB_O` | Positive actions whose literal squared-axis inverse lies in the displayed thickening; positivity is essential for inverse action reconstruction. | PASS |
| `p11cB_restrict` | Keeps all coefficients unchanged and restricts only their analyticity proof. Evaluation equality is `rfl`, including outside the smaller set. | PASS |

No new junk/default/fallback branch is introduced. Existing total integrals, square roots, derivatives and upstream flow definitions are used with their actual specifications on proved domains. The physical-domain, flow and analytic-jet hypotheses are established before applying the Lie estimate; no off-domain fallback is used to obtain a result.

## Proof and hygiene observations

The Lie estimate's source assumptions in the assembly helpers are transparent intermediate obligations, with the actual call in `Constants.lean:76` supplying `p11cB_R_analyticAt` and `p11cB_R_jetEq`. NR4 is proved by explicit mode encoding in `Choice.lean:49`. The five-jet proof in `Jets.lean:232` reduces all diagonal derivatives to exact physical order-two/order-four jets and evenness, then invokes the analytic diagonal-to-jet lemma. The actual averaged function is used throughout, not a formal polynomial surrogate. `P0 I` is chosen as the zero-slow average for the relevant perturbation; the moving difference `modelDelta` cancels exactly.

A recursive local import inspection from all 16 modules reached 278 KAM modules, **zero frozen theorem imports and zero provider imports**. Frozen definitions, notably `HasSecularBirkhoffForm`, are imported legitimately. Thus no DRAFT_SORRY theorem or quarantined provider is consumed. All 69 public source declarations are fresh short names outside the scoped files (a scan of other KAM sources found no duplicate); all live in `KAM.Planetary`, with no harmful root shadow.

All 16 files have copyright/module/public-import/module-doc/public-section form. Maximum file length is 311 lines; no scoped line exceeds 100 Unicode characters. The raw scoped forbidden-token/resource-option scan returned no matches. No heartbeat, recursion-depth or synthesis override is present. The handoff reports earlier default-heartbeat design signals resolved by splitting/naming intermediate terms; the fresh checks use default budgets. No implementation edit was made in this audit.

## Source/blueprint defects, deviations and limits

No new pinned-paper erratum was identified; pinned PDFs were not re-audited. Two explicit route differences from the blueprint remain documented rather than silently relabelled:

- `blueprint-P/parts/p11b-planar-torsion.tex:217`: “lifts analytically to the angle ... (covering S1→S1)” is superseded here by T14's explicit global oriented eigenframe and rotation-lift theorem. This is the design-approved matrix route (`P11C-LEAN-DESIGN.md:179`), not a claimed formalization of an angle-lifting theorem. The graph's historical gap/BYPASSED bookkeeping remains the orchestrator's task.
- `blueprint-P/parts/p11b-planar-torsion.tex:218`: “choose rho_K by compactness ... polydiscs” is implemented by a compact circular-torus tube plus periodic lattice reduction, followed by orthogonal/flow length estimates and `2*r ≤ delta`. It proves the physical image/analyticity properties actually consumed, without exporting source-local radius names.

The omitted displayed Hamiltonian split is the deliberate signed-interface decomposition established above, with no new physical premise; the report does not propose changing the signature. The signed definitions are placed in `Birkhoff/Defs.lean` and publicly re-exported by the facade, as required by the actual acyclic module split. No unsigned declaration reuses a graph-node name with a weaker statement. Splitting the original estimated 700-line T16 module into 16 files is within the hard per-file cap.

No frozen declaration, manifest, generated root, README, production Lean file or existing handoff was edited. The two frozen physical roots remain DRAFT_SORRY in this checkout; this audit cannot mark them seal-ready. Downstream source/delivery gates and the broader KAM campaign remain outside this package verdict.

## Independent check transcript

All commands run from `/root/code/KAM-inp-p11c-t16`. All audit-launched Lean/Lake commands are serialized, with `LEAN_NUM_THREADS=1` and niceness 5; lint's internal ABI Lean process inherits that environment/niceness. No rebuild from scratch, cache update, library clean or package-directory edit was performed.

1. Targeted gate build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-p11c-t16 KAM.Planetary.PlanarTorsion.Birkhoff
```

Exit **0**. Output begins `[inp-gate] slot 2 acquired 23:52:59 for KAM.Planetary.PlanarTorsion.Birkhoff` and ends `Build completed successfully (9324 jobs).` Replayed warnings are from upstream modules (unused binders); no T16 Birkhoff warning/error appeared. The command builds through the required gate, whose actual build invocation is `nice -n 5 lake build`.

2. Signed definitions, exact theorem telescope/body application, and axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T16Probe.lean
```

Exit **0**, no errors/warnings. The probe was generated from the signed definition text and theorem telescope, with fresh names; no signature `sorry` was copied. Its three text comparisons were `True`, and both body equalities were proved by `rfl`. Full `#print axioms` output for all 58 new public theorems:

```text
'KAM.Planetary.birkhoff_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_secular_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_secular_mov' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_frame_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_average_beta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_restrict_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_freq_analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_average_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_phi4_continuousAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_goodA_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_NR4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_O_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_O_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_actions_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_axes_actions' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_actions_mem_O' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_O_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_liftFlow_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_T_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_rotCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_diag_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_diag_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_iteratedDeriv_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_good_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_planeLength_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_fin2_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_circular_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_estimate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_quartic_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_basic_extract' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_family_of_coeffs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_fhat_clause' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_actions_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_secular_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_rotate_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_secular_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_rotate_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_rotate_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_sigma_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_R_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_quad_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_secular_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_R_jetEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_rotationLift_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_T_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_assemble_continuous' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_assemble_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_slowLength_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_rot_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_rot_abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_Zs_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_T_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_tube_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_result' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every line lists exactly the permitted three axioms; no `sorryAx` or extra axiom occurs.

3. Kernel replay, a single invocation with the facade and all 15 lemma modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Planetary.PlanarTorsion.Birkhoff \
  KAM.Planetary.PlanarTorsion.Birkhoff.Average \
  KAM.Planetary.PlanarTorsion.Birkhoff.BetaAvg \
  KAM.Planetary.PlanarTorsion.Birkhoff.Chi \
  KAM.Planetary.PlanarTorsion.Birkhoff.Choice \
  KAM.Planetary.PlanarTorsion.Birkhoff.Compose \
  KAM.Planetary.PlanarTorsion.Birkhoff.Constants \
  KAM.Planetary.PlanarTorsion.Birkhoff.Defs \
  KAM.Planetary.PlanarTorsion.Birkhoff.Diag \
  KAM.Planetary.PlanarTorsion.Birkhoff.Domain \
  KAM.Planetary.PlanarTorsion.Birkhoff.Estimate \
  KAM.Planetary.PlanarTorsion.Birkhoff.Family \
  KAM.Planetary.PlanarTorsion.Birkhoff.FhatClause \
  KAM.Planetary.PlanarTorsion.Birkhoff.Jets \
  KAM.Planetary.PlanarTorsion.Birkhoff.Map \
  KAM.Planetary.PlanarTorsion.Birkhoff.Result
```

Exit **0**. Complete replay output:

```text
replaying KAM.Planetary.PlanarTorsion.Birkhoff
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Defs
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Map
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Domain
replaying KAM.Planetary.PlanarTorsion.Birkhoff.FhatClause
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Chi
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Diag
replaying KAM.Planetary.PlanarTorsion.Birkhoff.BetaAvg
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Constants
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Jets
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Average
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Compose
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Family
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Choice
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Estimate
replaying KAM.Planetary.PlanarTorsion.Birkhoff.Result
```

4. Consumer deduction for the omitted Hamiltonian equation, both physical perturbations:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T16Consumer.lean
```

Final exit **0**, empty stdout/stderr. Both examples assume only `p.Valid`, signed action preservation and signed image-domain membership, then apply the existing product-chart splitting theorems for arbitrary real coupling. The initial scratch version had a rewrite mismatch between the reducible adapter `p.kappa` and `p.G*p.m0`; an explicit `change` normalization fixed it. This was a scratch elaboration correction, not a production defect or changed premise.

5. Source/module/frozen/ABI lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1091 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only failing diagnostic is the generated `KAM.lean` freshness check, the exact exception allowed by the audit brief. Module checks, frozen-anchor guard and all 144 elaborated ABI hashes pass. No other lint failure is present. The generated file was left untouched as required; orchestration must regenerate it before integration. This is the package's hygiene note, not a substantive Lean failure.

6. Read-only integrity checks:

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

All exit **0**, no diff/error output; three-dot commands emit only the already-recorded multiple-merge-base warning. Scoped scans find no forbidden proof escapes, resource options, EuclideanSpace, oversized files, overlong lines, duplicate public short names outside scope, or root shadows. The report covers all 58 public theorems and 11 definitions; one private continuity helper is additionally replayed with its module.

**Disposition:** T16 PASS WITH NOTES; no production fix requested. Preserve the documented global-frame bypass and consumer ownership of elementary Hamiltonian/periodicity deductions; regenerate the generated root at integration. Neither frozen physical root is sealed by this report. All disposable audit probes/inventories/diff captures were deleted; the sole added repository artifact is this report, beside the unchanged pre-existing untracked handoff.
