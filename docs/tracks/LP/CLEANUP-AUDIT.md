# Track LP clean-up audit (report only)

Worktree `KAM-lp-redmass`, branch `lp-cleanup-audit`, base `main` c9a123b53. No Lean edited, nothing built.
Scope A: `KAM/Planetary/{StrongAMD,Spatial}/**` (141 files, 24,090 lines, 1,217 public declarations: 927 theorem, 72 lemma,
205 def, 12 structure, 1 abbrev) and LP's 41 providers (`KAM/Provider/Planetary/{StrongAMD,Spatial}/`, 18 + 23).
Frozen LP files: 128 under `KAM/Frozen/Planetary/{StrongAMD,Spatial}/` (read-only). Scope B: errata and deviations (see
`errata-proposed.json`, summary in section B at the end).

Method: scripted token counts (every identifier segment, so dot-notation `h.foo` and `Foo.bar` count as uses of `foo`/`bar`;
docstring and comment mentions also count as uses, so every "dead" figure is a LOWER bound), then a fixpoint that removes
declarations whose only users are other dead declarations. Names used by a provider or frozen file were excluded
(24 declarations, listed by `res.json` in the scratchpad, e.g. `lp1_planar_strongAMD_safety_source_isDiophantine[_halfInteger]`,
`lp3_*_source`, `lp0_planar_barrier_source`, `orbital_identities`, `spatial_orbital_identities`, `osc_tangency`,
`spatialOscPhase_ellipse`, `pairThreshold_isLeast`, `strongAMD_nonneg`, `SourceCanonicalPhase.hz`). No frozen declaration
name collides with an implementation name (0 of 204), so the D62 rebase left no duplicated defs.

## Summary counts

| # | Category | Count |
|---|---|---|
| 1 | Dead-code candidates (never named anywhere, or only by other dead decls) | 114 (93 zero-use + 21 transitive), about 750 lines |
| 2 | Superseded helpers / parallel predicates (section 2) | about 45 decls, about 450 lines removable or mergeable |
| 3 | Stale or jargon comments | 142 `FREEZE-PROPOSAL.md` refs in 141 files (+41 in providers); 119 `Package LP-...`; 21 `Package LP3-...`; 89 `LP-SP-...`; 10 "L15" locators; 10 "draft" lines |
| 4 | Mathlib naming problems | about 460 declarations (section 4) |
| 5 | Files over 1000 lines | 0 (largest 498, `StrongAMD/Geometry.lean`) |
| 6 | Literal duplicates | 8 clusters (section 6) |

## 1. Dead code (candidates)

Rule: no occurrence of the short name anywhere in `KAM/` outside its own declaration line. `*` = found only by the transitive
pass; `~` = carries `@[simp]` or is an instance helper (candidate only, 3 such: `lpRescale_lpUnrescale`,
`lpRescaleNM_lpUnrescaleNM`, `planarEmbed_smul/sub`). All entries are `path:line` of the declaration.
Also 416 declarations are used only inside their own file (not dead, but candidates for `private` when someone does naming work).

By kind: 106 theorem, 5 lemma, 4 def (`lpRescaleEquiv`, `lpRescaleNMEquiv`, `spatialEccVector`, plus one transitive).
By role (approx.): 44 source-carrier `_def`/`_eq`/`_property` bridge lemmas (the frozen `Source*` defs are now owners; these
restate them), 14 chart leaf results of L7/L17 (`lpChart_energy/momentum/symplectic/analytic/localDiffeo/...`,
`spatialPoincare_symplectic/localDiffeo/eccVector`, `spatialRot_det`; source-completeness results, keep only if the owner wants
L7/L17 exported), 12 threshold API leaves (`orderedPairThreshold_pos`, `continuous_orderedStrongThreshold`, `strongThreshold_pos`, ...),
10 reflection/rotation API, 9 vector algebra (`spaceDot_*`, `spaceSq_sub`), 9 NM-twin bridge equations, 16 other.

| File (under `KAM/Planetary/`) | # | Declarations (`name:line`) |
|---|---|---|
| Spatial/AnalyticDomain/Alignment.lean | 1 | spaceE3_eq_e₃:39 |
| Spatial/AnalyticDomain/Bounds/Algebra.lean | 1 | cBody3_ofReal:41 |
| Spatial/AnalyticDomain/Core.lean | 1 | spatialSlowDeficit_nonneg:70 |
| Spatial/AnalyticDomain/Extension.lean | 1 | fSpatial_spatialPoincareProd_shift:57* |
| Spatial/Chart/Diffeo.lean | 3 | eq_zero_of_symplecticForm_eq_zero:34*, spatialPoincare_fderiv_equiv:43*, spatialPoincare_localDiffeo:64 |
| Spatial/Chart/Elements.lean | 5 | spatialEccVector:34*, planarEmbed_smul:46*~, planarEmbed_sub:49*~, spatialRot_det:63, spatialPoincare_eccVector:142 |
| Spatial/Chart/Symplectic.lean | 1 | spatialPoincare_symplectic:256 |
| Spatial/ComplexTube.lean | 3 | mem_ball_shiftNM:41*, complexTubeNM_self:153, periodicOrbitSetNM_self:156 |
| Spatial/Elements.lean | 1 | spatialStrongAMDOn_eq:47 |
| Spatial/Model.lean | 1 | spaceSq_sum:83 |
| Spatial/Nek/Cover.lean | 1 | spatialNekCell_slowGap_pos:116* |
| Spatial/Nek/Drift.lean | 1 | exists_spatialNek_rpow_lt:51* |
| Spatial/NonresonantAdapter.lean | 2 | lpUnrescaleNM_eq_lpUnrescale:48, lpRescaleHamNM_eq_lpRescaleHam:52 |
| Spatial/NonresonantAdapterRescale.lean | 2 | lpRescaleNM_lpUnrescaleNM:104*~, lpRescaleNMEquiv:116 |
| Spatial/Osculating/Basic.lean | 12 | spatialOscAxis_eq_spec:81, spatialOscEccVector_eq_spec:86, spatialSourceOscVelocity_eq:139, spatialSourceOscParam_eq:143, spatialSourceOscEnergy_eq:146, spatialSourceOscAxis_eq:151, spatialSourceOscEccVector_eq:155, spatialSourceOscEcc_eq:164, spatialSourceOscPeri_eq:167, spatialSourceOscApo_eq:171, spatialSourceKeplerPeri_eq:175, spatialSourceKeplerApo_eq:179 |
| Spatial/Product/Defs.lean | 1 | ofSpatialBodies_injective:102 |
| Spatial/Rotation.lean | 2 | spatialHamiltonian_rotate:65, spatialNegativeEnergy_rotate_iff:104 |
| Spatial/Rotation46.lean | 2 | incRotation_e₃_two_pos:232~, incRotation_e₃_injective:267 |
| Spatial/RotationSolution.lean | 2 | spatialRotatePhaseCLM_apply:44, isSpatialMovingSolutionOn_rotate_iff:94 |
| Spatial/SourceBarycentric.lean | 2 | spatialSourceBarycentricPositions_def:34, spatialSourceBarycentricVelocities_def:38 |
| Spatial/SourceCarrier.lean | 12 | spatialSourceCanonicalPhase_property:58, spatialSourceOsculatingPhase_property:63, spatialSourceKeplerAxis_def:73, spatialSourceKeplerAction_def:76, spatialSourceKeplerEccVector_def:80, spatialSourceKeplerEcc_def:88, spatialSourcePlanetAngularMomentum_def:92, spatialSourceAngularMomentum_def:97, spatialSourceStrongAMD_def:100, spatialSourceStrongAMD_eq_on:105, spatialSourceKeplerPeri_eq_source:110, spatialSourceKeplerApo_eq_source:117 |
| Spatial/SpatialSafety/Bridge.lean | 2 | spLiftChartSafe_eq_spatialChartSafe:56, lpChartHamNM_eq_spatialPulledHam:60 |
| Spatial/Vector.lean | 8 | spaceDot_comm:114*, spaceDot_add_right:117~, spaceSq_sub:131~, spaceSq_sum_eq_sum_sum:149*, spaceDot_cross_self_left:187~, spaceDot_cross_self_right:190~, spaceDot_cross_cross:194, bodyVector3_sub:290 |
| StrongAMD/AnalyticDomain/Bounds/Algebra.lean | 1 | cBody_ofReal:40 |
| StrongAMD/Modulus.lean | 1 | bddAbove_strongThresholdModulus:71 |
| StrongAMD/Nek/Cover.lean | 1 | nekCell_slowGap_pos:284* |
| StrongAMD/NonresonantAdapterRescale.lean | 3 | lp_append_addNat:40~, lpRescale_lpUnrescale:110*~, lpRescaleEquiv:122 |
| StrongAMD/Osculating/Basic.lean | 2 | oscAxis_eq_spec:68, oscEccVector_eq_spec:71 |
| StrongAMD/PlanarDictionary.lean | 9 | lpChart_energy:70, lpChart_momentum:82, lpChart_eccSq:105*, lpChart_eccentricity_sq:118, lpChart_symplectic:178, lpChart_analytic:183, lpChart_isOpen_dom:187, lpChart_periodic:190, lpChart_localDiffeo:210 |
| StrongAMD/Reflection.lean | 4 | reflectPhase_fst:47~, reflectPlane_reflectPlane:61~, reflectVec_zero:191~, isMovingSolutionOn_reflectPhase_iff:268 |
| StrongAMD/SourceCarrier.lean | 11 | sourceStrongAMD_def:59, sourceKeplerPeri_def:62, sourceKeplerApo_def:65, sourceOscVelocity_def:68, sourceOscParam_def:71, sourceOscEnergy_def:74, sourceOscAxis_def:77, sourceOscEccVector_def:80, sourceOscEcc_def:83, sourceOscPeri_def:86, sourceOscApo_def:89 |
| StrongAMD/Threshold/Defs.lean | 2 | orderedPairThreshold_eq:56, orderedCrossThreshold_eq:59 |
| StrongAMD/Threshold/Strong.lean | 13 | exists_starThreshold_eq:54*, exists_crossThreshold_eq:65*, strongThreshold_eq_member:85, crossThreshold_pos:94*, starThreshold_pos:99*, strongThreshold_pos:104*, strongThreshold_eq_min_first:126*, orderedPairThreshold_pos:148, orderedPairThreshold_lt:152, continuous_orderedPairThreshold:156, orderedStrongThreshold_pos:160, continuous_orderedStrongThreshold:164, orderedStrongThreshold_eq_min_first:168 |

Top removal targets by size: `StrongAMD/Threshold/Strong.lean` (81 lines), `StrongAMD/PlanarDictionary.lean` (80),
`Spatial/SourceCarrier.lean` (76), `Spatial/Chart/Diffeo.lean` (58), `Spatial/Osculating/Basic.lean` (56).
Caveat: 8 `lpChart_*` and the `*_def` lemmas may be intended as public API for the paper/graph (`docs/graph/LP` LEAN_REF, `papers/LP`);
check `docs/graph/LP/DEPGRAPH.md` before deleting (grep found no `lp1_planar`/`lp3_planar` there, but the paper `NOTES.md` cites 15 headline names).

## 2. Superseded helpers

| Item | Where | Status |
|---|---|---|
| Source-carrier bridge lemmas `source*_def`, `spatialSource*_def`, `spatialSource*_eq`, `spatialSourceKeplerPeri/Apo_eq_source`, `spatialSourceStrongAMD_eq_on` | `StrongAMD/SourceCarrier.lean:59-99`, `Spatial/SourceCarrier.lean:58-117`, `Spatial/SourceBarycentric.lean:34,38`, `Spatial/Osculating/Basic.lean` (12) | all zero-use: 44 decls, about 330 lines. Raw totals (`strongAMD`, `keplerPeri`, `osc*`) are NOT dead: still consumed by `PlanarSafeState`, `nekPlanarState`, estimates |
| Old `_source` theorems superseded by `_source_isDiophantine` | planar `PlanarSafety/Source.lean:38,132` (`_source_general`, `_source`), `SourceCorollary.lean:36,68` (`_source_halfInteger`); spatial `SpatialSafety/Source.lean:42,145`, `SourceCorollary.lean:42` | `_source_general` used only in its own file; `_source` and `_source_halfInteger` are still consumed by the `_isDiophantine[_halfInteger]` wrappers (`SourceDiophantine.lean:109,186`; spatial `SourceCorollary.lean:137,222`), which providers use. So the chain is load-bearing; re-prove the wrappers directly from `Main` to retire about 350 lines (`Source.lean` 208 + `SourceCorollary.lean` 149 planar, 248 + 304 spatial) |
| `KAM.Fourier.modeSize` Diophantine helper | `StrongAMD/DiophantineBridge.lean:32` `isDiophantine_iff_forall_modeSize` | still used (8 uses, 2 files: `PlanarSafety/SourceDiophantine.lean`, `SpatialSafety/SourceCorollary.lean`); becomes removable only after the previous row. `KAM/Planetary/MaximalStep/*` `modeSize` uses belong to track P, out of scope |
| `*_halfInteger` duplicates | planar `Main.lean:190` (`lp1_planar_strongAMD_safety_halfInteger`, 1 use, docstring only), spatial `Main.lean:210`; `_normalized` `Main.lean:137`/`:153` (2-3 uses, docstring) | the frozen HalfInteger anchors are proved by the `_source_isDiophantine_halfInteger` chain, not by these. Candidates, but the paper `NOTES.md` cites `lp1/lp2 + _normalized/_halfInteger/_source` by name (15 headline decls): coordinate with paper-lp |
| Drift-scale-generic parallel predicates | `StrongAMD/Nek/PlanarSafety/Orientation.lean:35,60` (`nekPlanarState`, `nekPlanarSol`) vs `PlanarSafety/Orientation.lean:100,126`; `Spatial/Nek/SpatialSafety/Orientation.lean:35,65` (`SpatialNekSafeState/Sol`, extra `ρ`) vs `SpatialSafety/Orientation.lean:131,161` | identical clauses with the drift scale as a parameter (`LP-W5C`, `LP3-PS`, `LP3-SP-SAFE` record this as the accepted deviation). Unify by giving `PlanarSafeState/Sol` and `SpatialSafeState/Sol` the scale parameter; about 110 lines; touches `Nek/*/Main,Prograde,Aligned` and the `of_reflectPhase/of_rotate` lemmas |
| Pre-option-C `L15` locators etc. | see section 3 | comments only |

## 3. Stale or jargon comments (implementation, 141 files)

| Pattern | Occurrences | Proposed fix |
|---|---|---|
| `The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.` (exact sentence; wraps across lines) | 124 lines in 124 files; 142 `FREEZE-PROPOSAL.md` mentions in 141 files (all of scope); providers: 36 files carry the sentence, 41 mention the file; frozen LP files 128 mention it (cannot edit) | delete the sentence; where the module is a frozen anchor's support, say "Statement frozen: D62/D64 (`docs/tracks/LP/FREEZE.md`)" |
| `non-frozen` after `track LP` | 141 | keep (true of implementation) or fold into one standard header |
| `Package LP-<CODE>` / `LP3-<CODE>` / `LP-SP-<CODE>` (package codes) | 119 + 21 + 89 lines (118, 21, 67 files) | replace with the mathematical role; codes are meaningless once handoffs are archived |
| wrong locator `LP:MAIN L15 (502–506)` (MAIN:502 is Theorem 15, should be `T15`) | 10 lines: `PlanarSafety/Main.lean:21,42`, `Prograde.lean:40`, `Orientation.lean:17,98`, `Source.lean:15,37`, `Nek/PlanarSafety/Prograde.lean:39`, `Orientation.lean:34`, `Nek/PlanarSafety/Main.lean:41` (recorded as N3 of `STATEMENT-AUDIT-DRAFT8-1.md`) | sed `L15` -> `T15`; spatial side already uses `T19` |
| "draft" / draft-2 / draft 7 / "LP1 of FREEZE-PROPOSAL.md" | 10 lines, 7 files (`PlanarSafety/Main.lean:24`, `Source.lean:18,131`, `SourceDiophantine.lean:14`, `SpatialSafety/Main.lean:19`, `SourceCorollary.lean:26,135`, `SourceBarycentric.lean:16`, `DiophantineBridge.lean:15`) | rewrite in terms of anchors |
| audit-note references (`LP-W4A-1 N1`, `audit note of LP-OSC`, `statement review 1, F1`) | about 6 | replace with the math fact |
| "in progress", "TODO", "PARTIAL", "stand-in" | 0 | clean |
| Providers: `quarantined while the frozen anchor is DRAFT_SORRY (or not yet created)`, `Until the frozen anchor is ...`, `draft-7 revision-1` | 41 of 41 provider files (historical since D62/D64; noted in `LP-FREEZE8-EXEC-handoff.md`) | providers are not frozen but are quarantined; docstring-only edit is allowed, hash unaffected? check `manifest` provider hashes before touching |

## 4. Mathlib naming problems (skill: snake_case theorems, UpperCamel Props/types, lowerCamel data)

Of 999 theorem/lemma names, a lowerCamel component inside a snake_case name is normal Mathlib style (`strongAMD_nonneg`), so
only project-code prefixes, whole-name camelCase and abbreviations are counted.

| Category | Count | Sample, proposed rename |
|---|---|---|
| Project-code theorem prefixes `lp0_ lp1_ lp2_ lp3_` | 27 (2 + 8 + 8 + 9) | `lp1_planar_strongAMD_safety` -> `planar_strongAMD_exponentialSafety'`/`strongAMD_planar_exp_safe`; `lp3_planar_strongAMD_safety_source` (provider-used: keep) |
| `lp`/`sp`/`nek`/`spLift` camel prefix on theorems | 128 (lp 104, nek 26 minus overlaps, spLift 12) | `lpChart_energy` -> `planarChart_energy`; `lpTraceNM` -> `trace_eq_of_chartTube` |
| `NM` suffix (spatial block-size twins of planar objects) | 71 | `lpRescaleNM_eq_lpRescale` -> `rescale_eq_rescale_nm`; better: merge twins (section 6) |
| `spatial*` prefix redundant with namespace `KAM.Planetary.Spatial` | 225 theorem names | `spatialOscAxis_rotate` -> `oscAxis_rotate` (breaks planar/spatial name clash only if both namespaces are opened; check `open` lines) |
| Whole-name lowerCamel theorems without `_` | 15 (`lpTrace`, `lpExtNFHyp`, `tubeNM`, `lpTraceNM`, `lpExtNFHypNM`, `IsChartExtension.toSmallerTube`, `IsPhysicalState.orbital`, ...) | `lpTrace` -> `trace_eq_of_chartTube` |
| `_def` / `_property` / `_eq_source` suffix | 26 | most are dead (section 1) |
| Project suffix `_source`, `_general`, `_normalized` | 38 | `..._source_general` -> `..._of_general_mass`; keep only live ones |
| Prop-valued defs in lowerCamel (should be UpperCamel) | 2 (`nekPlanarState`, `nekPlanarSol`, `StrongAMD/Nek/PlanarSafety/Orientation.lean:35,60`) | `PlanarNekSafeState`, `PlanarNekSafeSol` |
| Data defs with project prefix `lp`/`sp`/`nek` | 46 of 205 defs | `lpGamma` -> `planarGamma`, `lpRescale` -> `rescale` |
| Structures `LPChartTube`, `LPChartTubeNM`, `LiftData`, `SpatialLiftData` | 4 | `ChartTube`, `LiftData` (acronym `LP` is a project code) |
| Abbreviations `Ham`, `AMD` inside theorem names | 68 | keep `AMD` (term of art defined by the source); expand `Ham` -> `hamiltonian` when renaming anyway |

Names in 1,153 source lines carry `lp*/nek*/spLift*` tokens; 2,667 lines carry `spatial*` tokens.
Rename constraints: the 24 provider/frozen-referenced declarations and every `KAM.Planetary.StrongAMD.sourceOsc*`-style name
used inside frozen type texts must keep their names (frozen files are byte-pinned; a rename needs an alias `@[deprecated] abbrev`
or a retained wrapper). Names cited by the paper and `docs/graph/LP` also need aliases or a paper re-pin.

## 5. Files over about 1000 lines

None. Largest: `StrongAMD/Geometry.lean` 498, `Spatial/Vector.lean` 341, `StrongAMD/Osculating/Estimates.lean` 338,
`Spatial/Osculating.lean` 337, `Spatial/Confinement.lean` 333. All 141 files are far below the 1500 cap.

## 6. Literal duplicates (planar/spatial twins excluded)

| # | Duplicate | Evidence | Fix |
|---|---|---|---|
| 1 | `exists_budget_radius` `StrongAMD/PlanarSafety/Constants.lean:35` = `exists_spatialBudget_radius` `Spatial/SpatialSafety/Constants.lean:38` | identical statement and 17-line proof, same text (`LP-SP-SAFE` item (b): "spatial copy ... to avoid importing an unbuilt planar module") | delete the spatial copy, import planar |
| 2 | `exists_pos_le_forall_fin` `StrongAMD/Nek/Kepler.lean:43` vs `exists_pos_le_forall_fintype` `StrongAMD/Nek/Cells.lean:55` | same proof; the Fin version is the `Fintype` special case; also check Mathlib (`Finset.exists_le`-style) | keep the Fintype one, derive Fin or inline |
| 3 | `spatialSecularBall` `Spatial/AnalyticDomain/Containment.lean:36` vs `spLiftSecularBall` `Spatial/ChartLift/Stopped.lean:43` | equal sets; `Bridge.lean:42` proves it | keep one, delete `Bridge.lean:42,51` |
| 4 | `spatialChartSafe` `Spatial/AnalyticDomain/Safety.lean:36` vs `spLiftChartSafe` `ChartLift/Setting.lean:46` | `rfl` (`Bridge.lean:56`) | keep one |
| 5 | `lpChartHamNM` `Spatial/NonresonantReuse/Hyp.lean:41` vs `spatialPulledHam` `ChartLift/Setting.lean:50` (and `spLiftChartHam:54`, equal on the domain) | `rfl` (`Bridge.lean:60`) | keep one; `spatialStoppedBlock` vs `lpBlockNM` (`Bridge.lean:51`) likewise |
| 6 | `movingSolutionOn_mono` `StrongAMD/Confinement.lean:67` vs `lpMovingSolutionOn_mono` `StrongAMD/ChartLift/Lift.lean:43` | identical signature text | merge |
| 7 | within-file twins: `firstExitTube/firstExitCore` `StrongAMD/Confinement.lean:51,57`, `spatialFirstExitTube/Core` `Spatial/Confinement.lean:52,58`, `nekCellInner/Outer` `Nek/Cover.lean:88,91`, `posCLM3/momCLM3` `Spatial/Vector.lean:312,319`, `spatialGammaBody/ZBody` `Product/Defs.lean:81,84` | same statement text under two names | likely abbrevs; check |
| 8 | `lp1_planar_strongAMD_safety_source_general` (`Source.lean:38`) vs `lp1_planar_strongAMD_safety` (`Main.lean:44`) vs `planar_safety_of_prograde` (`Prograde.lean:43`), and the spatial analogues | statement texts hash-equal up to the premise block | candidate; inspect whether the `_general` is the same theorem |

`Bridge.lean` (`Spatial/SpatialSafety/Bridge.lean`, 97 lines) exists only to reconcile duplicates 3-5 and can go with them.
The parallel `_NM` twins (`lpRescaleNM`, `lpContinuousNM`, `tubeNM`, `complexTubeNM`, `lpChartTubeNM`, ... 71 names) are spatial
re-typings of planar objects at block size `n+n -> n+(n+n)` (`N12`); not literal duplicates, but a generic `m` could merge them.

## Proposed clean-up plan

| Pkg | Content | Lines | Risk |
|---|---|---|---|
| CL-1 comments | delete the FREEZE-PROPOSAL sentence (124 files), `L15`->`T15` (10), drop package codes and draft wording (about 250 lines), provider docstrings (41 files) | about 420 lines edited, 0 semantic change | provider hashes: check `manifest`/ABI before touching providers; implementation docstrings are free |
| CL-2 dead code | delete the 114 candidates (confirm each against `docs/graph/LP` LEAN_REF and `papers/LP` before) | -750 | low; build `KAM.Planetary` roots only via the serial driver |
| CL-3 duplicates | section 6 items 1-6 (+ delete `Bridge.lean`) | -120 | low; touches spatial `NonresonantReuse`, `ChartLift`, `AnalyticDomain` import order |
| CL-4 superseded | merge Nek predicates into `PlanarSafeState/SpatialSafeState` with a scale argument; re-prove `_isDiophantine` wrappers from `Main`, then drop `DiophantineBridge`, `_source_general`, unused `_normalized/_halfInteger` | -450 net | medium: `lp3_*_source` and the `_isDiophantine[_halfInteger]` theorems are provider-bound (names and type text fixed); the paper cites `_normalized/_halfInteger/_source` |
| CL-5 naming | drop `lp*/nek*/spLift*/spatial*` prefixes where not provider/frozen-referenced (about 460 decls) | about 1,500-2,000 changed lines | high churn; do after CL-2..4 to shrink it; renames of referenced names need `@[deprecated]` aliases; coordinate with paper-lp and graph |
| CL-6 lint | all `private` for the 416 file-local helpers | optional | low |

Estimated total: about 1,300 lines removed (5.4 % of 24,090), about 420 comment lines edited, about 1,500-2,000 lines touched by renames.
Frozen files and `manifest/` untouched throughout; every declaration used by a provider (24, listed above) keeps its name.

## B. Errata and deviations (scope B)

Proposed ledger entries are in `docs/tracks/LP/errata-proposed.json` (not merged). Source id `LPMAIN` is proposed for
`docs/tracks/LP/source/MAIN.md` (not yet in `docs/sources.json`; the ledger's existing `LP17` is Laskar-Petit and different).
Findings by origin: `PROOF-AUDIT-1.md` N1-N12 (12 notes), `AMENDMENTS.md` (same 12), `STATEMENT-REVIEW-1..5` (no source erratum;
scope defects F1/F2/F4 of the proposal are ours, not source), `STATEMENT-AUDIT-DRAFT7-1` (no source erratum), `STATEMENT-AUDIT-DRAFT8-1`
(C1 proposal prose "best exponent", N3 `L15` docstring nit; no erratum), `LP-SEAL-audit-1` and `LP-SEAL8-audit-1` (none),
package audits W1B..W5C and 60 handoffs (accepted deviations only), `docs/graph/LP/reviews/GLOBAL-review-1.md` (3 SOURCE_GAP
retained plus L10 pair), `papers/LP/NOTES.md` sections 10-12 (paper deviations; LP17 pin fix `b6241e69` is a `sources.json` record fix, not a ledger item).
`STATEMENT-AUDIT-DRAFT7-2.md` does not exist on main or on `inp-lp` (only `-1`).
Not proposed (ours, not source): the false `Algebra.lean:22` docstring, `PlanarSafety.lean` facade lacking `public section` (LP-PS H1),
process deviations (lint run, serial launch, provider one-liners), commit trailer.
See the JSON for the count (8 errata, 21 deviations, 29 entries).
