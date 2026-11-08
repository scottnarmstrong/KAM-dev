Audited HEAD: `ef3c63d0ea7888c81e4bfa263517885b2692ac4d`
Branch: `inp-lp-graph`
Independent global reviewer: `maud-lp-gglob-1` (fresh session; no extraction or slice review)

# Verdict: PASS WITH NOTES

The assembled graph passes the D65 provenance review, within the prescribed sampling scope. No sampled dependency has a wrong prerequisite or direction; both alternative routes are correctly separated. The notes below correct overly narrow evidence locators, not mathematical topology, frozen statements, or Lean status. They are nonblocking provenance refinements. This is not a new proof audit of the sealed track.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the full LP-GLOBAL-REVIEW-BRIEF.md and the dependency-graph skill. D65 overrides the skill's initial-status/per-slice procedure. Only this report was written; no state-changing git command, build, dashboard regeneration, or source repair was performed.

The main reference initially resolved to `7b65a83ecdb208b55cdac69af3330936acc27c28`; it advanced to `2bdf71d6383114c58e8e9e028823e8e614d74434` during review. Read-only diff between those snapshots is empty for the LP implementation directories, frozen Planetary files and manifest. The audited graph HEAD stayed fixed.

## Check table

| Check | Scope and evidence | Result |
|---|---|---|
| Root identity | All 149 anchor nodes: manifest ID, file, export, ABI hash, contract ID/version match main; every state SEALED; frozen file bytes equal main; exports found as declarations (including qualified `AdjIdx.upperIdx`). Main manifest bytes equal the graph worktree's manifest. | PASS |
| Root completeness | Exactly 41 roots, all sealed theorem anchors. Set equality with all non-definition `planetary.d59.*` entries: 34 characterizations + 5 D62 headlines + 2 D64 headlines. No definition root, missing theorem or extra root. | PASS |
| Structural coverage | Independently reran the exact required linter; exit 0, no stdout/stderr. All 301 nodes reachable; no structural/coverage error. | PASS |
| Source pins | `sha256sum -c docs/graph/LP/CORPUS.sha256` and `.../IMPORTS.sha256`: exit 0, all seven entries OK. | PASS |
| Coverage source sampling | 25 distinct random MAIN/AMENDMENTS items, seed 6502, drawn from 393 such items in database order; checked source text and dispositions. Also read all 47 exclusion reasons (438 total inventory items). Mappings and exclusions are justified. | PASS |
| Edge sampling | 40 distinct random MAIN-cited EDGE records, seed 6501; dependency and direction checked against the cited units. Evidence-locator refinements below. | PASS WITH NOTES |
| Statement symbols | 10 distinct random theorem-anchor edges to frozen definitions, seed 6504; checked the actual declaration before the manifest-bound proof, retaining local `let ... := ...` inside the statement. All ten symbols occur. | PASS |
| Routes | Both route records and their owner checked against MAIN L487/L500 and N6/N7. L12 gives r/4 at r=√μ; L13 gives r/2 at r=D₀√μ. ROUTES on `lpM:L14#improvement` expresses alternatives, not conjunctive DEPS. | PASS |
| PROVED | All anchor identities and seal states checked; all four ordinary nodes' seven main declarations/docstrings rechecked under the unique-match or planar/spatial-pair rule. One permitted axiom process checked all seven plus 10 random sealed theorem exports, seed 6503. | PASS |
| BYPASSED | Recomputed greatest fixed point over the reverse of DEPS and ROUTES. Exactly 136 nodes, identical to assigned BYPASSED set; no bypass sink or blocked consumer. All consumer paths terminate in PROVED sealed roots. Implementation-route justification below. | CONFIRMED |
| Remaining statuses | PROVED 153 = 149 anchors + 4 ordinary; BYPASSED 136; EXTERNAL 12; NOT_STARTED 0. No unexplained NOT_STARTED. | PASS |
| Header/counts | Exact label “streamlined review (D65): one global review” is present in both header.txt and database. Counts agree with current dashboard and final SPEC change-log row. | PASS |
| Source defects | Four already explicit source gaps preserved below; no additional mathematical source defect found in the sample. Normative N1–N12 respected. | NOTES |

Counts independently read/recomputed: 301 nodes; 149 frozen anchors; 41 roots; 1161 total dependency/route edges; root closure 301; 33 leaves; 0 assumptions; 12 external leaves; 2 routes; 4 SOURCE_GAP nodes; 438 coverage items, 47 excluded. The 229-node topology queue consists of records retained as PROPOSED under D65; it is not a requirement for 229 further slice reviews. GLOBAL_REVIEWER/GLOBAL_REVIEW_REF remain `-` pending the writer's incorporation of this report.

## Lean status and D27 confirmation

**I confirm the BYPASSED determination for all 136 assigned nodes.** Independently initialize the candidate set with every ordinary node having no LEAN_REF, excluding external leaves. Repeatedly remove a candidate if any consumer is neither PROVED nor in the candidate set. The greatest fixed point contains all 136 candidates, with no discrepancy against the graph's assigned statuses. Acyclicity and exhaustive root reachability ensure that the recursive rule is not vacuously satisfied by a closed cycle or an unconsumed component.

This is legitimate D27 route substitution in the provenance sense specified by the brief. The sealed headlines delegate through their providers to the `lp0_planar_barrier_source`, `lp1_planar_strongAMD_safety_source_isDiophantine`, corresponding LP2 source exports, half-integer corollaries and LP3 source exports. The LP1/LP2 implementation uses the repository nonresonant adapter (`StrongAMD/NonresonantAdapter.lean:153`, `NonresonantReuse/Drift.lean:131`, `ChartLift/Premises.lean:130`), rather than separately formalizing every paper step of L9–L12. LP3 uses the sealed `partialConvex_nekhoroshev` through `StrongAMD/Nek/Cells.lean:91-94`. Frozen statements remain the consumer interfaces. BYPASSED records the absence of a separate node-level formalization; it does not assert that a source gap has been proved by the graph or that geometric arguments disappear from the implementation.

The four ordinary PROVED nodes resolve as follows. Each pair has one planar and one spatial declaration citing the same MAIN result, as allowed by the map; this does not replace an exact frozen export.

| Node | Main declarations |
|---|---|
| `lpM:L1#velocity` | `KAM.Planetary.StrongAMD.oscVelocity_eq_movingField`; `KAM.Planetary.Spatial.spatialOscVelocity_eq_hamiltonianVectorField` |
| `lpM:L2` | `KAM.Planetary.StrongAMD.orbital_identities`; `KAM.Planetary.Spatial.spatial_orbital_identities` |
| `lpM:L5` | `KAM.Planetary.StrongAMD.barrier_osc_data`; `KAM.Planetary.Spatial.spatialBarrier_osc_data` |
| `lpM:L8` | `KAM.Planetary.StrongAMD.lemma8_complete` (unique docstring match, MAIN L8) |

The sampled Lean import closure comprises 388 local KAM modules; all source blobs match main. The only Lean invocation was one serial process through `/root/code/KAM-inp/.drafts/LP/lp_lean.sh /root/code/KAM-inp-lp-graph /dev/stdin`, with imports and 17 `#print axioms` commands supplied on stdin. Exit 0. Every printed declaration had exactly `[propext, Classical.choice, Quot.sound]`, with no sorryAx or additional axiom. No temporary Lean file was written.

Random sealed theorem sample (seed 6503; roots in header order):
- `KAM.Planetary.Spatial.spatialSourceOscPeri_le_length`
- `KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq`
- `KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast`
- `KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one`
- `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger`
- `KAM.Planetary.Spatial.spatialSourceOscEnergy_neg`
- `KAM.Planetary.Spatial.spatialSourceOscPeri_pos`
- `KAM.Planetary.Spatial.spatialSourceOscApo_ge_length`
- `KAM.Planetary.StrongAMD.sourceOscAxis_pos`
- `KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg`

General AGENTS check: `scripts/lint_sources.sh` was started; it printed `check_lean_modules: PASS (4235 Lean files, 0 comparator configurations)`. It was deliberately terminated (exit 143) while its Python frozen-anchor guard was still running, before `abi_hashes.py`: that later stage writes a scratch file and invokes `lake env lean` outside the mandated wrapper. No ABI-stage Lean invocation occurred. Therefore no full-source-lint PASS is claimed. No build or new result axiom audit was applicable to this report-only task; the brief restricts Lean to #print axioms. The required graph-specific linter completed successfully:

```text
python3 /root/.claude/skills/build-proof-dependency-graph/scripts/proof_depgraph.py --db docs/graph/LP/DEPGRAPH.md --manifest docs/graph/LP/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-all-reachable --check
exit 0; no output
```

## Reproducible sample ledger

Edge sample: Python `random.Random(6501).sample(pool, 40)`, with pool = EDGE records in NODE/file order whose locator contains `source/MAIN.md`. All are valid prerequisite/direction checks. The locator notes concern evidence precision only.

| Sample | Consumer → prerequisite | MAIN lines |
|---|---|---|
| E1 | `lpM:L16#element-error` → `lpM:L5#compact-physical` | L527-L527 |
| E2 | `lpM:L4#competitor` → `lpM:s1:data` | L149-L156 |
| E3 | `lpM:T19#apply-L14` → `lpM:L14` | L603-L603 |
| E4 | `lpM:L8#denominators` → `lpM:L8#real-margin` | L267-L267 |
| E5 | `lpM:L4#feasible-compact` → `lpM:s1:thresholds#actionAxis` | L149-L149 |
| E6 | `lpM:L18` → `lpM:L18#extension` | L595-L595 |
| E7 | `lpM:L18#extension` → `lpM:L18#margins` | L595-L595 |
| E8 | `lpM:L5` → `lpM:L5#compact-physical` | L175-L175 |
| E9 | `lpM:T15#reconstruction` → `lpM:T15#apply-L14` | L506-L506 |
| E10 | `lpM:L7` → `lpM:s1:elements` | L200-L200 |
| E11 | `lpM:T15#apply-L14` → `lpM:L14` | L506-L506 |
| E12 | `lpM:L18#rotation-invariance` → `lpM:s1:model` | L595-L595 |
| E13 | `lpM:L14#improvement` → `lpM:L14#route-L13` | L500-L500 |
| E14 | `lpM:L4#positivity` → `lpM:L4#feasible-compact` | L156-L156 |
| E15 | `lpM:L8#exact-split` → `lpM:s1:model` | L271-L271 |
| E16 | `lpM:L4#continuity` → `lpM:s1:thresholds#pairObjective` | L154-L154 |
| E17 | `lpM:L12#kappa-choice` → `lpM:L11` | L412-L412 |
| E18 | `lpM:T15#planar_strongAMD_exponentialSafety_halfInteger` → `lpM:L16:defs#sourceOscApo` | L93-L93 |
| E19 | `lpM:s1:thresholds#orderedCrossThreshold` → `lpM:s1:chamber#OrderedActions` | L52-L52 |
| E20 | `lpM:T15#chart-cover` → `lpM:L7` | L506-L506 |
| E21 | `lpM:s1:elements#strongAMD` → `lpM:s1:elements#keplerAction` | L33-L35 |
| E22 | `lpM:L2#spatialSourcePlanetAngularMomentum_length_le` → `lpM:s1:data#spaceLength` | L112-L112 |
| E23 | `lpM:L8#gluing` → `lpM:L8#compact-real-set` | L265-L265 |
| E24 | `lpM:L16#element-error` → `lpM:L5#pair-distances` | L527-L527 |
| E25 | `lpM:T15#planar_strongAMD_exponentialSafety` → `lpM:L1#barycentricVelocities` | L69-L69 |
| E26 | `lpM:L4#continuity` → `lpM:ext-heine-cantor` | L154-L154 |
| E27 | `lpM:L4#orderedCrossThreshold_isLeast` → `lpM:s1:chamber#OrderedActions` | L52-L52 |
| E28 | `lpM:L16:defs#sourceOscPeri` → `lpM:L16:defs#oscPeri` | L523-L523 |
| E29 | `lpM:L6` → `lpM:s1:chamber#chamber` | L179-L179 |
| E30 | `lpM:L9` → `lpM:L9#projections-tail` | L304-L304 |
| E31 | `lpM:T15#planar_strongAMD_exponentialSafety` → `lpM:L16:defs#sourceOscAxis` | L69-L69 |
| E32 | `lpM:T15` → `lpM:T15#reconstruction` | L506-L506 |
| E33 | `lpM:L2#sourceKeplerPeri_le_planeLength` → `lpM:s1:model#bodyVector` | L119-L119 |
| E34 | `lpM:L14` → `lpM:L14#axis-drift` | L495-L500 |
| E35 | `lpM:T15#planar_strongAMD_exponentialSafety` → `lpM:s1:model#IsMovingSolutionOn` | L69-L69 |
| E36 | `lpM:L2#spatialSourceKeplerApo_ge_length` → `lpM:s1:elements#SpatialSourceCanonicalPhase` | L118-L118 |
| E37 | `lpM:L16` → `lpM:L16#elliptic` | L527-L527 |
| E38 | `lpM:L2#sourceKepler_ecc_le_one` → `lpM:s1:data#planeLength` | L114-L114 |
| E39 | `lpM:L4#feasible-compact` → `lpM:s1:thresholds#pairObjective` | L149-L149 |
| E40 | `lpM:L16:defs#oscAxis` → `lpM:s1:model#Phase` | L516-L516 |

Statement-symbol sample: frozen theorem anchor → frozen definition only, in NODE/EDGE order, seed 6504. All symbols occur in the statement, before the proof boundary.

| Sample | Consumer → prerequisite |
|---|---|
| S1 | `lpM:T19#spatial_strongAMD_exponentialSafety_noArith` → `lpM:s1:data#spaceLength` |
| S2 | `lpM:T15#planar_strongAMD_exponentialSafety` → `lpM:s1:elements#keplerEnergy` |
| S3 | `lpM:T15#planar_strongAMD_exponentialSafety_noArith` → `lpM:L1#barycentricPositions` |
| S4 | `lpM:L5#planar_strongAMD_barrier` → `lpM:s1:elements#keplerAxis` |
| S5 | `lpM:L16#planeLength_le_sourceOscApo` → `lpM:L16:defs#SourceOsculatingPhase` |
| S6 | `lpM:T19#spatial_strongAMD_exponentialSafety_noArith` → `lpM:s1:elements#SpatialSourceCanonicalPhase` |
| S7 | `lpM:T15#planar_strongAMD_exponentialSafety_noArith` → `lpM:s1:thresholds#AdjIdx.upperIdx` |
| S8 | `lpM:L2#spatialSourceKeplerPeri_le_length` → `lpM:s1:model#bodyVector3` |
| S9 | `lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger` → `lpM:L16:defs#spatialOscEnergy` |
| S10 | `lpM:L2#spatialSourceKeplerEcc_nonneg` → `lpM:s1:elements#spatialSourceKeplerEcc` |

Coverage sample: seed 6502, MAIN/AMENDMENTS inventory items in file order. For each, raw source content matches the named unit and disposition; the two sampled exclusions are a section heading and normative N12's engineering-only note.

| Sample | Inventory item | Source lines |
|---|---|---|
| C1 | `lpM:h:s2` | MAIN L95-L95 |
| C2 | `lpM:L3#conservation` | MAIN L139-L139 |
| C3 | `lpM:L13#numeric-hypotheses` | MAIN L442-L457 |
| C4 | `lpM:eq25` | MAIN L293-L295 |
| C5 | `lpM:eq14` | MAIN L144-L146 |
| C6 | `lpA:N11` | AMENDMENTS L20-L20 |
| C7 | `lpM:s1:elements#spatialSourceStrongAMD` | MAIN L31-L37 |
| C8 | `lpM:L1#spatialSourceBarycentricVelocities` | MAIN L100-L108 |
| C9 | `lpM:s1:model#IsMovingSolutionOn` | MAIN L17-L24 |
| C10 | `lpM:s1:data` | MAIN L11-L15 |
| C11 | `lpM:L13#conclusion` | MAIN L460-L464 |
| C12 | `lpM:L8` | MAIN L244-L271 |
| C13 | `lpM:s1:model#spatialHamiltonian` | MAIN L17-L24 |
| C14 | `lpM:eq24` | MAIN L287-L291 |
| C15 | `lpM:L4#competitor` | MAIN L156-L156 |
| C16 | `lpM:L6#local-existence` | MAIN L189-L189 |
| C17 | `lpM:eq31` | MAIN L359-L362 |
| C18 | `lpM:s1:model#NoCollision` | MAIN L24-L24 |
| C19 | `lpM:L16#tangent-ellipse` | MAIN L527-L527 |
| C20 | `lpM:L11#induction` | MAIN L375-L375 |
| C21 | `lpM:s1:elements#spatialSourcePlanetAngularMomentum` | MAIN L31-L37 |
| C22 | `lpM:L14#choices` | MAIN L472-L476 |
| C23 | `lpM:eq27` | MAIN L316-L320 |
| C24 | `lpA:N12` | AMENDMENTS L21-L21 |
| C25 | `lpM:s1:model#bodyVector` | MAIN L17-L17 |

## Exact evidence-record refinements

Several records cite only MAIN L69 (“The common conclusion of Theorems 15 and 19. There are positive constants”), LP3-PLAN L85/L128 (section headings), or MAIN L118 (the opening display delimiter). These are navigational markers, not precise consumption evidence. Replace the indicated EDGE line in its existing NODE with the following exact EDGE line; keep the node's DEPS, all other edges and identity fields unchanged. No prerequisite is added, deleted or reversed. This lists every such locator defect identified in the required samples. Similar unsampled heading locators may remain; this is a sampled review, not a locator rewrite campaign.

```text
NODE: lpM:T15#planar_strongAMD_exponentialSafety
EDGE: lpM:L1#barycentricVelocities | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | Lemma 1 reconstructs the exact Newtonian motion, including the displayed barycentric velocities
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/source/MAIN.md#s1@L91-L91 | the actual-velocity osculating conclusion consumes the axes defined in Lemma 16 (516)
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L74-L78 | the solution of Hamiltonian (1) exists on the stated interval
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L70-L74 | the admissible initial states have negative Kepler energy

NODE: lpM:L2#spatialSourceKeplerApo_ge_length
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L120 | the source negative-energy carrier supplies the orbital assumptions for the radial upper bound

NODE: lpM:L2#spatialSourceKeplerPeri_le_length
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | the radial lower bound compares perihelion with the length of the position q

NODE: lpM:T19#spatial_strongAMD_exponentialSafety_noArith
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/lp3/LP3-PLAN.md#s1.3@L130-L134 | the spatial LP2 statement is retained except for the arithmetic premise and time/drift exponents; its physical Euclidean lengths are unchanged
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s1.3@L130-L134 | the spatial physical initial-state carrier and remaining LP2 premises are retained

NODE: lpM:T15#planar_strongAMD_exponentialSafety_noArith
EDGE: lpM:L1#barycentricPositions | docs/tracks/LP/lp3/LP3-PLAN.md#s1.2@L115-L119 | the retained Newtonian reconstruction explicitly uses barycentricPositions
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s1.2@L95-L98 | all other LP1 conclusions, including adjacent separations and osculating annuli, are retained with the same adjacent upper index

NODE: lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L510-L520 | the retained velocity-osculating conclusion uses the energy in (42) and asserts nondegenerate ellipticity
```

## Source defects and retained gaps

No new source defect is asserted beyond the following omissions already recorded as SOURCE_GAP. They remain visible even though the roots are sealed and the corresponding source steps are BYPASSED.

- MAIN L132–139: “On such an orbit” restricts the projection argument for (13) to the nonzero-total-angular-momentum regime; the frozen AMD characterization is on every source canonical phase. MAIN does not separately argue its L=0 case. Retain `lpM:L3#deficit-zero-L`; do not add a nonzero-L premise to the frozen characterization.
- MAIN L340–344 and AMENDMENTS N5 (L14): “Flow existence, Lie-series identification and c_D are sketched”. The source does not supply all substantive analytic details of the optional Lie-flow route. Retain `lpM:L10#flow-existence` and `lpM:L10#lie-flow-identification`. These affect the paper L12 route, not the separately implemented L13 supplier.
- MAIN L478: “Take the maximal local Newtonian solution.” Lemma 6's local existence and gluing argument does not explicitly construct the unique maximal solution agreeing with every local solution on overlaps. Retain `lpM:L14#maximal-solution`; the global/maximal ODE construction is a separate obligation from local continuation.

Amendments N2/N3 fix the common U and width conventions; N4 removes (35) from dependencies; N6/N7 fix route-specific radii and alternatives; N8 fixes orientation-free AMD under D59; N10 pays the half-gap osculating losses; N11 orders the perihelion and momentum constants. No sampled record reinstates an overridden premise or conflates canonical momenta with actual velocity. LP3 uses its own supplier and first-exit records, rather than inheriting a Diophantine premise through the LP1/LP2 assembly node.

Historical setup paragraphs in SPEC.md (LP3 “not frozen”) and LEAN_STATUS.md (“Not applied ... yet”) are superseded by their explicit final wave-4/step-C records. Read the final records as current; these historical passages are documentation clarity notes, not contradictory current counts. The earlier W2-lint report is a wave-2/3 snapshot, not evidence for the final 301-node state; the independent final linter run above supplies that evidence.

## Handoff

File: `docs/graph/LP/reviews/GLOBAL-review-1.md` only. Approach: exhaustive identity/structure/status rules plus the required reproducible source samples. Uncertainty: unsampled mathematical edges and source clauses were not independently audited; no proof or ABI rebuild is claimed. Deviations: the general source lint was stopped before its incompatible ABI stage, as documented; no mathematical or frozen-source deviation was introduced. Incorporate this review and the optional exact evidence refinements through the graph's single writer.
