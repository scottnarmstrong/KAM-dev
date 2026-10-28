# P5-CH independent package audit 2 — delta audit

Overall verdict: **PASS WITH NOTES**. Audit-1 finding F1 (`stepP:p5:pc-ham`) is closed. The 42-line additive fix exports the literal composed identity with source hypotheses only; prior statements and proofs are byte-unchanged. Build, signed-interface/displayed-identity probes, all public axiom checks, and kernel replay pass. Lint has only the expressly allowed stale generated-root exception. The live inp comparison includes unrelated history and is recorded explicitly below.

| Source anchor | Verdict | Scope |
|---|---|---|
| bpP:p5:phi | PASS | Definitions and real polar bridge unchanged. |
| bpP:p5:phi-chart | PASS | Geometric statement unchanged; new phi_comp_hamiltonian supplies the omitted pc-ham assertion. |
| bpP:p5:location | PASS | Signed statement and proof unchanged. |
| Package hygiene | PASS WITH NOTES | Generated-root lint exception and unrelated live-comparison provenance. |

Audit date: 2026-10-28 UTC.

Scope: `/root/code/KAM-inp-p5ch`, HEAD `215d57207ef58f30a5f6d3ff27c8304a4e0103b9`, delta from `00d2c742`. Only `KAM/Planetary/PGAssembly/Chart{,Defs,Loc,Mem}.lean` is audited. Round 1 remains the evidence for unchanged implementation arguments; this audit independently checks preservation, the new export, and current validation. These are infrastructure nodes; no frozen anchor is provided or authorized for sealing. Provider/frozen-type and seal-body probes are N/A.

Read the supplied package brief, AGENTS.md, PLAN, DECISIONS, both handoffs, audit 1, the P45 node table and Revision 4, shared P45Signatures, blueprint P5, Track P statement, PGData and relevant frozen source premises. The explicit user destination overrides the generic brief destination. Repository edits are restricted to this report and temporary `.lake/abi-scratch/` probes. No git mutation, source repair, generated-root refresh, or frozen-file modification.

## Delta integrity

`git diff --numstat 00d2c742 HEAD` outputs exactly:

```text
42  0  KAM/Planetary/PGAssembly/Chart.lean
```

The 42 added lines are Chart:67–108, inserted before `location`; this is additive insertion, not an append at end of file. Removing precisely that byte slice reproduces `git show 00d2c742:KAM/Planetary/PGAssembly/Chart.lean` byte for byte. ChartDefs, ChartLoc and ChartMem are independently byte-identical to that commit. All signed interfaces and prior proof bodies are thus byte-unchanged. The signature SHA256 remains `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304`, matching audit 1.

| File | Lines | Maximum line width | SHA256 |
|---|---:|---:|---|
| Chart.lean | 201 | 98 | `65fd8a17cda3d5c0223f3ee0f9bde21ceac66c20fb7c53ff5ee53bc02cdd35bc` |
| ChartDefs.lean | 73 | 96 | `131362847bbb68b517c9b21b9ce2351e0f3f430ed1e372ca77bec4cbecb3fb85` |
| ChartLoc.lean | 70 | 95 | `2f64e51d8a96b4a20b13de86a689ee95ea6cb5b28239706c1c796fd8fb26c88f` |
| ChartMem.lean | 144 | 100 | `d65a9e13066182c424087c27584d5fb3794abf2b30bdaf30e2eb2b9bc678522b` |

Every audited line is at most 100 Unicode characters and every file is below 1500 lines. The pre-fix claim “all files <160 lines” is superseded for Chart by the additive fix.

## Literal pc-ham and hypotheses

Blueprint `p5-pg-assembly.tex:189–190` states “Moreover” followed by the composed Hamiltonian decomposition on O0. Its proof step at :195 composes the averaging identity with Pol and identifies the oscillator actions. P45-LEAN-DESIGN.md:172–175 assigns this exact composition to Chart. `KAM.Planetary.phi_comp_hamiltonian` at Chart:72–107 now exports that assertion, pointwise for every `z ∈ phiDomain`:

- The left side is the extension Hamiltonian `H0 + mu P` evaluated at the actual real chart point `phi z`, included in complex phase space.
- `complexIntegrable d mu` is evaluated at the original fast actions and slow actions of z, with the literal polynomial integrable part of FrequencyDefs:55–56 and JetsDefs:41–43.
- The perturbation is exactly `mu * pgRemainder` plus the same selected averaging record's remainder, both evaluated after the same polar map. No factor of mu or 2*pi is added or dropped, and no action-angle scaling is silently introduced.

The proof obtains `AveragingSpec` from `(pg_avg ...).choose_spec` at :82, selects its fourth Hamiltonian field and ninth real-trace field at :83, and applies the fourth field to `polar_mem_averagingDomain h hz` at :84–85. The real-trace field identifies `Psi(realInclusion₂(Pol z))` with `realInclusion₂(phi z)` at :86–89. The fast actions are unchanged (:90–91). The slow-action equality (:92–106) proves `(sqrt(2I) sin θ)^2 + (sqrt(2I) cos θ)^2 = 2I` using positivity derived from `phiDomain_slow_pos`; division by two gives precisely J2. This proves the graph step rather than assuming it.

Binders: implicit a,b are typing data; d is the unchanged source-data bundle, with the original frozen premises expanded in audit 1 and rechecked against PG/Setting here; r,mu,z are source parameters; h is the five source admissibility inequalities; hz is exactly source membership in O0. No assumed averaging identity, output record, chart, inverse, Hamiltonian equality, or extra typeclass is accepted as a premise. No conclusion-shaped hypothesis or new constant dependence exists. The existing existence theorem supplies the same selected witness used in phi, so no choice-compatibility gap arises.

Revision 4 is respected: this is the complex-extension form of the blueprint Hamiltonian. It does not assert equality with the original total `d.P` at arbitrary points outside the original cylinder. Such a physical identification needs its actual cylinder/closure hypothesis; the present package does not bypass that condition. This is the same interpretation prescribed in audit-1's repair criterion and the Round 2 handoff.

## Node and declaration ledger

All short Lean names have namespace `KAM.Planetary`. Unchanged rows carry their mathematical argument verdict from audit 1 after byte verification; current axiom/build/replay evidence is listed below.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| bpP:p5:phi | phi; phiDomain; oscillatorPolarComplex | PASS | Literal definitions unchanged; exact source objects. |
| polar real bridge | oscillatorPolarComplex_real | PASS | Signed statement and proof unchanged. |
| bpP:p5:phi-chart | phi_chart; phi_comp_hamiltonian | PASS | Signed geometry plus separately named literal Hamiltonian export now cover full source lemma. |
| stepP:p5:pc-img | polar_mem_averagingDomain; phi_chart | PASS | Actual proved membership supplies both geometry and identity. |
| stepP:p5:pc-lat | oscillatorPolar_fullShift; phi_chart | PASS | Unchanged lattice argument. |
| stepP:p5:pc-ham | phi_comp_hamiltonian, Chart:72 | PASS | Former F1 closed by the explicit composition and polar action equality. |
| bpP:p5:location | location, Chart:109 | PASS | Exact signed statement and proof unchanged. |
| stepP:p5:lo-range | location | PASS | Unchanged input-collar argument. |
| stepP:p5:lo-act | location | PASS | Unchanged physical fast-action margin. |
| stepP:p5:lo-disc | location | PASS | Unchanged strict oscillator disc estimate. |
| threshold helper | chart_dyn | PASS | Unchanged produced threshold facts. |
| radius helper | chart_rK_lt_half | PASS | Unchanged scalar consequence of r_k. |
| literal parameter identity | params_l2_eq | PASS | Unchanged rfl identity. |
| domain openness | isOpen_phiDomain | PASS | Unchanged continuous pullback argument. |
| action shell bounds | phiDomain_slow | PASS | Unchanged literal inequalities. |
| lattice domain | phiDomain_fullShift | PASS | Unchanged action-preserving shift. |
| slow positivity | phiDomain_slow_pos | PASS | Unchanged positive action consequence. |
| conditional averaging periodicity | realAverageMap_add_fastShift | PASS | Unchanged distinct helper; its conditions are supplied from the actual witness. |
| scalar disc helper | chart_disc_aux | PASS | Unchanged elementary estimate. |
| radial slack helper | chart_radial_margin | PASS | Unchanged elementary estimate. |
| inner-core helper | mem_of_dist_lt_innerCore | PASS | Unchanged geometric source-data argument. |

No new def/abbrev/structure is introduced. Existing phi, phiDomain, oscillatorPolarComplex retain audit-1 classification: literal body, correct whole carrier, no theorem-relevant fallback or junk value. phi uses a produced existential witness without claiming canonical uniqueness. Positivity explicitly guards the real polar bridge; no holomorphic meaning is claimed at arbitrary nonpositive slow actions.

## Comparison with inp and hygiene scope

The required `git diff inp...HEAD` was inspected, including its four-file package slice. Live inp is `e2088d57c609cc20f1033b70a41e064402222f53`. Git warns “multiple merge bases” and chooses `a05a4da2c925a5430a4de470e6494c13235fb468`. The resulting 149-file comparison includes unrelated upstream history, not solely this package: in particular 71 added root import lines in KAM.lean. Therefore the brief's whole-live-comparison protected/generated-empty check is NOT literally clean for KAM.lean. Frozen, manifest and README paths are empty even in that comparison.

For provenance isolation, `git diff --quiet d9183adae208ecf2e726620694b69c8168e33006...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0, and the exact round-2 delta has no protected/generated changes. The old comparison pin is audit 1's actual inp snapshot, not a replacement for reporting the live comparison. No generated-root modification is attributable to the fix or the original P5-CH slice.

`git diff --check 00d2c742 HEAD` and the four-file `git diff --check inp...HEAD -- ...` exit 0. The whole live `git diff --check inp...HEAD` exits 2 with pre-existing whitespace in RectangularAverage:62,67; ToriInvStage:186; B02-handoff:17; P11A-P4-handoff:25; and trailing blank lines in P23-18-audit-2:324, P5-CH-audit-1:272, S10-F-audit-1:193. None is part of the 42-line fix; no repair was performed.

A recursive source import scan finds 246 KAM modules and no provider or frozen theorem module; no DRAFT_SORRY import. A declaration scan across KAM finds all 20 package short names unique, including exactly one `phi_comp_hamiltonian` at Chart:72 inside KAM.Planetary. No root shadow. All prior public names remain unchanged. The four files have copyright, module, public import, module docstring, exposed public section. `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/PGAssembly/Chart{,Defs,Loc,Mem}.lean` returns no matches (exit 1).

## Execution evidence

All Lean work is serialized with LEAN_NUM_THREADS=1 and nice priority 5. Independent current-turn checks, not merely prover receipts:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5ch KAM.Planetary.PGAssembly.Chart
```

Exit 0. The gate acquired slot 2 at 18:23:36 UTC; the wrapper runs `nice -n 5 lake build`. Final output: `Build completed successfully (9292 jobs).` Cached dependency warnings concerned unused variables/simp arguments in CompactLipschitz, JetsPoly, Jets, Kepler/Mass and Polar; no error or audited-file warning. No whole-library rebuild, clean, cache download or package mutation was requested.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5CHDeltaAudit.lean
```

Exit 0. Probe copies the signed phi_chart/location/oscillatorPolarComplex_real interfaces directly from the unchanged shared signature and proves them by the real exports. A separate example introduces the literal Hmu, hmu and fmu formulas and proves `Hmu (phi z) = hmu z.2 + fmu z` by the new export, verifying vector inclusion/append and additive grouping without adding a hypothesis. All 20 public declarations were queried with `#print axioms`. Complete axiom output:

```text
'KAM.Planetary.phi_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phi_comp_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.location' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phiDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolarComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolarComplex_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_disc_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_radial_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_of_dist_lt_innerCore' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_dyn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_rK_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_l2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_phiDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phiDomain_slow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolar_fullShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polar_mem_averagingDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phiDomain_fullShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phiDomain_slow_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.realAverageMap_add_fastShift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Chart KAM.Planetary.PGAssembly.ChartDefs KAM.Planetary.PGAssembly.ChartMem KAM.Planetary.PGAssembly.ChartLoc
```

Single invocation, exit 0. Complete output:

```text
replaying KAM.Planetary.PGAssembly.ChartLoc
replaying KAM.Planetary.PGAssembly.ChartMem
replaying KAM.Planetary.PGAssembly.ChartDefs
replaying KAM.Planetary.PGAssembly.Chart
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the generated-root exception expressly permitted by the package brief. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (832 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

KAM.lean was not regenerated. No heartbeat, recursion-depth, synthesis-budget, size, module, frozen-anchor or ABI failure was reported.


## Errata, uncertainties and closeout

No new suspected defect of a pinned published source or frozen statement. The known Revision 4 blueprint extension-agreement imprecision is retained, not silently repaired. The node table's phrase “local to phi_chart” now corresponds to the separate premise-faithful export phi_comp_hamiltonian in the same assigned Chart module; the signed phi_chart interface is unchanged. No proof/source deviation introduced by this auditor. This audit neither re-audits the entire P5-AV dependency nor authorizes sealing P-G.

Final integrity: all four source hashes still match the table; removing the new 42-line block still reproduces the baseline Chart bytes exactly. The shared signature hash is unchanged. The exact delta whitespace check passes. The temporary probe, comparison capture and validation logs have been removed from `.lake/abi-scratch/`. `git status --short` contains only this new report. No required check remains pending, and no blocking finding remains in the audited slice.
