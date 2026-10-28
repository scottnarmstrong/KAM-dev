# P5-CH independent package audit 1

Overall verdict: **FAIL — incomplete assigned graph slice**. The three definitions and three signed theorem interfaces match the current signature file, and the chart/lattice/location arguments pass inspection. However, `stepP:p5:pc-ham`, explicitly assigned to Chart, is neither stated nor proved by any export in the four audited files. Signature fidelity does not discharge this missing source assertion. This is an implementation/design coverage failure, not a counterexample to the proved chart or location statements.

| Source anchor | Overall verdict | Scope |
|---|---|---|
| bpP:p5:phi | PASS | All assigned definitions and real polar bridge are present. |
| bpP:p5:phi-chart | FAIL | Geometric signed theorem passes, but the source lemma's pc-ham assertion is omitted. |
| bpP:p5:location | PASS | Complete assigned range/action/disc slice. |

These are infrastructure verdicts, not a frozen-anchor seal authorization.

## Scope, authority, and immutable inputs

Audit date: 2026-10-28 UTC. Worktree `/root/code/KAM-inp-p5ch`; HEAD `9d4eef2444283434da27d1f725ffc5610c088393`; comparison branch `inp` = `d9183adae208ecf2e726620694b69c8168e33006`. All line references below refer to this snapshot (frozen-v1).

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied package brief, P5-CH-handoff.md, P45 design/node table/proof plan including Revision 4, P45 design audits, P45Signatures.lean, blueprint P5, the Track P statement, and the relevant frozen P-G theorem and definitions. Applied the manuscript-audit tier-2 and lean-statement-audit procedures to this infrastructure slice. The user explicitly authorized this report in this worktree, overriding the brief's generic main-worktree output instruction. Repository source/history is read-only; only this report and temporary probes under `.lake/abi-scratch/` may be written. No repair, commit, sealing, or generated-file regeneration is authorized or performed.

Only `KAM/Planetary/PGAssembly/Chart{,Defs,Loc,Mem}.lean` is under audit. The full `git diff inp...HEAD` contains 20 new files, including the merged 16-file P5-AV dependency; those averaging proofs are inspected only at the consumption boundary and are not independently re-audited here. No frozen anchor is implemented or sealed by P5-CH. Provider/frozen exact-type and seal-copy probes are therefore N/A; exact signed helper probes replace them. The wider P-G theorem remains outside this package's closure claim.

| Input | SHA256 |
|---|---|
| Chart.lean | `18fbc9502829808205847e0beacc41f517f1d676884f74d15f9f4ece3ae11de8` |
| ChartDefs.lean | `131362847bbb68b517c9b21b9ce2351e0f3f430ed1e372ca77bec4cbecb3fb85` |
| ChartLoc.lean | `2f64e51d8a96b4a20b13de86a689ee95ea6cb5b28239706c1c796fd8fb26c88f` |
| ChartMem.lean | `d65a9e13066182c424087c27584d5fb3794abf2b30bdaf30e2eb2b9bc678522b` |
| Shared `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` | `586ed2e3188b154d5cc6d44d3f85b420ef85ddd7faaa2bcbb6d6ca6db7d0f304` |
| docs/tracks/P/design/P45-LEAN-DESIGN.md | `fe084af07ac93f216e4f98e0ff5284319c5a544ee6df073af2069e9639d47559` |
| blueprint-P/parts/p5-pg-assembly.tex | `f8a5bc1683f30fed2576d0bb1ab6d51a1e6f00c6bf78c180d5a32efb0cef9968` |

## Finding F1: missing composed Hamiltonian identity

**Severity:** blocking source/graph coverage gap. **Refutation status:** survived a separate adversarial pass through the signatures, all four files, upstream specification, revised ownership, and potential definitional discharge. **Disposition:** reported only; no repair.

The design node table at P45-LEAN-DESIGN.md:172–175 assigns `bpP:p5:phi-chart` and `stepP:p5:pc-ham` to `PGAssembly/Chart`, with the text **“IsChart; Q1; Q2; compose the AveragingSpec identity”** and `pc-ham` **“local to phi_chart”**. Blueprint p5:190–195 says **“Moreover”** followed by `H_mu ∘ Phi = h_mu + f_mu` on O0, and Step Hamiltonian says **“H_mu ∘ barPsi is given by Proposition ...; compose with Pol, R_j ∘ Pol = J_2,j”**.

In contrast, Chart.lean:28–34 ends its exported conclusion at lattice injectivity. The proof at line 35 destructures `(pg_avg ...).choose_spec` as `⟨-, hinj, -, -, -, -, -, hper, hreal, hchart, -⟩`: its fourth component, the Hamiltonian identity, is discarded. `location` also discards it (line 96). No declaration in ChartDefs, ChartMem, ChartLoc, or Chart mentions `complexIntegrable`, `pgRemainder`, the averaging remainder, or `degenerateHamiltonian`. `IsChart` means analyticity and symplecticity, not an identity for this Hamiltonian.

Refutation attempts:

1. **Perhaps the signature differs:** no; the implemented `phi_chart` exactly matches the signed draft. The gap is already in the design's signature-to-node coverage, and old declaration-level design PASS receipts do not prove this omitted node.
2. **Perhaps the identity follows definitionally:** `phi` is only a composition of coordinate maps; its definition does not assert the nontrivial averaging equality. The fourth field of AveragingSpec still has to be applied, and the polar quadratic action identified with the input action.
3. **Perhaps an imported theorem already closes the node:** AveragingSpec provides an identity before composition, on `averagingDomain`, not its instantiated polar composition on `phiDomain`. No local theorem applies that field to `polar_mem_averagingDomain`; the actual compiled source contains no such composition. The geometric `location` conclusion does not supply it.
4. **Perhaps P5-KH owns it:** the controlling node table assigns `pc-ham` to Chart, while P5-KH owns separate analytic estimates. No explicit reassignment or extra Chart export is present. A future downstream proof cannot retrospectively make this slice complete.

Repair criterion for the owner: supply a separately named, premise-faithful composed identity and map this node to it, or explicitly revise the design ownership/interface and independently audit its replacement. Respect Revision 4: distinguish the complex extension identity from identification with the original total `d.P`; the latter may be used only where its actual source-domain premises have been proved. Do not silently strengthen `phi_chart` or frozen files during this audit.

No falsehood of a frozen theorem or new defect of a pinned published source is alleged. F1 is a mismatch between the blueprint/node contract and the delivered Lean surface.

## Node and declaration ledger

All Lean names below have prefix `KAM.Planetary.`. PASS rows describe the stated export; they do not override F1 or assert campaign closure.

| Node / role | Declaration and locator | Verdict | Evidence |
|---|---|---|---|
| bpP:p5:phi | phi, ChartDefs:30 | PASS | Exact formula and total type; real averaging after polar map. |
| bpP:p5:phi | phiDomain, ChartDefs:34 | PASS | Exact open action collar/shell predicate. |
| bpP:p5:phi / polar bridge | oscillatorPolarComplex, ChartDefs:39 | PASS | Exact principal complex-power formula in position/momentum order. |
| polar bridge | oscillatorPolarComplex_real, ChartDefs:44 | PASS | Exact signed positive-action real restriction; proves root and trigonometric compatibility. |
| bpP:p5:phi-chart, signed geometric part | phi_chart, Chart:28 | PASS | Exact signed type; openness, chart, lattice invariance/equivariance and injectivity modulo lattice. |
| stepP:p5:pc-img | polar_mem_averagingDomain, ChartMem:83; phi_chart:47 | PASS | Full domain membership, positive actions, then P4/P1 chart composition. |
| stepP:p5:pc-lat | oscillatorPolar_fullShift, ChartMem:73; phi_chart:36–65 | PASS | Polar shift, averaging periodicity, actual averaging injectivity, P4 lattice inverse. |
| stepP:p5:pc-ham | No export | FAIL | F1; no composed Hamiltonian identity. |
| bpP:p5:location | location, Chart:67 | PASS | Exact signature; stronger than only torus-range specialization: any action in the prescribed real neighbourhood. |
| stepP:p5:lo-range | location:73–95 | PASS | Witness y and componentwise Pi-norm estimate put scaled point in phiDomain. |
| stepP:p5:lo-act | location:103–119 | PASS | Fast displacement plus rK less than inner-core margin. |
| stepP:p5:lo-disc | location:120–155 | PASS | Two coordinate displacements bounded in Euclidean oscillator radius by sqrt(2) D2; strict radial slack. |
| parameter helper | chart_dyn, ChartMem:28 | PASS | Projects proved threshold dynamics; no extra input record. |
| parameter helper | chart_rK_lt_half, ChartMem:40 | PASS | r_k plus rhoHat <= l1/2; denominator branch does not change statement. |
| literal parameter identity | params_l2_eq, ChartMem:58 | PASS | rfl, l2=r²/2 globally. |
| openness | isOpen_phiDomain, ChartMem:60 | PASS | Continuous pullback of open sets; no admissibility required. |
| shell bounds | phiDomain_slow, ChartMem:67 | PASS | Exact lower bound and upper action <r². |
| shift domain | phiDomain_fullShift, ChartMem:119 | PASS | Actions unchanged; valid for every lattice shift. |
| positive action | phiDomain_slow_pos, ChartMem:123 | PASS | Admissible l1>0 plus shell lower endpoint. |
| conditional periodicity helper | realAverageMap_add_fastShift, ChartMem:129 | PASS | Distinct helper; all assumptions supplied by pg_avg and domain membership in phi_chart. |
| scalar disc estimate | chart_disc_aux, ChartLoc:26 | PASS | Cauchy–Schwarz and (s+E)²<r²; general elementary helper. |
| scalar radial slack | chart_radial_margin, ChartLoc:36 | PASS | E*r=l and s²<r²−3l imply s+E<r; general elementary helper. |
| geometric inner core | mem_of_dist_lt_innerCore, ChartLoc:45 | PASS | Connected closed ball avoiding frontier stays inside V; no openness assumption smuggled in. |

## Definition classification and public carriers

The three new definitions are **literal**, not characterization-defined objects. No new abbrev or structure exists in this slice.

| Definition | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | DEFINITION_VERDICT |
|---|---|---|---|---|---|---|
| phi | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| phiDomain | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| oscillatorPolarComplex | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |

`phi` is the literal composition with the already selected `pgAvg`; the source explicitly permits any extension away from O0. `pgAvg` selects an averaging map satisfying an existential specification, not a supposedly unique canonical solution; no uniqueness claim is used here. `phiDomain` has its exact meaning even for inadmissible r,mu; it is an open-set formula, with no fallback branch. `oscillatorPolarComplex` is the literal principal-power formula; holomorphic meaning is confined to positive-real-part slow actions, and its total extension outside that locus is not used to assert holomorphy or real agreement there. The real bridge explicitly requires positive slow actions. No junk value or hidden valid-locus-only replacement is introduced.

## Binder and consumption audit

For `phi_chart`, `location`, and `oscillatorPolarComplex_real`, signature comparison includes binder order/implicitness, dependence, carrier and conclusion. No constants are newly chosen after r,mu. Ambient spaces remain Fin-indexed Pi spaces with the Pi max norm; oscillator discs use the explicit sum of two squares. Fast physical shifts use 2*pi, and `location` explicitly scales all input angles by 2*pi.

The `PGData` bundle is expanded below against PG/Setting.lean:46–77 and the unchanged frozen `properlyDegenerateKAM` telescope. Data fields are SOURCE; logical premises are STANDING source premises, rather than unproduced graph obligations. Each field is listed separately.

| Expanded d field | Bin | Source meaning |
|---|---|---|
| ha | STANDING | Positive fast dimension. |
| hb | STANDING | Positive slow dimension. |
| V | SOURCE | Fast action set. |
| hV | STANDING | Open V. |
| hVc | STANDING | Connected V. |
| hVb | STANDING | Bounded V. |
| W | SOURCE | Ambient fast domain. |
| hW | STANDING | Open W. |
| hVW | STANDING | closure V inside W. |
| hboundary | STANDING | Source collar-volume condition, with its original existential constants and quantifiers. |
| r0 | SOURCE | Initial oscillator radius. |
| mu0 | SOURCE | Parameter upper bound. |
| B | SOURCE | Torsion determinant lower bound parameter. |
| hr0 | STANDING | Positive r0. |
| hmu0 | STANDING | Positive mu0. |
| hB | STANDING | Positive B. |
| H0 | SOURCE | Original fast Hamiltonian. |
| P | SOURCE | Original perturbation family. |
| P0 | SOURCE | Original secular constant coefficient. |
| Omega | SOURCE | Original linear secular coefficient. |
| beta | SOURCE | Original quadratic secular matrix. |
| hP | STANDING | Joint analyticity on the closed cylinder and parameter interval. |
| hperiod | STANDING | Fast 2*pi periodicity on the original cylinder. |
| hfreq | STANDING | Frozen HasFastDiffeomorphism: analytic H0, open frequency image, C1 inverse and both inverse identities. |
| hBNF | STANDING | Frozen HasSecularBirkhoffForm: integrability and the complete epsilon/delta little-o expansion, including zero. |
| htorsion | STANDING | Determinant bound for all original mu,I. |
| hsymm | STANDING | Matrix symmetry for all original mu,I. |

Counts in expanded d: SOURCE=10, STANDING=17, TYPING=0, RULED=0, EXCESS=0. The quantified clauses inside hboundary/hfreq/hBNF are the literal frozen source predicates, not added helpers; their full bodies were inspected.

| Remaining binder (each named separately) | Bin | Applicability / evidence |
|---|---|---|
| a | TYPING | Implicit natural dimension, all three signed theorems. |
| b | TYPING | Implicit natural dimension, all three signed theorems. |
| r | SOURCE | Small radius, phi_chart/location. |
| mu | SOURCE | Small perturbation parameter, phi_chart/location. |
| h.1 | SOURCE | 0<r. |
| h.2.1 | SOURCE | r<pgRstar d. |
| h.2.2.1 | SOURCE | 0<mu. |
| h.2.2.2.1 | SOURCE | mu<d.mu0. |
| h.2.2.2.2 | SOURCE | mu<r^6/log(1/r)^(2*pgTau+2). |
| z (location) | SOURCE | Arbitrary real phase input, a strengthening of torus specialization. |
| hz (location) | SOURCE | Its action is in the prescribed real rK-neighbourhood. |
| z (real bridge) | SOURCE | Real phase input. |
| hz (real bridge) | SOURCE | All slow actions positive. |

Totals per signed theorem after expanding d and h: phi_chart SOURCE=17, STANDING=17, TYPING=2; location SOURCE=19, STANDING=17, TYPING=2; real bridge SOURCE=2, STANDING=0, TYPING=2. RULED=EXCESS=0 in every case. No instance binder hides an assumption.

Auxiliary lemmas use only their displayed typing data, scalar/geometric hypotheses and already listed standing inputs. In particular `realAverageMap_add_fastShift` is explicitly conditional on `hper`, `hreal`, `hw`, `hw'`; it never substitutes for the source theorem. At Chart:43–45 these are supplied by the eighth/ninth fields of the actual `pg_avg` witness and `polar_mem_averagingDomain` before and after the lattice shift. Similarly `mem_of_dist_lt_innerCore` receives actual checked-core membership/frontier separation and the proved strict distance estimate. The elementary scalar inequalities assume their elementary inputs as helpers and prove, rather than assume, the graph's radial estimate inside `location`.

Actual proof dependencies: `pg_avg` produces the same chosen record as `pgAvg`; `phi_chart` uses its injectivity, periodicity, real trace, and chart fields. `disc_measure_chart.1` restricts to the positive slow-action set and composes via P1 `IsChart.comp`. P1 `hol_chart` is consumed upstream by `avg_chart` at AveragingDisp:47–54, then enters via the produced chart field; it is not assumed as a new premise. P4 `oscillatorPolar_lattice` is applied to the equality obtained using actual averaging injectivity. `location` uses the last AveragingSpec displacement field, `chart_dyn`, and `r_k`, and proves strict physical disc membership rather than replacing it with a rectangular oscillator bound. The missing fourth-field composition is F1.

## Verification evidence

Checks below are independent reruns, with `LEAN_NUM_THREADS=1`, sequential Lean/Lake invocations and nice priority 5. The gated targeted build may wait for another campaign's compile slot. No library clean, dependency cache fetch, or Mathlib rebuild was requested.

The pinned comparison merge base is `a6f0279b6313a38fe00178901d42e7a494d83ae4`. The shared `inp` ref advanced during this audit (observed later at `de67213e831cc1bc77872f080fce92c2e2a7d0a0`). The initial requested `git diff inp...HEAD` was reviewed before that move; reproducible comparisons below use the pinned initial inp commit, not a changing ref. A later symbolic comparison warned of multiple merge bases; it is not used to silently change the audit snapshot.

### Targeted build

Command:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5ch KAM.Planetary.PGAssembly.Chart
```

Exit 0. Output included:

```text
[inp-gate] slot 2 acquired 17:45:09 for KAM.Planetary.PGAssembly.Chart
Build completed successfully (9292 jobs).
```

The job count is Lake's dependency graph/replay count, not a clean library rebuild. Existing dependency linter warnings were replayed (including CompactLipschitz, JetsPoly, Jets, Scales, Diophantine, Collar, Poincare/Kepler and Polar); no warning/error was reported from the four audited files.

### Exact declaration probes and axioms

Command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5CHAudit1.lean
```

Final exit 0, no errors/warnings. Final probe SHA256 `f1a7b6106130c821a18ea29e1f366b338c7758da18ce02626ac74036db554cff`. The probe imported only Chart, copied the three signed theorem statements under `example` and applied their exact exports, copied the three signed definition bodies under fresh `audit_` names and checked equality with each exported definition by `rfl`. Mechanical comparisons (whitespace ignored only) returned:

```text
EXACT_SIGNATURE phi_chart True
EXACT_SIGNATURE location True
EXACT_SIGNATURE oscillatorPolarComplex_real True
EXACT_DEFINITION phi True
EXACT_DEFINITION phiDomain True
EXACT_DEFINITION oscillatorPolarComplex True
```

Two initial probe-only runs exited 1 because the generated copies needed a noncomputable section and then its correct closing order. These were auditor probe-scaffolding errors, not package errors; only scratch was corrected. The final complete run above passed.

`#print axioms` output for every one of these exports was exactly the same standard axiom list:

```text
'KAM.Planetary.phi_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.location' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'KAM.Planetary.phi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.phiDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscillatorPolarComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Structural hygiene

- Recursive project import traversal from Chart: 246 KAM modules, including 52 frozen definitions; **zero provider or frozen theorem modules**. No DRAFT_SORRY anchor or provider bypass is imported. Frozen theorem manifest-state checks are vacuous for this closure.
- Declaration-name scan across all KAM Lean files: all 19 new short declaration names have exactly one declaration site; no duplicate or root shadow found. All exports lie in `KAM.Planetary`.
- `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/PGAssembly/Chart{,Defs,Loc,Mem}.lean`: no output, exit 1 (no matches).
- File line counts: Chart=159, ChartDefs=73, ChartLoc=70, ChartMem=144. Each has the copyright, `module`, public imports, module docstring, exposed public noncomputable section, and a closing namespace/module section. No resource override.
- `git diff --check d9183adae208ecf2e726620694b69c8168e33006...HEAD`: no output, exit 0.
- `git diff --quiet d9183adae208ecf2e726620694b69c8168e33006...HEAD -- KAM/Frozen manifest KAM.lean README.md`: no output, exit 0. No protected/generated file changed.

### Kernel replay

Command (single invocation; nice priority inherited from the serial Python runner):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Chart KAM.Planetary.PGAssembly.ChartDefs KAM.Planetary.PGAssembly.ChartMem KAM.Planetary.PGAssembly.ChartLoc
```

Exit **0**, wall time **174.89 s**. Complete output:

```text
replaying KAM.Planetary.PGAssembly.ChartLoc
replaying KAM.Planetary.PGAssembly.ChartMem
replaying KAM.Planetary.PGAssembly.ChartDefs
replaying KAM.Planetary.PGAssembly.Chart
```

### Source lint

Command (nice priority and thread limit inherited from the same serial runner, after kernel replay exited):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, wall time **163.30 s**. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (832 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Hygiene verdict: **PASS WITH NOTES**, solely for the generated-root exception expressly permitted by the audit brief. KAM.lean was not regenerated or edited. No other lint defect was emitted.

## Closeout, uncertainties, and deviations

The audit is complete; the package is **not complete against its assigned graph slice**. F1 remains the single blocking finding. All 19 declarations and all nine assigned blueprint nodes (including the missing pc-ham step) are classified. All implemented public theorem axiom closures pass; the exact signed statements and all literal definitions pass; build and kernel replay pass; source lint has only the allowed generated-root exception. There is no pending check and no unresolved tentative finding.

No suspected new error in a pinned published source or frozen statement was found. The design's omitted Hamiltonian assertion is recorded under F1 with exact source/node evidence. The earlier Revision 4 extension-domain restriction is respected as an input; it must also be respected when F1 is repaired. No source, frozen, manifest, generated, or proof file was changed, and no implementation deviation was introduced by this auditor. The audit does not approve sealing P-G or certify the merged P5-AV package; those are separate tasks.

Final integrity checks: the four audited SHA256 values, the shared signature hash and the local design hash remained unchanged. The only new deliverable is this report; the pre-existing untracked P5-CH-handoff.md was preserved. The exact-type/definition/axiom probe and the two audit log files under `.lake/abi-scratch/` were removed after recording their results. No state-changing git command was run.

